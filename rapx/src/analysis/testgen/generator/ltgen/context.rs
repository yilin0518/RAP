use super::folder::extract_rids;
use super::lifetime::{RegionGraph, Rid};
use super::pattern::PatternProvider;
use super::utils;
use super::{destruct_ret_alias, FnAliasMap};
use crate::analysis::testgen::context::{ApiCall, Context, HoldTyCtxt};
use crate::analysis::testgen::context::{Stmt, StmtKind, Var};
use crate::analysis::testgen::generator::ltgen::folder::RidExtractFolder;
use crate::analysis::testgen::generator::ltgen::lifetime::{
    visit_structure_region_with, RegionNode,
};
use crate::analysis::testgen::generator::ltgen::safety;
use crate::{rap_debug, rap_info, rap_trace, rap_warn};
use rustc_hir::def_id::DefId;
use rustc_middle::ty::{self, GenericArg, Ty, TyCtxt, TyKind, TypeFoldable, TypeVisitableExt};
use std::collections::{HashMap, HashSet, VecDeque};

pub struct LtContext<'tcx, 'a> {
    stmts: Vec<Stmt<'tcx>>,
    available: HashSet<Var>,
    var_ty: HashMap<Var, Ty<'tcx>>,
    var_mutability: HashMap<Var, ty::Mutability>,
    var_rid: HashMap<Var, Rid>,
    var_dropped: HashSet<Var>,
    tcx: TyCtxt<'tcx>,
    region_graph: RegionGraph,
    pat_provider: PatternProvider<'tcx>,
    alias_map: &'a FnAliasMap,
    covered_api: HashSet<DefId>,
    droped_cnt: usize,
}

impl<'tcx, 'a> HoldTyCtxt<'tcx> for LtContext<'tcx, 'a> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }
}

impl<'tcx, 'a> Context<'tcx> for LtContext<'tcx, 'a> {
    fn stmts(&self) -> &[Stmt<'tcx>] {
        &self.stmts
    }

    fn add_stmt(&mut self, stmt: Stmt<'tcx>) {
        let var = stmt.place();
        // maintain lifetime relationship between ref and var
        match stmt.kind() {
            StmtKind::Call(apicall) => {
                let fn_did = apicall.fn_did();

                self.covered_api.insert(fn_did);

                let real_fn_sig = self.mk_fn_sig(&stmt);
                let mut folder = RidExtractFolder::new(self.tcx());
                real_fn_sig.fold_with(&mut folder);

                // get pattern
                self.pat_provider.get_patterns_with(
                    apicall.fn_did(),
                    apicall.generic_args(),
                    |patterns| {
                        rap_debug!("patterns: {:?}", patterns);
                        rap_debug!("regions: {:?}", folder.rids());

                        self.region_graph
                            .add_edges_by_patterns(patterns, folder.rids());
                    },
                );
            }
            StmtKind::Ref(inner_var, _) => {}
            StmtKind::Deref(inner_var) => {
                todo!()
            }
            _ => {}
        }
        self.stmts.push(stmt);
    }

    fn lift_mutability(&mut self, var: Var, mutability: ty::Mutability) {
        if matches!(mutability, ty::Mutability::Mut) {
            self.var_mutability.insert(var, ty::Mutability::Mut);
        }
    }

    fn var_mutability(&self, var: Var) -> ty::Mutability {
        *self
            .var_mutability
            .get(&var)
            .unwrap_or(&ty::Mutability::Not)
    }

    fn available_values(&self) -> &HashSet<Var> {
        &self.available
    }

    fn mk_var(&mut self, ty: Ty<'tcx>, is_input: bool) -> Var {
        let next_var = Var(self.var_ty.len() + 1, is_input);
        let ty = self.region_graph.register_ty(ty, self.tcx());
        let rid = self.region_graph.register_var(next_var);

        rap_debug!("[mk_var] ('?{}) {}: {:?}", rid.index(), next_var, ty);

        self.var_ty.insert(next_var, ty);
        self.var_rid.insert(next_var, rid);
        self.available.insert(next_var);

        rap_debug!("[mk_var] var: {}, type: {:?}", next_var, ty);

        // add structural constraint between 'var and 'a where carry by the type of var
        visit_structure_region_with(
            ty,
            Some(self.region_of(next_var)),
            self.tcx(),
            &mut |from, to| {
                self.region_graph.add_edge_by_region(from, to);
            },
        );
        next_var
    }

    fn ref_region(&self, var: Var) -> ty::Region<'tcx> {
        self.region_of(var)
    }

    fn set_var_unavailable_unchecked(&mut self, var: Var) {
        self.available.remove(&var);
    }

    fn type_of(&self, var: Var) -> Ty<'tcx> {
        *self.var_ty.get(&var).expect("no type for var")
    }
}

impl<'tcx, 'a> LtContext<'tcx, 'a> {
    pub fn new(tcx: TyCtxt<'tcx>, alias_map: &'a FnAliasMap) -> Self {
        Self {
            stmts: Vec::new(),
            available: HashSet::new(),
            var_ty: HashMap::new(),
            var_rid: HashMap::new(),
            var_dropped: HashSet::new(),
            tcx,
            var_mutability: HashMap::new(),
            region_graph: RegionGraph::new(),
            pat_provider: PatternProvider::new(tcx),
            alias_map,
            covered_api: HashSet::new(),
            droped_cnt: 0,
        }
    }

    pub fn region_graph(&self) -> &RegionGraph {
        &self.region_graph
    }

    pub fn detect_potential_vulnerability(
        &self,
        stmt: &Stmt<'tcx>,
    ) -> Option<HashMap<Var, Vec<Rid>>> {
        let mut ret: HashMap<Var, Vec<Rid>> = HashMap::new();
        let tcx = self.tcx();

        let call = stmt.api_call();
        let fn_sig = self.mk_fn_sig(stmt);

        let mut check_potential_region_leak = |lhs_var, lhs_ty, rhs_var, rhs_ty| {
            rap_trace!(
                "[check_potiential_region_leak] lhs_var={}: {} rhs_var={}: {}",
                lhs_var,
                lhs_ty,
                rhs_var,
                rhs_ty
            );

            let mut rhs_ty_rids = extract_rids(rhs_ty, tcx);

            // if rhs_ty does not bind with any lifetime,
            // this maybe imply that lhs is a reference of rhs (e.g., lhs=&rhs.f)
            // the coresponding lifetime binding 'lhs->'rhs should be added
            // FIXME: the field-sensitive alias analysis is not exactly possible,
            // so we may miss some 'lhs -> 'rhs lifetime bindings
            if rhs_ty_rids.is_empty() && safety::check_possibility(lhs_ty, rhs_ty, tcx) {
                rhs_ty_rids.push(self.rid_of(rhs_var));
            }
            let lhs_rid = self.rid_of(lhs_var);
            let entry: &mut _ = ret.entry(lhs_var).or_default();

            // add all unsafe regions into entry
            rhs_ty_rids.into_iter().for_each(|rid| {
                if !self.region_graph().prove(lhs_rid, rid) {
                    entry.push(rid);
                }
            });
        };

        for alias in self
            .alias_map
            .get(&call.fn_did())
            .expect(&format!("{:?} do not have alias infomation", call.fn_did()))
            .aliases()
        {
            // ths alias is symmetric, that is, if (a,b) exists, then (b,a) must exist
            let (lhs_ty, rhs_ty) = destruct_ret_alias(fn_sig, alias, self.tcx());
            let lhs_var = stmt.as_call_arg(alias.left_index);
            let rhs_var = stmt.as_call_arg(alias.right_index);
            check_potential_region_leak(lhs_var, lhs_ty, rhs_var, rhs_ty);
        }
        if ret.is_empty() {
            return None;
        }
        Some(ret)
    }

    pub fn rid_of(&self, var: Var) -> Rid {
        self.var_rid[&var]
    }

    pub fn region_of(&self, var: Var) -> ty::Region<'tcx> {
        ty::Region::new_var(
            self.tcx(),
            ty::RegionVid::from_usize(self.rid_of(var).into()),
        )
    }

    pub fn dropped_count(&self) -> usize {
        self.droped_cnt
    }

    fn set_var_dropped(&mut self, var: Var) {
        if self.var_dropped.insert(var) {
            self.droped_cnt += 1;
        }
    }

    fn add_drop_stmt(&mut self, dropped: Var) -> Var {
        let var = self.mk_var(self.tcx().types.unit, false);
        self.add_stmt(Stmt::drop_(var, dropped));
        self.set_var_dropped(var);
        self.set_var_unavailable_recursive(dropped);
        var
    }

    fn set_var_unavailable_recursive(&mut self, var: Var) {
        let mut q = VecDeque::from([self.rid_of(var).into()]);
        let mut visited = vec![false; self.region_graph.total_node_count()];
        visited[self.rid_of(var).index()] = true;
        while let Some(rid) = q.pop_front() {
            if let RegionNode::Named(var) = self.region_graph.get_node(rid) {
                rap_debug!("set var {} unavailable", var);
                self.set_var_unavailable_unchecked(var);
            }
            for next_idx in self
                .region_graph
                .inner()
                .neighbors_directed(rid.into(), petgraph::Direction::Incoming)
            {
                if !visited[next_idx.index()] {
                    visited[next_idx.index()] = true;
                    q.push_back(next_idx.into());
                }
            }
        }
    }

    pub fn try_inject_drop(&mut self) -> bool {
        let stmt = self.stmts().last().unwrap();
        let mut success = false;
        if stmt.kind().is_call() {
            if let Some(vec) = self.detect_potential_vulnerability(&stmt) {
                for (var, rids) in vec {
                    rap_debug!("[unsafe] variable {} lack of binding with {:?}", var, rids);
                    for rid in rids {
                        let mut src_rids = Vec::new();
                        self.region_graph
                            .for_each_source(rid, &mut |rid| src_rids.push(rid));
                        let dropped_var: Vec<Var> = src_rids
                            .into_iter()
                            .map(|rid| self.region_graph.get_node(rid).as_var())
                            .collect();
                        if !dropped_var.is_empty() {
                            success = true;
                        }
                        for var in dropped_var.iter() {
                            self.add_drop_stmt(*var);
                        }
                        rap_debug!("[unsafe] drop var: {:?}", dropped_var);
                    }
                }
            }
        }
        success
    }

    pub fn num_covered_api(&self) -> usize {
        self.covered_api.len()
    }
}
