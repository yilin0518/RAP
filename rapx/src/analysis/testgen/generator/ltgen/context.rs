use super::lifetime::RegionGraph;
use super::RegionSubgraphMap;
use crate::analysis::testgen::context::{Context, HoldTyCtxt};
use crate::analysis::testgen::context::{Stmt, StmtKind, Var};
use crate::analysis::testgen::generator::ltgen::folder::RegionExtractFolder;
use crate::analysis::testgen::utils;
use crate::rap_debug;
use rustc_middle::ty::{self, Ty, TyCtxt, TyKind, TypeFoldable};

use std::collections::{HashMap, HashSet};

pub struct LtContext<'tcx, 'a> {
    stmts: Vec<Stmt>,
    available: HashSet<Var>,
    var_ty: HashMap<Var, Ty<'tcx>>,
    var_is_mut: HashMap<Var, ty::Mutability>,
    var_vid: HashMap<Var, usize>,
    tcx: TyCtxt<'tcx>,
    region_graph: RegionGraph,
    subgraph_map: &'a RegionSubgraphMap,
}

impl<'tcx, 'a> HoldTyCtxt<'tcx> for LtContext<'tcx, 'a> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }
}

impl<'tcx, 'a> Context<'tcx> for LtContext<'tcx, 'a> {
    fn stmts(&self) -> &[Stmt] {
        &self.stmts
    }
    fn add_stmt(&mut self, stmt: Stmt) {
        let var = stmt.place();
        let var_ty = self.type_of(var);
        let tcx = self.tcx();

        // maintain lifetime relationship between ref and var
        match stmt.kind() {
            StmtKind::Call(apicall) => {
                let fn_did = apicall.fn_did();
                let mut fn_sig = utils::fn_sig_without_binders(fn_did, tcx);

                // get actual vid of input in the pattern
                let mut inputs = Vec::new();
                for var in apicall.args() {
                    let ty = self.type_of(*var);
                    inputs.push(ty);
                }
                let real_fn_sig = tcx.mk_fn_sig(
                    inputs.into_iter(),
                    var_ty,
                    fn_sig.c_variadic,
                    fn_sig.safety,
                    fn_sig.abi,
                );
                let mut folder = RegionExtractFolder::new(self.tcx());
                real_fn_sig.fold_with(&mut folder);

                if let ty::Ref(inner_region, ..) = var_ty.kind() {
                    self.region_graph
                        .add_edge_by_region(self.region_of(var), *inner_region);
                }

                // get pattern
                let patterns = self.subgraph_map.get(&fn_did).unwrap();
                rap_debug!("patterns: {:?}", patterns);
                rap_debug!("regions: {:?}", folder.regions());

                self.region_graph.add_edges_with(patterns, folder.regions());
            }
            StmtKind::Ref(inner_var, _) => {
                let id = match var_ty.kind() {
                    TyKind::Ref(region, _, _) => match region.kind() {
                        ty::RegionKind::ReVar(vid) => vid.index(),
                        _ => {
                            panic!("unexpected region: {:?}", region);
                        }
                    },
                    _ => {
                        panic!("unexpected type: {:?}", var_ty);
                    }
                };

                // if ref_stmt is something like lhs = &rhs, where b is also a reference,
                // then add lhs-->rhs because rhs must outlive lhs
                self.region_graph
                    .add_edge_by_id(self.vid_of(var), self.vid_of(**inner_var));
            }
            StmtKind::Deref(var) => {
                todo!()
            }
            _ => {}
        }
        self.stmts.push(stmt);
    }

    fn lift_mutability(&mut self, var: Var, mutability: ty::Mutability) {
        if matches!(mutability, ty::Mutability::Mut) {
            self.var_is_mut.insert(var, ty::Mutability::Mut);
        }
    }

    fn var_mutability(&self, var: Var) -> ty::Mutability {
        *self.var_is_mut.get(&var).unwrap_or(&ty::Mutability::Not)
    }

    fn available_values(&self) -> &HashSet<Var> {
        &self.available
    }

    fn mk_var(&mut self, ty: Ty<'tcx>, is_input: bool) -> Var {
        let next_var = Var(self.var_ty.len(), is_input);
        let ty = self.region_graph.register_var_ty(ty, self.tcx());
        let id = self.region_graph.next_named_node();
        rap_debug!("var: {} ty: {:?}", next_var, ty);

        // self.vid_map.insert(id, next_var);
        self.var_vid.insert(next_var, id);
        self.var_ty.insert(next_var, ty);
        self.available.insert(next_var);
        next_var
    }

    fn ref_region(&self, var: Var) -> ty::Region<'tcx> {
        self.region_of(var)
    }

    fn remove_var(&mut self, var: Var) {
        self.available.remove(&var);
    }

    fn type_of(&self, var: Var) -> Ty<'tcx> {
        *self.var_ty.get(&var).expect("no type for var")
    }
}

impl<'tcx, 'a> LtContext<'tcx, 'a> {
    pub fn new(tcx: TyCtxt<'tcx>, subgraph_map: &'a RegionSubgraphMap) -> Self {
        Self {
            stmts: Vec::new(),
            available: HashSet::new(),
            var_ty: HashMap::new(),
            var_vid: HashMap::new(),
            tcx,
            // vid_map: HashMap::new(),
            var_is_mut: HashMap::new(),
            region_graph: RegionGraph::new(),
            subgraph_map,
        }
    }

    pub fn region_graph(&self) -> &RegionGraph {
        &self.region_graph
    }

    // pub fn debug_constraint(&self) {
    //     let region_constraint_data = self.infcx.take_and_reset_region_constraints();

    //     for (constraint, _origin) in region_constraint_data.constraints {
    //         rap_debug!("constraint: {}", constraint_str(constraint, self.tcx()));
    //     }
    // }

    pub fn vid_of(&self, var: Var) -> usize {
        self.var_vid[&var]
    }

    pub fn region_of(&self, var: Var) -> ty::Region<'tcx> {
        ty::Region::new_var(self.tcx(), self.vid_of(var).into())
    }
}
