use super::lifetime;
use crate::analysis::testgen::{generator::ltgen::folder::InfcxVarFolder, utils};
use crate::{rap_debug, rap_info, rap_trace};
use rustc_hir::def_id::DefId;
use rustc_infer::infer;
use rustc_infer::{
    infer::{region_constraints::Constraint, TyCtxtInferExt as _},
    traits::ObligationCause,
};
use rustc_middle::ty::{self, TyCtxt, TypeFoldable as _};
use rustc_span::DUMMY_SP;
use rustc_type_ir::RegionVid;
use std::collections::HashMap;

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum PatternNode {
    Static,
    Named(usize),
    Temp(usize),
}

#[derive(Debug)]
pub struct EdgePattern(PatternNode, PatternNode);
impl EdgePattern {
    pub fn from(&self) -> PatternNode {
        self.0
    }
    pub fn to(&self) -> PatternNode {
        self.1
    }
}

#[derive(Debug, Default)]
pub struct EdgePatterns {
    named_region_num: usize,
    temp_num: usize,
    patterns: Vec<EdgePattern>,
}

impl EdgePatterns {
    pub fn named_region_num(&self) -> usize {
        self.named_region_num
    }

    pub fn temp_num(&self) -> usize {
        self.temp_num
    }

    pub fn patterns(&self) -> &[EdgePattern] {
        &self.patterns
    }
}

pub struct PatternProvider<'tcx> {
    tcx: TyCtxt<'tcx>,
    map: HashMap<DefId, EdgePatterns>,
}

impl<'tcx> PatternProvider<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> PatternProvider<'tcx> {
        PatternProvider {
            tcx: tcx,
            map: HashMap::new(),
        }
    }
    pub fn get_patterns_with<T>(
        &mut self,
        fn_did: DefId,
        args: &[ty::GenericArg<'tcx>],
        mut f: impl FnMut(&EdgePatterns) -> T,
    ) -> T {
        let tcx = self.tcx;
        if !utils::fn_requires_monomorphization(fn_did, tcx) {
            f(self
                .map
                .entry(fn_did)
                .or_insert_with(|| extract_constraints(fn_did, args, tcx)))
        } else {
            f(&extract_constraints(fn_did, args, tcx))
        }
    }
}

pub fn extract_constraints<'tcx>(
    fn_did: DefId,
    generic_args: &[ty::GenericArg<'tcx>],
    tcx: TyCtxt<'tcx>,
) -> EdgePatterns {
    rap_trace!(
        "[extract_constraints] fn_did: {:?}, generic_args: {:?}",
        fn_did,
        generic_args
    );

    let infcx = tcx.infer_ctxt().build(ty::TypingMode::PostAnalysis);
    let mut folder = InfcxVarFolder::new(&infcx, tcx);

    let early_fn_sig = tcx.fn_sig(fn_did);
    rap_debug!("[extract_contraints] early_fn_sig = {:?}", early_fn_sig);

    let fresh_args =
        tcx.mk_args_from_iter(generic_args.iter().map(|arg| arg.fold_with(&mut folder)));
    rap_debug!("[extract_contraints] fresh_args = {:?}", fresh_args);

    // formal fn_sig
    let fn_binder = early_fn_sig.instantiate(tcx, fresh_args);
    let fn_sig = infcx.instantiate_binder_with_fresh_vars(
        DUMMY_SP,
        infer::BoundRegionConversionTime::FnCall,
        fn_binder,
    );

    let temp_cnt = infcx.num_region_vars();
    assert!(infcx.num_ty_vars() == 0);

    // outer universe fn_sig
    let free_fn_sig = fn_sig.fold_with(&mut folder);

    rap_debug!("[extract_contraints] fn_sig = {:?}", fn_sig);
    rap_debug!("[extract_contraints] free_fn_sig = {:?}", free_fn_sig);

    let param_env = tcx.param_env(fn_did);

    let dummy = ObligationCause::dummy();

    let res = infcx
        .at(&dummy, param_env)
        .sub(infer::DefineOpaqueTypes::Yes, fn_sig, free_fn_sig)
        .unwrap();

    rap_trace!("infcx result: {res:?}");

    let at = infcx.at(&dummy, param_env);
    let mut f = |prev_region, region| {
        let _ = at
            .sub(infer::DefineOpaqueTypes::Yes, region, prev_region)
            .unwrap();
    };

    for input in fn_sig.inputs().iter() {
        lifetime::visit_structure_region_with(*input, None, tcx, &mut f);
    }
    lifetime::visit_structure_region_with(fn_sig.output(), None, tcx, &mut f);

    let region_constraint_data = infcx.take_and_reset_region_constraints();
    let get_pattern_node = |vid: RegionVid| -> PatternNode {
        let id = vid.as_usize();
        if id < temp_cnt {
            PatternNode::Temp(id)
        } else {
            PatternNode::Named(id - temp_cnt)
        }
    };

    let mut subgraph = EdgePatterns::default();

    for (constraint, _) in region_constraint_data.constraints {
        let edge = match constraint {
            Constraint::VarSubVar(a, b) => EdgePattern(get_pattern_node(a), get_pattern_node(b)),
            Constraint::RegSubVar(region, var) => {
                if region.is_static() {
                    EdgePattern(PatternNode::Static, get_pattern_node(var))
                } else {
                    panic!("unexpected constraint: {:?}", constraint);
                }
            }
            Constraint::VarSubReg(var, region) => {
                if region.is_static() {
                    EdgePattern(get_pattern_node(var), PatternNode::Static)
                } else {
                    panic!("unexpected constraint: {:?}", constraint);
                }
            }
            _ => {
                panic!("unexpected constraint: {:?}", constraint);
            }
        };
        subgraph.patterns.push(edge);
    }

    // extract constraints from where clauses of Fn
    let predicates = tcx.predicates_of(fn_did).instantiate(tcx, fresh_args);
    predicates.predicates.iter().for_each(|clause| {
        if let Some(outlive_pred) = clause.as_region_outlives_clause() {
            let outlive_pred = outlive_pred.skip_binder();
            // lhs : rhs
            let (lhs, rhs) = (outlive_pred.0, outlive_pred.1);

            // build edge from rhs to lhs
            subgraph.patterns.push(EdgePattern(
                get_pattern_node(rhs.as_var()),
                get_pattern_node(lhs.as_var()),
            ));
        }
    });

    subgraph.named_region_num = infcx.num_region_vars() - temp_cnt;
    subgraph.temp_num = temp_cnt;
    subgraph
}
