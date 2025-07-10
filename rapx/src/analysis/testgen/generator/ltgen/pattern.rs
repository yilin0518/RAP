use super::lifetime;
use crate::analysis::testgen::{generator::ltgen::folder::InfcxVarFolder, utils};
use crate::rap_trace;
use rustc_hir::def_id::DefId;
use rustc_infer::infer;
use rustc_infer::{
    infer::{region_constraints::Constraint, TyCtxtInferExt as _},
    traits::ObligationCause,
};
use rustc_middle::ty::{self, TyCtxt, TypeFoldable as _};
use std::collections::HashMap;

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum PatternNode {
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

    let fn_sig = utils::fn_sig_with_generic_args(fn_did, generic_args, tcx);
    let fn_with_free_vars = fn_sig.fold_with(&mut folder);

    let param_env = tcx.param_env(fn_did);

    let dummy = ObligationCause::dummy();

    let res = infcx
        .at(&dummy, param_env)
        .sub(infer::DefineOpaqueTypes::Yes, fn_sig, fn_with_free_vars)
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
    let mut map = HashMap::new();
    let mut temp_region_no = |region: ty::Region<'tcx>| -> usize {
        if region.is_var() {
            panic!("region is var");
        }
        let len = map.len();
        *map.entry(region).or_insert(len)
    };
    let mut subgraph = EdgePatterns::default();

    for (constraint, _) in region_constraint_data.constraints {
        let edge = match constraint {
            Constraint::VarSubVar(a, b) => EdgePattern(
                PatternNode::Named(a.as_usize()),
                PatternNode::Named(b.as_usize()),
            ),
            Constraint::RegSubVar(a, b) => EdgePattern(
                PatternNode::Temp(temp_region_no(a)),
                PatternNode::Named(b.as_usize()),
            ),
            Constraint::VarSubReg(a, b) => EdgePattern(
                PatternNode::Named(a.as_usize()),
                PatternNode::Temp(temp_region_no(b)),
            ),
            Constraint::RegSubReg(a, b) => EdgePattern(
                PatternNode::Temp(temp_region_no(a)),
                PatternNode::Temp(temp_region_no(b)),
            ),
        };
        subgraph.patterns.push(edge);
    }

    // extract constraints from where clauses of Fn
    let predicates = tcx.predicates_of(fn_did);
    predicates.predicates.iter().for_each(|(pred, _)| {
        if let Some(outlive_pred) = pred.as_region_outlives_clause() {
            let outlive_pred = outlive_pred.skip_binder();
            // lhs : rhs
            let (lhs, rhs) = (outlive_pred.0, outlive_pred.1);

            // build edge from rhs to lhs
            subgraph.patterns.push(EdgePattern(
                PatternNode::Temp(temp_region_no(rhs)),
                PatternNode::Temp(temp_region_no(lhs)),
            ));
        }
    });

    subgraph.named_region_num = folder.cnt();
    subgraph.temp_num = map.len();
    subgraph
}
