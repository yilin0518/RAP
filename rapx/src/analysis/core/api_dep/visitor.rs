use super::graph::ApiDepGraph;
use super::graph::{DepEdge, DepNode};
use super::Config;
use crate::rap_debug;
use rustc_hir::{
    def_id::{DefId, LocalDefId},
    intravisit::{FnKind, Visitor},
    BodyId, BodyOwnerKind, FnDecl,
};
use rustc_middle::ty::{self, FnSig, ParamEnv, Ty, TyCtxt, TyKind};
use rustc_span::Span;
use std::io::Write;

fn is_api_public(fn_def_id: impl Into<DefId>, tcx: TyCtxt<'_>) -> bool {
    matches!(tcx.visibility(fn_def_id.into()), ty::Visibility::Public)
}

pub struct FnVisitor<'tcx, 'a> {
    fn_cnt: usize,
    tcx: TyCtxt<'tcx>,
    funcs: Vec<DefId>,
    config: Config,
    graph: &'a mut ApiDepGraph<'tcx>,
}

impl<'tcx, 'a> FnVisitor<'tcx, 'a> {
    pub fn new(
        graph: &'a mut ApiDepGraph<'tcx>,
        config: Config,
        tcx: TyCtxt<'tcx>,
    ) -> FnVisitor<'tcx, 'a> {
        let fn_cnt = 0;
        let funcs = Vec::new();
        FnVisitor {
            fn_cnt,
            tcx,
            graph,
            funcs,
            config,
        }
    }
    pub fn fn_cnt(&self) -> usize {
        self.fn_cnt
    }
    pub fn write_funcs<T: Write>(&self, f: &mut T) {
        for id in &self.funcs {
            write!(f, "{}\n", self.tcx.def_path_str(id)).expect("fail when write funcs");
        }
    }
}

impl<'tcx, 'a> Visitor<'tcx> for FnVisitor<'tcx, 'a> {
    fn visit_fn<'v>(
        &mut self,
        fk: FnKind<'v>,
        fd: &'v FnDecl<'v>,
        b: BodyId,
        span: Span,
        id: LocalDefId,
    ) -> Self::Result {
        let fn_did = id.to_def_id();
        let is_generic = self
            .tcx
            .generics_of(fn_did)
            .requires_monomorphization(self.tcx);
        if self.config.pub_only && !is_api_public(fn_did, self.tcx) {
            return;
        }
        if !self.config.include_generic_api && is_generic {
            return;
        }
        let res = if !is_generic {
            self.graph.add_api(fn_did, &[])
        } else {
            self.graph.add_generic_api(fn_did)
        };
        if res {
            self.fn_cnt += 1;
            self.funcs.push(fn_did);
        }
    }
}
