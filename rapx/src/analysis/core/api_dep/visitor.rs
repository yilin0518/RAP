use super::graph::ApiDepGraph;
use super::graph::{DepEdge, DepNode};
use super::is_def_id_public;
use super::Config;
use crate::analysis::core::api_dep::mono;
use crate::{rap_debug, rap_trace};
use rustc_hir::{
    def_id::{DefId, LocalDefId},
    intravisit::{FnKind, Visitor},
    BodyId, BodyOwnerKind, FnDecl,
};
use rustc_middle::ty::{self, FnSig, ParamEnv, Ty, TyCtxt, TyKind};
use rustc_span::Span;
use std::io::Write;

pub struct FnVisitor<'tcx, 'a> {
    tcx: TyCtxt<'tcx>,
    apis: Vec<DefId>,
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
            tcx,
            graph,
            apis: funcs,
            config,
        }
    }

    pub fn count_api(&self) -> usize {
        self.apis.len()
    }

    pub fn apis(self) -> Vec<DefId> {
        self.apis
    }

    pub fn write_funcs<T: Write>(&self, f: &mut T) {
        for id in &self.apis {
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
        if self.config.pub_only && !is_def_id_public(fn_did, self.tcx) {
            return;
        }
        if !self.config.resolve_generic && is_generic {
            return;
        }

        if !is_generic {
            let args = ty::GenericArgs::identity_for_item(self.tcx, fn_did);
            self.graph.add_api(fn_did, &args);
        }

        self.apis.push(fn_did);
    }
}
