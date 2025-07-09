use super::statistic::Statistics;
use crate::{rap_debug, rap_info, rap_trace};
use rustc_hir::{
    def_id::{DefId, LocalDefId},
    intravisit::{walk_block, walk_fn, FnKind, Visitor},
    BodyId, BodyOwnerKind, FnDecl,
};
use rustc_middle::{
    hir::nested_filter,
    ty::{self, FnSig, ParamEnv, Ty, TyCtxt, TyKind},
};
use rustc_span::Span;
use std::io::Write;

pub struct FnVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    stats: Statistics<'tcx>,
}

fn is_api_public(fn_def_id: impl Into<DefId>, tcx: TyCtxt<'_>) -> bool {
    let fn_def_id: DefId = fn_def_id.into();
    let local_id = fn_def_id.expect_local();
    rap_trace!(
        "vis: {:?} (path: {}) => {:?}",
        fn_def_id,
        tcx.def_path_str(fn_def_id),
        tcx.effective_visibilities(()).effective_vis(local_id)
    );
    tcx.effective_visibilities(()).is_directly_public(local_id)
    // || tcx.effective_visibilities(()).is_exported(local_id)
}

impl<'tcx> FnVisitor<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> FnVisitor<'tcx> {
        FnVisitor {
            tcx,
            stats: Statistics::default(),
        }
    }
    pub fn statistic(self) -> Statistics<'tcx> {
        self.stats
    }
    fn work_at_fn<'v>(
        &mut self,
        fk: FnKind<'v>,
        fd: &'v FnDecl<'v>,
        b: BodyId,
        span: Span,
        id: LocalDefId,
    ) {
        let fn_did = id.to_def_id();

        if !is_api_public(fn_did, self.tcx) {
            return;
        }

        let is_generic = self
            .tcx
            .generics_of(fn_did)
            .requires_monomorphization(self.tcx);
        let fn_sig = self.tcx.fn_sig(fn_did);

        if is_generic {
            self.stats.pub_generic_api.insert(fn_did);
        } else {
            self.stats.pub_non_generic_api.insert(fn_did);
        }

        if fk.header().map_or(false, |header| header.is_unsafe()) {
            self.stats.pub_unsafe_api.insert(fn_did);
        }
    }
}

impl<'tcx> Visitor<'tcx> for FnVisitor<'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.tcx
    }

    fn visit_fn(
        &mut self,
        fk: FnKind<'tcx>,
        fd: &'tcx FnDecl<'tcx>,
        b: BodyId,
        span: Span,
        id: LocalDefId,
    ) -> Self::Result {
        self.work_at_fn(fk, fd, b, span, id);
        walk_fn(self, fk, fd, b, id);
    }

    fn visit_block(&mut self, b: &'tcx rustc_hir::Block<'tcx>) -> Self::Result {
        let r = b.rules;
        if matches!(r, rustc_hir::BlockCheckMode::UnsafeBlock(_)) {
            self.stats.unsafe_block.push(*b)
        }
        walk_block(self, b);
    }
}
