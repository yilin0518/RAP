use super::context::stmt::{ApiCall, Stmt};
use super::context::Context;
use super::{utils, Generator};
use crate::analysis::testgen::generator::utils::jump_all_binders;
use crate::rap_debug;
use rand::{self, Rng};
use rustc_hir::def_id::DefId;
use rustc_infer::infer::TyCtxtInferExt;
use rustc_middle::ty::{self, Ty, TyCtxt, TyKind};
use rustc_span::Span;
use std::cell::RefCell;

pub struct LtGen<'tcx, R: Rng> {
    pub_api: Vec<DefId>,
    tcx: TyCtxt<'tcx>,
    rng: RefCell<R>,
    // current: Context<'tcx>
}

impl<'tcx, R: Rng> LtGen<'tcx, R> {
    pub fn new(tcx: TyCtxt<'tcx>, rng: R) -> LtGen<'tcx, R> {
        LtGen {
            pub_api: utils::get_all_pub_apis(tcx),
            tcx,
            rng: RefCell::new(rng),
        }
    }

    pub fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    pub fn pub_api_def_id(&self) -> &[DefId] {
        &self.pub_api
    }

    pub fn is_api_eligable(&self, fn_did: DefId, cx: &Context<'tcx>) -> Option<ApiCall> {
        let tcx = self.tcx();

        let mut api_call = ApiCall {
            fn_did,
            args: Vec::new(),
        };
        rap_debug!("consider: {:?}", fn_did);

        // TODO: now only consider fn_sig without type & const parameters
        if tcx.generics_of(fn_did).requires_monomorphization(tcx) {
            return None;
        }
        let fn_sig = jump_all_binders(fn_did, tcx);

        for input_ty in fn_sig.inputs().iter() {
            rap_debug!("check: {input_ty:?}");
            let providers = cx.all_possible_providers(*input_ty);
            if providers.is_empty() {
                rap_debug!("no possible providers");
                return None;
            }
            let idx = self.rng.borrow_mut().random_range(0..providers.len());
            api_call.args.push(providers[idx].clone());
        }

        Some(api_call)
    }

    fn choose_eligable_api(&self, cx: &Context<'tcx>) -> Option<ApiCall> {
        let mut eligable_calls = Vec::new();
        for fn_did in self.pub_api_def_id() {
            if let Some(call) = self.is_api_eligable(*fn_did, cx) {
                eligable_calls.push(call);
            }
        }
        if eligable_calls.is_empty() {
            return None;
        }
        rap_debug!("eligable calls: {eligable_calls:?}");
        let idx = self.rng.borrow_mut().random_range(0..eligable_calls.len());
        Some(eligable_calls.swap_remove(idx))
    }

    pub fn gen_in_place(&mut self, cx: &mut Context<'tcx>) {
        let mut count = 0;
        while let Some(call) = self.choose_eligable_api(cx) {
            cx.add_call_stmt(call);
            count += 1;
            if count >= 5 {
                break;
            }
        }
    }
}
