use crate::rap_debug;

use super::context::{ApiCall, ArgSrc, Context};
use super::{utils, Generator};
use rand::{self, Rng};
use rustc_hir::def_id::DefId;
use rustc_middle::ty::{self, Ty, TyCtxt, TyKind};

pub struct LtGen<'tcx, R: Rng> {
    pub_api: Vec<DefId>,
    tcx: TyCtxt<'tcx>,
    rng: R,
    // current: Context<'tcx>
}

impl<'tcx, R: Rng> LtGen<'tcx, R> {
    pub fn new(tcx: TyCtxt<'tcx>, rng: R) -> LtGen<'tcx, R> {
        LtGen {
            pub_api: utils::get_all_pub_apis(tcx),
            tcx,
            rng,
        }
    }

    pub fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    pub fn pub_api_def_id(&self) -> &[DefId] {
        &self.pub_api
    }

    pub fn try_initiate_for_ty_with<'cx>(
        &self,
        cx: &Context<'cx>,
        ty: Ty<'tcx>,
    ) -> Option<ApiCall<'cx>> {
        todo!()
    }

    pub fn is_api_eligable<'cx>(&self, fn_did: DefId) -> Option<ApiCall<'cx>> {
        let tcx = self.tcx();
        let early_fn_sig = tcx.fn_sig(fn_did);
        let mut api_call = ApiCall {
            fn_did,
            args: Vec::new(),
        };
        rap_debug!("consider: {:?}", fn_did);
        // TODO: now only consider fn_sig without type & const parameters
        if !tcx.generics_of(fn_did).requires_monomorphization(tcx) {
            let binder_fn_sig = early_fn_sig.instantiate_identity();
            let fn_sig = binder_fn_sig.skip_binder();
            for input_ty in fn_sig.inputs().iter() {
                rap_debug!("check: {input_ty:?}");
                if utils::is_fuzzable_ty(*input_ty) {
                    api_call.args.push(ArgSrc::input());
                } else {
                    return None;
                }
            }
        }
        Some(api_call)
    }

    fn choose_eligable_api(&mut self, cx: &Context<'_>) -> Option<ApiCall> {
        let tcx = self.tcx();
        let mut eligable_calls = Vec::new();
        for fn_did in self.pub_api_def_id() {
            if let Some(call) = self.is_api_eligable(*fn_did) {
                eligable_calls.push(call);
            }
        }
        if eligable_calls.is_empty() {
            return None;
        }
        rap_debug!("eligable calls: {eligable_calls:?}");
        let idx = self.rng.random_range(0..eligable_calls.len());
        let choosed = &eligable_calls[idx];
        let name = tcx.def_path_str(choosed.fn_did);
        rap_debug!("finally choose: {name}");
        Some(eligable_calls.swap_remove(idx))
    }
}

impl<'tcx, R: Rng> Generator for LtGen<'tcx, R> {
    fn gen_in_place<'cx>(&mut self, cx: &mut super::context::Context<'cx>) {
        let api = self.choose_eligable_api(cx);
    }
}
