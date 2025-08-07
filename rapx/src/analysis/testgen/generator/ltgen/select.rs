use crate::analysis::testgen::context::ApiCall;
use crate::analysis::testgen::generator::ltgen::context::LtContext;
use crate::analysis::testgen::generator::ltgen::LtGen;
use crate::analysis::testgen::utils::{self};
use crate::rap_debug;
use rand::{self, Rng};
use rustc_hir::def_id::DefId;
use rustc_middle::ty::{self};

impl<'tcx, 'a, R: Rng> LtGen<'tcx, 'a, R> {
    pub fn get_eligable_call(
        &self,
        fn_did: DefId,
        args: ty::GenericArgsRef<'tcx>,
        lt_ctxt: &mut LtContext<'tcx, 'a>,
    ) -> Option<ApiCall<'tcx>> {
        let tcx = self.tcx;

        let mut api_call = ApiCall {
            fn_did,
            args: Vec::new(),
            generic_args: args,
        };

        let fn_sig =
            utils::fn_sig_with_generic_args(api_call.fn_did(), api_call.generic_args(), tcx);

        rap_debug!(
            "check eligible api: {}",
            tcx.def_path_str_with_args(api_call.fn_did, tcx.mk_args(&api_call.generic_args()))
        );
        let mut moved_vars = Vec::new();
        for input_ty in fn_sig.inputs().iter() {
            rap_debug!("input_ty = {input_ty}");
            let providers = lt_ctxt.cx().all_possible_providers(*input_ty);
            if providers.is_empty() {
                rap_debug!("no possible providers");
                return None;
            }
            let mut fail_count = 0;
            loop {
                if fail_count >= 5 {
                    return None;
                }
                rap_debug!("providers: {providers:?}");
                let idx = self.rng.borrow_mut().random_range(0..providers.len());

                // the provider is moved by another arg, try again
                if !lt_ctxt.is_var_impl_copy(providers[idx]) && moved_vars.contains(&providers[idx])
                {
                    fail_count += 1;
                    continue;
                }
                api_call.args.push(providers[idx].clone());
                if !lt_ctxt.is_var_impl_copy(providers[idx]) {
                    moved_vars.push(providers[idx]);
                }
                break;
            }
        }

        Some(api_call)
    }
}
