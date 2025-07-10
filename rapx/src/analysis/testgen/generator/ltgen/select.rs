use super::mono;
use crate::analysis::core::alias::{FnRetAlias, RetAlias};
use crate::analysis::core::api_dep::{graph::TransformKind, ApiDepGraph};
use crate::analysis::testgen::context::{ApiCall, Context, Var};
use crate::analysis::testgen::generator::ltgen::context::LtContext;
use crate::analysis::testgen::generator::ltgen::LtGen;
use crate::analysis::testgen::utils::{self};
use crate::{rap_debug, rap_info};
use itertools::Itertools;
use rand::rngs::ThreadRng;
use rand::{self, Rng};
use rustc_data_structures::fx::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::{self, GenericArgs, Ty, TyCtxt, TyKind};
use std::cell::RefCell;
use std::collections::HashSet;

impl<'tcx, 'a, R: Rng> LtGen<'tcx, 'a, R> {
    pub fn get_eligable_call(
        &self,
        fn_did: DefId,
        lt_ctxt: &mut LtContext<'tcx, 'a>,
    ) -> Option<ApiCall<'tcx>> {
        let tcx = self.tcx;

        let mut api_call = ApiCall {
            fn_did,
            args: Vec::new(),
            generic_args: GenericArgs::identity_for_item(tcx, fn_did),
        };

        if tcx.generics_of(fn_did).requires_monomorphization(tcx) {
            if !self.is_enable_monomorphization() {
                return None;
            }
            let available_ty =
                lt_ctxt
                    .cx()
                    .available_vars()
                    .fold(HashSet::new(), |mut set, var| {
                        set.insert(tcx.erase_regions(lt_ctxt.cx().type_of(var)));
                        set
                    });
            rap_debug!("generate mono API for {}", tcx.def_path_str(fn_did));
            rap_debug!("available types: {:?}", available_ty);
            let monos = mono::resolve_mono_apis(fn_did, available_ty, tcx);
            rap_debug!("monos: {:?}", monos);
            if monos.is_empty() {
                return None;
            }
            let idx = self.rng.borrow_mut().random_range(0..monos.count());
            let args = monos.args_at(idx);
            rap_debug!("choosed mono args: {args:?}");
            api_call.generic_args = tcx.mk_args(&args.value);
            // update api_graph
            if self.api_graph.borrow_mut().add_api(fn_did, &args.value) {
                self.api_graph.borrow_mut().update_transform_edges();
            }
        }

        let fn_sig =
            utils::fn_sig_with_generic_args(api_call.fn_did(), api_call.generic_args(), tcx);

        rap_debug!(
            "check eligible api: {}",
            tcx.def_path_str_with_args(api_call.fn_did, tcx.mk_args(&api_call.generic_args()))
        );
        for input_ty in fn_sig.inputs().iter() {
            rap_debug!("input_ty = {input_ty}");
            let providers = lt_ctxt.cx().all_possible_providers(*input_ty);
            if providers.is_empty() {
                rap_debug!("no possible providers");
                return None;
            }
            rap_debug!("providers: {providers:?}");
            let idx = self.rng.borrow_mut().random_range(0..providers.len());
            api_call.args.push(providers[idx].clone());
        }

        Some(api_call)
    }

    pub fn choose_eligable_api(
        &mut self,
        lt_ctxt: &mut LtContext<'tcx, 'a>,
    ) -> Option<ApiCall<'tcx>> {
        let mut eligable_calls = Vec::new();
        for fn_did in self.pub_api_def_id() {
            if let Some(call) = self.get_eligable_call(*fn_did, lt_ctxt) {
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

    pub fn choose_transform(
        &self,
        lt_ctxt: &mut LtContext<'tcx, 'a>,
    ) -> Option<(Var, TransformKind)> {
        let mut vec: Vec<(Var, TransformKind)> = Vec::new();
        for var in lt_ctxt.cx().available_vars() {
            let ty = lt_ctxt.cx().type_of(var);
            for transform in self.api_graph.borrow().all_transforms(ty) {
                vec.push((var, transform));
            }
        }
        rap_debug!("transform candidates: {vec:?}");
        if vec.is_empty() {
            return None;
        }
        let idx = self.rng.borrow_mut().random_range(0..vec.len());
        Some(vec.swap_remove(idx))
    }
}
