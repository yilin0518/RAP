mod generator;
use crate::{rap_debug, rap_info};
use generator::context::Context;
use generator::ltgen::LtGen;
use generator::syn::FuzzDriverSynImpl;
use generator::syn::Synthesizer;
use generator::utils::{get_all_pub_apis, is_ty_impl_copy};
use rand;
use rustc_hir::def_id::LOCAL_CRATE;
use rustc_middle::query::Key;
use rustc_middle::ty::TyCtxt;

use super::core::{alias, api_dep};

/// Automatic Test Generator for detecting lifetime-related bugs
pub struct Testgen<'tcx> {
    pub tcx: TyCtxt<'tcx>,
}

impl<'tcx> Testgen<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Testgen<'tcx> {
        Testgen { tcx }
    }
    pub fn start(&self) {
        // check input and output type of all public APIs whether they implement Copy
        // for fn_did in get_all_pub_apis(self.tcx) {
        //     let fn_sig = self.tcx.liberate_late_bound_regions(
        //         fn_did,
        //         self.tcx.fn_sig(fn_did).instantiate_identity(),
        //     );
        //     for input_ty in fn_sig.inputs().iter() {
        //         if !is_ty_impl_copy(*input_ty, self.tcx) {
        //             rap_debug!("{}: {}", input_ty, "not implement Copy");
        //         }
        //     }
        //     let output_ty = fn_sig.output();
        //     if !is_ty_impl_copy(output_ty, self.tcx) {
        //         rap_debug!("{}: {}", output_ty, "not implement Copy");
        //     }
        // }
        // return;

        let _api_dep_graph = api_dep::ApiDep::new(self.tcx).start();
        let mut alias_analysis = alias::mop::MopAlias::new(self.tcx);
        let alias_map = alias_analysis.start();

        rap_debug!("result count = {}", alias_map.len());
        for (did, ret_alias) in alias_map.iter() {
            rap_debug!("{}: {:?}", self.tcx.def_path_str(did), ret_alias);
        }

        let local_crate_name = self.tcx.crate_name(LOCAL_CRATE);
        let local_crate_type = self.tcx.crate_types()[0];
        rap_info!(
            "Generate testcase on {} ({})",
            local_crate_name.as_str(),
            local_crate_type
        );
        let mut lt_gen = LtGen::new(self.tcx, rand::rng());
        let mut cx = Context::new(self.tcx);
        lt_gen.gen_in_place(&mut cx);
        let mut syn = FuzzDriverSynImpl::new();
        let fuzz_driver = syn.syn(cx, self.tcx);
        rap_debug!("{}", fuzz_driver);
    }
}
