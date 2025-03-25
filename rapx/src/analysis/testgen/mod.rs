mod generator;
use std::fs::File;
use std::io::Write;
use std::path::Path;

use crate::{rap_debug, rap_info};
use generator::context::Context;
use generator::input::SillyInputGen;
use generator::ltgen::LtGen;
use generator::syn::FuzzDriverSynImpl;
use generator::syn::SynOption;
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
        // build option
        let option = SynOption {
            crate_name: local_crate_name.to_string(),
        };
        let mut syn = FuzzDriverSynImpl::new(SillyInputGen, option);
        let rs_str = syn.syn(cx, self.tcx);

        let output_path = Path::new("fuzz_driver.rs");
        let mut file = File::create(output_path).unwrap();
        file.write_all(rs_str.as_bytes()).unwrap();

        rap_debug!("{}", rs_str);
    }
}
