mod generator;
use generator::context::Context;
use generator::ltgen::LtGen;
use generator::Generator;
use rand;
use rustc_hir::def_id::LOCAL_CRATE;
use rustc_middle::ty::TyCtxt;

use crate::{rap_debug, rap_info};

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
        let mut cx = Context::new();
        lt_gen.gen_in_place(&mut cx);
    }
}
