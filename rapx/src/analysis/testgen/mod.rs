mod context;
mod generator;
mod syn;
mod utils;

use rand;

use crate::analysis::core::{alias, api_dep};
use crate::{rap_debug, rap_info};
use context::ContextBase;
use generator::ltgen::context::LtContext;
use generator::ltgen::{initialize_subgraph_map, LtGenBuilder};
use generator::rulf;
use rustc_hir::def_id::LOCAL_CRATE;
use rustc_middle::ty::TyCtxt;
use std::fs::File;
use std::io::Write;
use std::path::Path;
use syn::input::SillyInputGen;
use syn::{FuzzDriverSynImpl, SynOption, Synthesizer};

/// Automatic Test Generator for detecting lifetime-related bugs
pub struct Testgen<'tcx> {
    pub tcx: TyCtxt<'tcx>,
}

impl<'tcx> Testgen<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Testgen<'tcx> {
        Testgen { tcx }
    }

    pub fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    pub fn start(&self) {
        let mut _api_dep_graph = api_dep::ApiDep::new(self.tcx()).start(true);
        let mut alias_analysis = alias::mop::MopAlias::new(self.tcx());
        let alias_map = alias_analysis.start();

        rap_debug!("result count = {}", alias_map.len());
        // for (did, ret_alias) in alias_map.iter() {
        //     rap_debug!("{}: {:?}", self.tcx.def_path_str(did), ret_alias);
        // }

        let local_crate_name = self.tcx.crate_name(LOCAL_CRATE);
        let local_crate_type = self.tcx.crate_types()[0];
        rap_info!(
            "Generate testcase on {} ({})",
            local_crate_name.as_str(),
            local_crate_type
        );

        //rulf
        let mut cx: ContextBase<'tcx> = ContextBase::new(self.tcx);
        let mut rng = rand::rng();
        rulf::rulf_algorithm(self.tcx, &mut _api_dep_graph, 3, &mut cx, &mut rng);
        // for stmt in cx.stmts(){
        //     rap_info!("stmt: {:?}", stmt);
        // }

        // let mut lt_gen = LtGenBuilder::new(self.tcx, alias_map)
        //     .max_complexity(10)
        //     .build();
        // let subgraph_map = initialize_subgraph_map(self.tcx());
        // let mut cx = LtContext::new(self.tcx, &subgraph_map);
        // // lt_gen.check_all_vulnerable_api();
        // lt_gen.gen_in_place(&mut cx);
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
