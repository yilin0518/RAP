use crate::analysis::core::{alias, api_dep};
use crate::analysis::testgen::generator::ltgen::LtGenBuilder;
use crate::analysis::testgen::syn::impls::FuzzDriverSynImpl;
use crate::analysis::testgen::syn::input::SillyInputGen;
use crate::analysis::testgen::syn::project::{CargoProjectBuilder, RsProjectOption};
use crate::analysis::testgen::syn::{SynOption, Synthesizer};
use crate::{analysis, rap_debug, rap_error, rap_info, rap_warn};
use rustc_hir::def_id::LOCAL_CRATE;
use rustc_middle::ty::TyCtxt;
use serde::Deserialize;
use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};
use toml;

#[derive(Deserialize)]
pub struct LtGenConfig {
    pub max_complexity: usize,
    pub max_iteration: usize,
    pub build_dir: PathBuf,
    pub max_run: usize,
}

impl LtGenConfig {
    pub fn load() -> Result<Self, Box<dyn std::error::Error>> {
        let config_path = std::env::home_dir()
            .expect("Cannot find homedir")
            .join(".ltgenconfig");
        let contents = fs::read_to_string(config_path)?;
        let config: LtGenConfig = toml::from_str(&contents)?;
        Ok(config)
    }
}

pub fn driver_main(tcx: TyCtxt<'_>) -> Result<(), Box<dyn std::error::Error>> {
    let config = LtGenConfig::load()?;

    let local_crate_name = tcx.crate_name(LOCAL_CRATE);
    let build_dir = PathBuf::from(&config.build_dir);
    let workspace_dir = build_dir.join(local_crate_name.as_str());
    fs::create_dir_all(&workspace_dir)?;

    let mut run_count = 0;

    let api_dep_graph = api_dep::ApiDep::new(tcx).start(api_dep::Config {
        pub_only: true,
        include_generic_api: false,
    });
    let mut alias_analysis = alias::mop::MopAlias::new(tcx);
    let alias_map = alias_analysis.start();

    let mut lt_gen = LtGenBuilder::new(tcx, alias_map, api_dep_graph)
        .max_complexity(config.max_complexity)
        .max_iteration(config.max_iteration)
        .build();

    let mut report_file = std::fs::OpenOptions::new()
        .create(true)
        .read(true)
        .write(true)
        // .append(true)
        .open(workspace_dir.join("miri_report.txt"))?;

    while config.max_run == 0 || run_count < config.max_run {
        // 1. generate context
        let cx = lt_gen.gen();

        // 2. synthesize Rust program
        let option = SynOption {
            crate_name: local_crate_name.to_string(),
        };
        let mut syn = FuzzDriverSynImpl::new(SillyInputGen, option);
        let rs_str = syn.syn(cx, tcx);

        // 3. Build cargo project
        let project_name = format!("{}_case_{}", local_crate_name, run_count);
        let project_path = workspace_dir.join(&project_name);

        let fuzz_config = RsProjectOption {
            tested_crate_name: local_crate_name.to_string(),
            tested_crate_path: std::env::current_dir()?,
            project_name,
            project_path,
            verbose: true,
        };

        let project_builder = CargoProjectBuilder::new(fuzz_config);
        let project = project_builder.build()?;
        project.create_src_file("main.rs", &rs_str)?;

        // 4. run miri & save feedback
        let report = project.run_miri()?;
        let delimeter = "=".repeat(40);

        writeln!(&mut report_file, "{}", delimeter)?;
        writeln!(&mut report_file, "{}", report.brief())?;
        writeln!(&mut report_file, "{}", delimeter)?;

        // {
        //     Some(retcode) => {
        //         rap_info!("miri run completed with return code: {}", retcode);
        //         if retcode != 0 {
        //             rap_warn!(
        //                 "miri return a non-zero code ({retcode}), this may indicate a bug detected"
        //             );
        //         }
        //     }
        //     None => {
        //         rap_error!(
        //             "Faile to run miri for {}: Execution is interrupted",
        //             project_name
        //         );
        //     }
        // }

        run_count += 1;
    }

    Ok(())
}
