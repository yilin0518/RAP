use crate::analysis::core::{alias, api_dep};
use crate::analysis::testgen::generator::ltgen::LtGenBuilder;
use crate::analysis::testgen::syn::impls::FuzzDriverSynImpl;
use crate::analysis::testgen::syn::input::SillyInputGen;
use crate::analysis::testgen::syn::project::{CargoProjectBuilder, RsProjectOption};
use crate::analysis::testgen::syn::{SynOption, Synthesizer};
use crate::{rap_error, rap_info, rap_warn};
use rustc_hir::def_id::LOCAL_CRATE;
use rustc_middle::ty::TyCtxt;
use serde::Deserialize;
use std::fs;
use std::io::Write;
use std::path::PathBuf;
use toml;

#[derive(Deserialize, Debug)]
pub struct LtGenConfig {
    pub max_complexity: usize,
    pub max_iteration: usize,
    pub build_dir: PathBuf,
    pub max_run: usize,
    #[serde(default = "default_mode")]
    pub mode: String,
    #[serde(rename = "override")]
    pub override_: bool,
}

fn default_mode() -> String {
    "nodebug".into()
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
    pub fn is_debug_mode(&self) -> bool {
        self.mode == "debug"
    }
    pub fn can_override(&self) -> bool {
        self.override_
    }
}

pub fn driver_main(tcx: TyCtxt<'_>) -> Result<(), Box<dyn std::error::Error>> {
    let mut config = LtGenConfig::load()?;
    let local_crate_name = tcx.crate_name(LOCAL_CRATE);

    let workspace_dir;

    if config.is_debug_mode() {
        workspace_dir = std::env::current_dir()?.join(format!("testgen_{}", local_crate_name));
        config.max_run = 1;
    } else {
        workspace_dir = config.build_dir.join(local_crate_name.as_str());
    }

    if (config.is_debug_mode() || config.can_override()) && fs::exists(&workspace_dir)? {
        fs::remove_dir_all(&workspace_dir)?;
    }

    fs::create_dir_all(&workspace_dir)?;

    let mut run_count = 0;

    let api_dep_graph = api_dep::ApiDep::new(tcx).start(api_dep::Config {
        pub_only: true,
        include_generic_api: false,
    });
    let mut alias_analysis = alias::mop::MopAlias::new(tcx);
    let alias_map = alias_analysis.start();

    let mut ltgen = LtGenBuilder::new(tcx, alias_map, api_dep_graph)
        .max_complexity(config.max_complexity)
        .max_iteration(config.max_iteration)
        .build();

    let mut report_file = std::fs::OpenOptions::new()
        .create(true)
        .read(true)
        .write(true)
        // .append(true)
        .open(workspace_dir.join("miri_report.txt"))?;

    let mut reports = Vec::new();
    let package_name = std::env::var("CARGO_PKG_NAME")?;
    let package_dir = std::env::var("CARGO_MANIFEST_DIR")?;

    while config.max_run == 0 || run_count < config.max_run {
        // 1. generate context
        let cx = ltgen.gen();

        // 2. synthesize Rust program
        let option = SynOption {
            crate_name: local_crate_name.to_string(),
        };
        let mut syn = FuzzDriverSynImpl::new(SillyInputGen, option);
        let rs_str = syn.syn(&cx, tcx);

        // 3. Build cargo project
        let project_name = format!("{}_case_{}", local_crate_name, run_count);
        let project_path = workspace_dir.join(&project_name);
        let debug_path = project_path.as_path().join("region_graph.dot");

        let fuzz_config = RsProjectOption {
            tested_crate_name: (&package_name).into(),
            tested_crate_path: (&package_dir).into(),
            project_name,
            project_path,
            verbose: true,
        };

        let project_builder = CargoProjectBuilder::new(fuzz_config);
        let project = project_builder.build()?;
        project.create_src_file("main.rs", &rs_str)?;
        // output debug file
        let mut file = std::fs::File::create(debug_path)?;
        cx.region_graph().dump(&mut file).unwrap();

        // 4. run miri & save feedback
        let report = project.run_miri()?;
        let delimeter = "=".repeat(40);

        writeln!(&mut report_file, "{}", delimeter)?;
        writeln!(&mut report_file, "{}", report.brief())?;
        writeln!(&mut report_file, "{}", delimeter)?;

        match report.retcode {
            Some(retcode) => {
                rap_info!("miri run completed with return code: {}", retcode);
                if retcode != 0 {
                    rap_warn!(
                        "miri return a non-zero code ({retcode}), this may indicate a bug detected"
                    );
                }
            }
            None => {
                rap_error!(
                    "Faile to run miri for {}: Execution is interrupted",
                    report.project_name
                );
            }
        }

        reports.push(report);
        run_count += 1;
    }

    ltgen
        .api_graph()
        .borrow()
        .dump_to_dot(workspace_dir.join("api_graph.dot"), tcx);

    writeln!(&mut report_file, "{}", ltgen.statistic_str())?;

    rap_info!("non-zero returned:");
    for report in reports {
        if report.retcode.unwrap_or(-1) == 0 {
            continue;
        }
        rap_warn!(
            "case = {}, retcode = {:?}",
            report.project_name,
            report.retcode
        );
    }

    Ok(())
}
