use crate::analysis::core::alias_analysis::{AAResultMap, AliasAnalysis};
use crate::analysis::core::api_dependency::ApiDependencyAnalysis;
use crate::analysis::core::{alias_analysis, api_dependency};
use crate::analysis::testgen::generator::ltgen::LtGenBuilder;
use crate::analysis::testgen::syn::impls::FuzzDriverSynImpl;
use crate::analysis::testgen::syn::input::RandomGen;
use crate::analysis::testgen::syn::project::{CargoProjectBuilder, RsProjectOption, TestResult};
use crate::analysis::testgen::syn::{SynOption, Synthesizer};
use crate::analysis::Analysis;
use crate::{rap_error, rap_info, rap_warn};
use rustc_hir::def_id::LOCAL_CRATE;
use rustc_middle::ty::TyCtxt;
use serde::Deserialize;
use std::io::Write;
use std::path::Path;
use std::{fs, io};
use toml;

#[derive(Deserialize, Debug)]
pub struct LtGenConfig {
    pub max_complexity: usize,
    pub max_iteration: usize,
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
    pub fn load() -> io::Result<Self> {
        let mut current_dir = std::env::current_dir()?;

        loop {
            let config_path = current_dir.join(".ltgenconfig");
            if config_path.exists() {
                rap_debug!("load config file from: {}", config_path.display());
                return Self::load_from(config_path);
            }

            if !current_dir.pop() {
                return Err(io::Error::new(
                    io::ErrorKind::NotFound,
                    "Could not find .ltgenconfig in any parent directory",
                ));
            }
        }
    }

    pub fn load_from<P: AsRef<Path>>(path: P) -> io::Result<Self> {
        let path = path.as_ref();
        let contents = fs::read_to_string(&path)?;
        let config: LtGenConfig = toml::from_str(&contents)
            .expect(&format!("cannot parse the content of {}", path.display()));
        Ok(config)
    }

    pub fn is_debug_mode(&self) -> bool {
        self.mode == "debug"
    }
    pub fn can_override(&self) -> bool {
        self.override_
    }
}

pub fn dump_alias_map(
    alias_map: &AAResultMap,
    mut os: impl Write,
    tcx: TyCtxt<'_>,
) -> Result<(), Box<dyn std::error::Error>> {
    for (did, aliases) in alias_map {
        if tcx.is_closure_like(*did) {
            continue;
        }
        writeln!(
            os,
            "{} : {} = {}",
            tcx.def_path_str(did),
            tcx.fn_sig(did).instantiate_identity().skip_binder(),
            aliases
        )?;
    }
    Ok(())
}

pub fn driver_main(tcx: TyCtxt<'_>) -> Result<(), Box<dyn std::error::Error>> {
    let mut config = LtGenConfig::load()?;
    let local_crate_name = tcx.crate_name(LOCAL_CRATE);
    rap_info!("run on crate: {}", local_crate_name);

    let workspace_dir = std::env::current_dir()?.join("testgen");

    if config.is_debug_mode() {
        config.max_run = 1;
    }

    if (config.is_debug_mode() || config.can_override()) && fs::exists(&workspace_dir)? {
        rap_info!(
            "removing existing workspace directory: {}",
            workspace_dir.display()
        );
        fs::remove_dir_all(&workspace_dir)?;
    }

    fs::create_dir_all(&workspace_dir)?;

    let mut run_count = 0;

    let mut api_analyzer = api_dependency::ApiDependencyAnalyzer::new(
        tcx,
        api_dependency::Config {
            pub_only: true,
            resolve_generic: true,
            ignore_const_generic: true,
            include_unsafe: false,
        },
    );
    api_analyzer.run();
    let api_dep_graph = api_analyzer.get_api_dependency_graph();

    api_dep_graph.dump_to_dot(workspace_dir.join("api_graph.dot"));

    let mut alias_analyzer = alias_analysis::default::AliasAnalyzer::new(tcx);
    alias_analyzer.run();
    let alias_map = alias_analyzer.get_all_fn_alias();

    let alias_file = std::fs::OpenOptions::new()
        .create(true)
        .read(true)
        .write(true)
        .open(workspace_dir.join("alias_file.txt"))?;

    dump_alias_map(&alias_map, alias_file, tcx)?;

    let mut ltgen = LtGenBuilder::new(tcx, &alias_map, api_dep_graph)
        .max_complexity(config.max_complexity)
        .max_iteration(config.max_iteration)
        .build();

    let report_path = workspace_dir.join("miri_report.txt");

    let mut report_file = std::fs::OpenOptions::new()
        .create(true)
        .read(true)
        .write(true)
        .open(&report_path)?;

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
        let mut syn = FuzzDriverSynImpl::new(RandomGen::new(), option);
        let rs_str = syn.syn(cx.cx(), tcx);

        // 3. Build cargo project
        let project_name = format!("case{}", run_count);
        let project_path = workspace_dir.join(&project_name);
        let debug_path = project_path.as_path().join("region_graph.dot");

        let fuzz_config = RsProjectOption {
            tested_crate_name: (&package_name).into(),
            tested_crate_path: (&package_dir).into(),
            project_name: project_name.clone(),
            project_path: project_path.clone(),
            verbose: true,
        };

        let project_builder = CargoProjectBuilder::new(fuzz_config);
        let project = project_builder.build()?;
        project.create_src_file("main.rs", &rs_str)?;
        // output debug file
        let mut file = std::fs::File::create(debug_path)?;
        cx.region_graph().dump(&mut file).unwrap();

        // 4. run miri & save feedback
        let delimeter = "=".repeat(40);
        let report = project.run_miri()?;

        writeln!(&mut report_file, "{}", delimeter)?;
        writeln!(&mut report_file, "{}", report.brief())?;
        writeln!(&mut report_file, "{}", delimeter)?;

        match report.result {
            TestResult::FailInCheck(retcode) => {
                rap_error!("running `cargo check` fail (retcode = {retcode:?}). This may due to the compile error");
            }
            TestResult::RunSuccess(retcode) => match retcode {
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
            },
        }

        reports.push(report);
        run_count += 1;
    }

    writeln!(&mut report_file, "{}", ltgen.statistic_str())?;

    rap_info!("non-zero returned:");
    for report in reports {
        if report.get_retcode().unwrap_or(-1) == 0 {
            continue;
        }
        rap_warn!(
            "case = {}, retcode = {:?}",
            report.project_name,
            report.get_retcode()
        );
    }

    rap_info!("report saved to: {}", report_path.display());

    Ok(())
}
