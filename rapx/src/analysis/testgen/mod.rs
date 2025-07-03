mod context;
mod driver;
mod generator;
mod syn;
mod utils;

use crate::analysis::testgen::driver::driver_main;
use crate::{rap_error, rap_info};
use rustc_middle::ty::TyCtxt;
use rustc_session::config::CrateType;

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

    pub fn start(&self, test_crate: Option<&str>) {
        if matches!(self.tcx.crate_types()[0], CrateType::Executable) {
            rap_info!("Skip executable target");
            return;
        }

        if let Some(test_crate) = test_crate {
            let package_name =
                std::env::var("CARGO_PKG_NAME").expect("cannot capture env var `CARGO_PKG_NAME`");
            if package_name != test_crate {
                return;
            }
        }

        match driver_main(self.tcx) {
            Ok(_) => rap_info!("testgen completed successfully"),
            Err(e) => rap_error!("testgen failed:\n{}", e),
        }
    }
}
