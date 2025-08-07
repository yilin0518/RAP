mod statistic;
/// NOTE: This analysis module is currently under development and is highly unstable.
/// The #[allow(unused)] attribute is applied to suppress excessive lint warnings.
/// Once the analysis stabilizes, this marker should be removed.

#[allow(unused)]
mod visitor;
use crate::{analysis::scan::visitor::FnVisitor, rap_debug, rap_info, rap_trace};
use rustc_hir::def_id::{DefId, LOCAL_CRATE};
use rustc_middle::ty::TyCtxt;
use rustc_session::config::CrateType;

pub struct ScanAnalysis<'tcx> {
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> ScanAnalysis<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        ScanAnalysis { tcx }
    }
    pub fn start(&self) {
        let crate_name = self.tcx.crate_name(LOCAL_CRATE);
        let crate_type = self.tcx.crate_types()[0];
        rap_info!("Scan crate: {}", crate_name.as_str());
        let mut fn_visitor = FnVisitor::new(self.tcx);
        self.tcx.hir_visit_all_item_likes_in_crate(&mut fn_visitor);
        let stats = fn_visitor.statistic();
        stats.info().print_log();
    }
}
