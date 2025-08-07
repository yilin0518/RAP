/// NOTE: This analysis module is currently under development and is highly unstable.
/// The #[allow(unused)] attribute is applied to suppress excessive lint warnings.
/// Once the analysis stabilizes, this marker should be removed.

#[allow(unused)]
pub mod graph;
mod mono;
mod utils;
#[allow(unused)]
mod visitor;

use crate::{rap_debug, rap_info, rap_trace};
pub use graph::ApiDepGraph;
pub use graph::{DepEdge, DepNode};
use rustc_hir::def_id::{DefId, LOCAL_CRATE};
use rustc_middle::ty::{self, Ty, TyCtxt};
pub struct ApiDep<'tcx> {
    pub tcx: TyCtxt<'tcx>,
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, PartialOrd, Default)]
pub struct Config {
    pub pub_only: bool,
    pub resolve_generic: bool,
    pub ignore_const_generic: bool,
}

pub fn is_def_id_public(fn_def_id: impl Into<DefId>, tcx: TyCtxt<'_>) -> bool {
    let fn_def_id: DefId = fn_def_id.into();
    let local_id = fn_def_id.expect_local();
    rap_trace!(
        "vis: {:?} (path: {}) => {:?}",
        fn_def_id,
        tcx.def_path_str(fn_def_id),
        tcx.effective_visibilities(()).effective_vis(local_id)
    );
    tcx.effective_visibilities(()).is_directly_public(local_id)
    // || tcx.effective_visibilities(()).is_exported(local_id)
}

impl<'tcx> ApiDep<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> ApiDep<'tcx> {
        ApiDep { tcx }
    }
    pub fn start(&self, config: Config) -> ApiDepGraph<'tcx> {
        let local_crate_name = self.tcx.crate_name(LOCAL_CRATE);
        let local_crate_type = self.tcx.crate_types()[0];
        rap_debug!(
            "Build API dependency graph on {} ({}), config = {:?}",
            local_crate_name.as_str(),
            local_crate_type,
            config,
        );
        let mut api_graph = ApiDepGraph::new(self.tcx);
        api_graph.build(config);

        let (estimate, total) = api_graph.estimate_coverage(self.tcx);

        let statistics = api_graph.statistics();
        // print all statistics
        rap_info!(
            "API Graph contains {} API nodes, {} type nodes, {} edges",
            statistics.api_count,
            statistics.type_count,
            statistics.edge_cnt
        );
        rap_info!(
            "estimate coverage: {:.2} ({}/{})",
            estimate as f64 / total as f64,
            estimate,
            total
        );
        let dot_filename = format!("api_graph_{}_{}.dot", local_crate_name, local_crate_type);
        rap_info!("Dump API dependency graph to {}", dot_filename);
        api_graph.dump_to_dot(dot_filename, self.tcx);
        api_graph
    }
}
