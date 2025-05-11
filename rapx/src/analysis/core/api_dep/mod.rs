/// NOTE: This analysis module is currently under development and is highly unstable.
/// The #[allow(unused)] attribute is applied to suppress excessive lint warnings.
/// Once the analysis stabilizes, this marker should be removed.

#[allow(unused)]
pub mod graph;
#[allow(unused)]
mod visitor;
use crate::{rap_debug, rap_info};
pub use graph::ApiDepGraph;
pub use graph::{DepEdge, DepNode};
use rustc_hir::def_id::LOCAL_CRATE;
use rustc_middle::ty::TyCtxt;

pub struct ApiDep<'tcx> {
    pub tcx: TyCtxt<'tcx>,
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, PartialOrd, Default)]
pub struct Config {
    pub pub_only: bool,
    pub include_generic_api: bool,
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

        let statistics = api_graph.statistics();
        // print all statistics
        rap_debug!(
            "API Graph contains {} API nodes, {} type nodes, {} generic parameter def nodes",
            statistics.api_count,
            statistics.type_count,
            statistics.generic_param_count
        );

        let dot_filename = format!("api_graph_{}_{}.dot", local_crate_name, local_crate_type);
        rap_info!("Dump API dependency graph to {}", dot_filename);
        api_graph.dump_to_dot(dot_filename, self.tcx);
        api_graph
    }
}
