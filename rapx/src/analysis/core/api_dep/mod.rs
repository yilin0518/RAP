/// NOTE: This analysis module is currently under development and is highly unstable.
/// The #[allow(unused)] attribute is applied to suppress excessive lint warnings.
/// Once the analysis stabilizes, this marker should be removed.

#[allow(unused)]
mod graph;
#[allow(unused)]
mod visitor;

use crate::{rap_debug, rap_info};
pub use graph::ApiDepGraph;
use rustc_hir::def_id::LOCAL_CRATE;
use rustc_middle::ty::TyCtxt;
pub use graph::{DepNode, DepEdge};
use visitor::FnVisitor;

pub struct ApiDep<'tcx> {
    pub tcx: TyCtxt<'tcx>,
}

impl<'tcx> ApiDep<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> ApiDep<'tcx> {
        ApiDep { tcx }
    }
    pub fn start(&self, all_pub_api: bool) -> ApiDepGraph<'tcx> {
        let local_crate_name = self.tcx.crate_name(LOCAL_CRATE);
        let local_crate_type = self.tcx.crate_types()[0];
        let graph_all_pub_api = if all_pub_api {
            "all APIs including private APIs"
        } else {
            "only public APIs"
        };
        rap_debug!(
            "Build API dependency graph on {} ({}), graph based on {}",
            local_crate_name.as_str(),
            local_crate_type,
            graph_all_pub_api,
        );

        let mut api_graph = ApiDepGraph::new(all_pub_api);
        let mut fn_visitor = FnVisitor::new(self.tcx, &mut api_graph);
        self.tcx
            .hir()
            .visit_all_item_likes_in_crate(&mut fn_visitor);
        rap_debug!("api-dep find {} APIs.", fn_visitor.fn_cnt());

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