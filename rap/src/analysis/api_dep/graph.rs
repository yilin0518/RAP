use petgraph::dot::{Config, Dot};
use petgraph::graph::NodeIndex;
use petgraph::Graph;
use rustc_hir::def_id::DefId;
use rustc_middle::query::IntoQueryParam;
use rustc_middle::ty::{self, Ty, TyCtxt};
use std::collections::{HashMap, HashSet};
use std::fmt::Display;
use std::io::Write;
use std::path::Path;

use crate::utils::fs::rap_create_file;

#[derive(Clone, Copy, Eq, PartialEq, Hash, Debug)]
pub enum DepNode<'tcx> {
    Api(DefId),
    Ty(Ty<'tcx>),
    Region(Ty<'tcx>, usize)
    // Lifetime
}
pub enum DepEdge {
    Ty2Fn,
    Fn2Ty,
}

type InnerGraph<'tcx> = Graph<DepNode<'tcx>, ()>;
pub struct ApiDepGraph<'tcx> {
    graph: InnerGraph<'tcx>,
    node_indices: HashMap<DepNode<'tcx>, NodeIndex>,
    // lifetime_binding: HashMap<DepNode<'tcx>, DepNode<'tcx>> // whether the type has an lifetime binding. Type -> Lifetime
}

impl<'tcx> DepNode<'tcx> {
    pub fn api(id: impl IntoQueryParam<DefId>) -> DepNode<'tcx> {
        DepNode::Api(id.into_query_param())
    }
    pub fn ty(ty: Ty<'tcx>) -> DepNode<'tcx> {
        DepNode::Ty(ty)
    }
    pub fn region(ty: Ty<'tcx>, no: usize) -> DepNode<'tcx> {
        DepNode::Region(ty, no)
    }
    pub fn desc_str(&self, tcx: TyCtxt<'tcx>) -> String {
        match self {
            DepNode::Api(def_id) => tcx.def_path_str(def_id),
            DepNode::Ty(ty) => format!("{ty}"),
            DepNode::Region(ty, no) => format!("{ty}/{no}"),
        }
    }
}

// impl Display for DepNode {
//     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
//         f.
//         match self{
//             DepNode::Api(def_id) => std.
//             DepNode::Ty(hir_id) => todo!(),
//         }
//     }
// }

impl<'tcx> ApiDepGraph<'tcx> {
    pub fn new() -> ApiDepGraph<'tcx> {
        ApiDepGraph {
            graph: Graph::new(),
            node_indices: HashMap::new(),
        }
    }
    
    pub fn inner_graph(&self) -> &InnerGraph<'tcx>{
        &self.graph
    }

    pub fn get_node(&mut self, node: DepNode<'tcx>) -> NodeIndex {
        if let Some(node_index) = self.node_indices.get(&node) {
            *node_index
        } else {
            let node_index = self.graph.add_node(node);
            self.node_indices.insert(node, node_index);
            node_index
        }
    }

    pub fn add_edge(&mut self, src: NodeIndex, dst: NodeIndex) {
        self.graph.add_edge(src, dst, ());
    }

    pub fn dump_to_dot<P: AsRef<Path>>(&self, path: P, tcx: TyCtxt<'tcx>) {
        // let dot = Dot::with_config(&self.graph, &[Config::NodeIndexLabel]);
        let get_edge_attr = |graph, edge_ref| "".to_owned();
        let get_node_attr = |graph, node_ref: (NodeIndex, &DepNode<'tcx>)| {
            format!("label={:?}, ", node_ref.1.desc_str(tcx))
                + match node_ref.1 {
                    DepNode::Api(_) => "color = blue",
                    DepNode::Ty(_) => "color = red",
                    DepNode::Region(..) => "color = green",
                }

                + ", shape=box"
        };
    
        let dot = Dot::with_attr_getters(
            &self.graph,
            &[Config::NodeNoLabel, Config::EdgeNoLabel],
            &get_edge_attr,
            &get_node_attr,
        );
        let mut file = rap_create_file(path, "can not create dot file");
        write!(&mut file, "{:?}", dot).expect("fail when writing data to dot file");
        // println!("{:?}", dot);
    }
}

