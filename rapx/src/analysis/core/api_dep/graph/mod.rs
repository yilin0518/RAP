pub mod dep_edge;
pub mod dep_node;
mod resolve;
pub mod transform;
mod ty_wrapper;

use super::Config;
use crate::analysis::core::api_dep::utils;
use crate::analysis::core::api_dep::visitor::FnVisitor;
use crate::analysis::utils::def_path::path_str_def_id;
use crate::rap_debug;
use crate::rap_trace;
use crate::utils::fs::rap_create_file;
pub use dep_edge::DepEdge;
pub use dep_node::{desc_str, DepNode};
use petgraph::dot;
use petgraph::graph::NodeIndex;
use petgraph::visit::EdgeRef;
use petgraph::Direction;
use petgraph::Graph;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::Binder;
use rustc_middle::ty::{self, Ty, TyCtxt};
use std::collections::HashMap;
use std::collections::HashSet;
use std::collections::VecDeque;
use std::hash::Hash;
use std::io::Write;
use std::path::Path;
pub use transform::TransformKind;
pub use ty_wrapper::TyWrapper;

type InnerGraph<'tcx> = Graph<DepNode<'tcx>, DepEdge>;
pub struct ApiDepGraph<'tcx> {
    graph: InnerGraph<'tcx>,
    node_indices: HashMap<DepNode<'tcx>, NodeIndex>,
    ty_nodes: Vec<NodeIndex>,
    api_nodes: Vec<NodeIndex>,
    all_apis: HashSet<DefId>,
    tcx: TyCtxt<'tcx>,
}

pub struct Statistics {
    pub api_count: usize,
    pub type_count: usize,
    pub edge_cnt: usize,
}

fn get_bound_var_attr(var: ty::BoundVariableKind) -> (String, bool) {
    let name: String;
    let is_lifetime;
    match var {
        ty::BoundVariableKind::Ty(bound_ty_kind) => {
            is_lifetime = false;
            name = match bound_ty_kind {
                ty::BoundTyKind::Param(_, sym) => sym.to_string(),
                _ => "anon".to_string(),
            }
        }
        ty::BoundVariableKind::Region(bound_region_kind) => {
            is_lifetime = true;
            name = match bound_region_kind {
                ty::BoundRegionKind::Named(_, name) => name.to_string(),
                _ => "anon".to_string(),
            }
        }
        ty::BoundVariableKind::Const => {
            is_lifetime = false;
            name = "anon const".to_string();
        }
    }
    (name, is_lifetime)
}

impl<'tcx> ApiDepGraph<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> ApiDepGraph<'tcx> {
        ApiDepGraph {
            graph: Graph::new(),
            node_indices: HashMap::new(),
            ty_nodes: Vec::new(),
            api_nodes: Vec::new(),
            tcx,
            all_apis: HashSet::new(),
        }
    }

    pub fn num_api(&self) -> usize {
        self.api_nodes.len()
    }

    pub fn num_ty(&self) -> usize {
        self.ty_nodes.len()
    }

    pub fn api_at(&self, idx: usize) -> (DefId, ty::GenericArgsRef<'tcx>) {
        let index = self.api_nodes[idx];
        self.graph[index].as_api()
    }

    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    pub fn build(&mut self, config: Config) {
        let tcx = self.tcx();
        let mut fn_visitor = FnVisitor::new(self, config, tcx);

        // 1. collect APIs
        tcx.hir_visit_all_item_likes_in_crate(&mut fn_visitor);
        self.all_apis = fn_visitor.apis().into_iter().collect();
        // add auxillary API from std
        // self.add_auxiliary_api();

        // 2. resolve generic API to monomorphic API
        if config.resolve_generic {
            self.resolve_generic_api();
        } else {
            self.update_transform_edges();
        }
    }

    pub fn inner_graph(&self) -> &InnerGraph<'tcx> {
        &self.graph
    }

    pub fn statistics(&self) -> Statistics {
        let mut api_cnt = 0;
        let mut ty_cnt = 0;
        let mut edge_cnt = 0;

        for node in self.graph.node_indices() {
            match self.graph[node] {
                DepNode::Api(..) => api_cnt += 1,
                DepNode::Ty(_) => ty_cnt += 1,
            }
        }

        for edge in self.graph.edge_indices() {
            edge_cnt += 1;
        }

        Statistics {
            api_count: api_cnt,
            type_count: ty_cnt,
            edge_cnt,
        }
    }

    pub fn is_node_exist(&self, node: &DepNode<'tcx>) -> bool {
        self.node_indices.contains_key(&node)
    }

    pub fn get_or_create_index(&mut self, node: DepNode<'tcx>) -> NodeIndex {
        if let Some(node_index) = self.node_indices.get(&node) {
            *node_index
        } else {
            let node_index = self.graph.add_node(node.clone());
            self.node_indices.insert(node.clone(), node_index);
            match node {
                DepNode::Api(..) => {
                    self.api_nodes.push(node_index);
                }
                DepNode::Ty(_) => {
                    self.ty_nodes.push(node_index);
                }
                _ => {}
            }
            node_index
        }
    }

    pub fn get_index(&self, node: DepNode<'tcx>) -> Option<NodeIndex> {
        self.node_indices.get(&node).map(|index| *index)
    }

    pub fn add_edge(&mut self, src: NodeIndex, dst: NodeIndex, edge: DepEdge) {
        self.graph.add_edge(src, dst, edge);
    }

    pub fn add_edge_once(&mut self, src: NodeIndex, dst: NodeIndex, edge: DepEdge) {
        if !self.graph.contains_edge(src, dst) {
            self.graph.add_edge(src, dst, edge);
        }
    }

    pub fn eligible_api_nodes_with(&self, tys: &[Ty<'tcx>]) -> Vec<&DepNode<'tcx>> {
        let check_ty = |ty: Ty<'tcx>| {
            if utils::is_fuzzable_ty(ty, self.tcx) {
                return true;
            }
            if tys.iter().any(|avail_ty| {
                if utils::is_ty_eq(*avail_ty, ty, self.tcx) {
                    return true;
                }
                false
            }) {
                return true;
            }
            return false;
        };
        self.graph
            .node_indices()
            .filter_map(|index| {
                if let DepNode::Api(fn_did, args) = self.graph[index] {
                    if self
                        .graph
                        .neighbors_directed(index, Direction::Incoming)
                        .all(|neighbor| check_ty(self.graph[neighbor].as_ty().ty()))
                    {
                        return Some(&self.graph[index]);
                    }
                }
                None
            })
            .collect()
    }

    pub fn eligible_transform_with(
        &self,
        tys: &[Ty<'tcx>],
    ) -> Vec<(TyWrapper<'tcx>, TransformKind)> {
        let mut set = HashSet::new();
        for ty in tys {
            if let Some(node) = self.get_index(DepNode::Ty((*ty).into())) {
                for edge in self.graph.edges(node) {
                    if let Some(kind) = edge.weight().as_transform_kind() {
                        let target_ty = self.graph[edge.target()].as_ty();
                        set.insert((target_ty, kind));
                    }
                }
            }
        }
        set.into_iter().collect()
    }

    pub fn add_generic_api(&mut self, fn_did: DefId) -> bool {
        let args = ty::GenericArgs::identity_for_item(self.tcx, fn_did);

        if !self.add_api(fn_did, args) {
            return false;
        }

        let api_node = self.get_or_create_index(DepNode::api(fn_did, args));
        let binder_fn_sig = self.tcx.fn_sig(fn_did).instantiate_identity();

        // add generic param def to graph
        // NOTE: generics_of query only return early bound generics
        let generics = self.tcx.generics_of(fn_did);
        let early_generic_count = generics.count();
        // rap_debug!("early bound generic count = {}", early_generic_count);
        // for i in 0..early_generic_count {
        //     let generic_param_def = generics.param_at(i, self.tcx);
        //     // rap_debug!("early bound generic#{i}: {:?}", generic_param_def);
        //     let node_index = self.get_or_create_index(DepNode::generic_param_def(
        //         fn_did,
        //         i,
        //         generic_param_def.name,
        //         !generic_param_def.kind.is_ty_or_const(),
        //     ));
        //     self.add_edge_once(api_node, node_index, DepEdge::fn2generic());
        // }

        // add late bound generic
        // for (i, var) in binder_fn_sig.bound_vars().iter().enumerate() {
        //     // rap_debug!("bound var#{i}: {var:?}");
        //     let (name, is_lifetime) = get_bound_var_attr(var);
        //     let node_index = self.get_or_create_index(DepNode::generic_param_def(
        //         fn_did,
        //         early_generic_count + i,
        //         name,
        //         is_lifetime,
        //     ));
        //     self.add_edge_once(api_node, node_index, DepEdge::fn2generic());
        // }
        true
    }

    /// return true if the api is added successfully, false if it already exists.
    pub fn add_api(&mut self, fn_did: DefId, args: &[ty::GenericArg<'tcx>]) -> bool {
        let node = DepNode::api(fn_did, self.tcx.mk_args(args));
        if self.is_node_exist(&node) {
            return false;
        }
        let api_node = self.get_or_create_index(node);

        rap_trace!("[ApiDepGraph] add fn: {:?} args: {:?}", fn_did, args);

        let fn_sig = utils::fn_sig_with_generic_args(fn_did, args, self.tcx);

        // add inputs/output to graph, and compute constraints based on subtyping
        for (no, input_ty) in fn_sig.inputs().iter().enumerate() {
            let input_node = self.get_or_create_index(DepNode::ty(*input_ty));
            self.add_edge(input_node, api_node, DepEdge::arg(no));
        }

        let output_ty = fn_sig.output();
        let output_node = self.get_or_create_index(DepNode::ty(output_ty));
        self.add_edge(api_node, output_node, DepEdge::ret());

        true
    }

    /// return all transform kind for `ty` that we intersted in.
    pub fn all_transforms(&self, ty: Ty<'tcx>) -> Vec<TransformKind> {
        let mut tfs = Vec::new();
        if let Some(index) = self.get_index(DepNode::Ty(ty.into())) {
            for edge in self.graph.edges_directed(index, Direction::Outgoing) {
                if let DepEdge::Transform(kind) = edge.weight() {
                    tfs.push(*kind);
                }
            }
        }
        tfs
    }

    pub fn is_start_node_index(&self, index: NodeIndex) -> bool {
        match self.graph[index] {
            DepNode::Api(..) => self
                .graph
                .neighbors_directed(index, Direction::Incoming)
                .next()
                .is_none(),
            DepNode::Ty(ty) => utils::is_fuzzable_ty(ty.into(), self.tcx),
        }
    }

    /// estimate maximum fuzzing coverage
    /// return (num_covered, num_total)
    pub fn estimate_coverage(&self, tcx: TyCtxt<'tcx>) -> (usize, usize) {
        let mut estimated_cover = HashSet::new();

        let mut reachable = vec![false; self.graph.node_count()];

        // initialize worklist with start node (indegree is zero)
        let mut worklist = VecDeque::from_iter(self.graph.node_indices().filter(|index| {
            if self.is_start_node_index(*index) {
                reachable[index.index()] = true;
                true
            } else {
                false
            }
        }));

        rap_debug!("[estimate_coverage] worklist = {:?}", worklist);

        // initialize queue with fuzzable type
        while let Some(index) = worklist.pop_front() {
            if let DepNode::Api(did, args) = self.graph[index] {
                estimated_cover.insert((did, args));
            }

            for next in self.graph.neighbors(index) {
                if reachable[next.index()] {
                    continue;
                }
                if match self.graph[next] {
                    DepNode::Ty(_) => true,
                    DepNode::Api(..) => {
                        if self
                            .graph
                            .neighbors_directed(next, petgraph::Direction::Incoming)
                            .all(|nbor| reachable[nbor.index()])
                        {
                            true
                        } else {
                            false
                        }
                    }
                } {
                    rap_debug!("[estimate_coverage] add {:?} to worklist", next);
                    reachable[next.index()] = true;
                    worklist.push_back(next);
                }
            }
        }
        (estimated_cover.len(), self.num_api())
    }

    pub fn dump_to_dot<P: AsRef<Path>>(&self, path: P, tcx: TyCtxt<'tcx>) {
        let get_edge_attr =
            |graph: &Graph<DepNode<'tcx>, DepEdge>,
             edge_ref: petgraph::graph::EdgeReference<DepEdge>| {
                let color = match edge_ref.weight() {
                    DepEdge::Arg(_) | DepEdge::Ret => "black",
                    DepEdge::Fn2Generic => "grey",
                    DepEdge::Transform(_) => "darkorange",
                };
                format!("label=\"{}\", color = {}", edge_ref.weight(), color)
            };
        let get_node_attr = |graph: &Graph<DepNode<'tcx>, DepEdge>,
                             node_ref: (NodeIndex, &DepNode<'tcx>)| {
            format!("label={:?}, ", desc_str(node_ref.1.clone(), tcx))
                + match node_ref.1 {
                    DepNode::Api(..) => "color = blue",
                    DepNode::Ty(_) => "color = red",
                }
                + ", shape=box"
        };

        let dot = dot::Dot::with_attr_getters(
            &self.graph,
            &[dot::Config::NodeNoLabel, dot::Config::EdgeNoLabel],
            &get_edge_attr,
            &get_node_attr,
        );
        let mut file = rap_create_file(path, "can not create dot file");
        write!(&mut file, "{:?}", dot).expect("fail when writing data to dot file");
        // println!("{:?}", dot);
    }
}
