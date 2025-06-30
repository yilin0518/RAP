pub mod dep_edge;
pub mod dep_node;
pub mod transform;
mod ty_wrapper;

use super::Config;
use crate::analysis::core::api_dep::visitor::FnVisitor;
use crate::rap_trace;
use crate::utils::fs::rap_create_file;
pub use dep_edge::DepEdge;
pub use dep_node::{desc_str, DepNode};
use petgraph::dot;
use petgraph::graph::NodeIndex;
use petgraph::Direction;
use petgraph::Graph;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::{self, Ty, TyCtxt};
use std::collections::HashMap;
use std::collections::HashSet;
use std::hash::Hash;
use std::io::Write;
use std::path::Path;
pub use transform::TransformKind;
pub use ty_wrapper::TyWrapper;

type InnerGraph<'tcx> = Graph<DepNode<'tcx>, DepEdge>;
pub struct ApiDepGraph<'tcx> {
    graph: InnerGraph<'tcx>,
    node_indices: HashMap<DepNode<'tcx>, NodeIndex>,
    tcx: TyCtxt<'tcx>,
    tys: HashSet<TyWrapper<'tcx>>,
}

pub struct Statistics {
    pub api_count: usize,
    pub type_count: usize,
    pub generic_param_count: usize,
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
            tcx,
            tys: HashSet::new(),
        }
    }

    pub fn num_api(&self) -> usize {
        self.graph
            .node_indices()
            .filter(|index| matches!(self.graph[*index], DepNode::Api(..)))
            .count()
    }

    pub fn num_ty(&self) -> usize {
        // self.tys.len()
        self.graph
            .node_indices()
            .filter(|index| matches!(self.graph[*index], DepNode::Ty(_)))
            .count()
    }

    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    pub fn build(&mut self, config: Config) {
        // 1. scan
        let tcx = self.tcx();
        let mut fn_visitor = FnVisitor::new(self, config, tcx);
        tcx.hir_visit_all_item_likes_in_crate(&mut fn_visitor);

        // 2. add transform node
        self.update_transform_edges();

        // 3. prune redundant nodes
        self.prune_redundant_nodes();
    }

    pub fn update_transform_edges(&mut self) {
        for node_index in self.graph.node_indices() {
            if let DepNode::Ty(ty) = self.graph[node_index] {
                self.add_possible_transform::<3>(ty, 0);
            }
        }
    }

    fn add_possible_transform<const MAX_DEPTH: usize>(
        &mut self,
        current_ty: TyWrapper<'tcx>,
        depth: usize,
    ) -> Option<NodeIndex> {
        if depth > 0 {
            let index = self.get_index_by_node(DepNode::Ty(current_ty));
            if index.is_some() {
                return index;
            }
        }

        if depth >= MAX_DEPTH {
            return None;
        }

        let mut ret = None;
        for kind in TransformKind::all() {
            let new_ty = current_ty.transform(*kind, self.tcx()); // &T or &mut T
            if let Some(next_index) = self.add_possible_transform::<MAX_DEPTH>(new_ty, depth + 1) {
                let current_index = self.get_node(DepNode::Ty(current_ty));
                self.add_edge_once(current_index, next_index, DepEdge::transform(*kind));
                ret = Some(current_index);
            }
        }
        ret
    }

    pub fn prune_redundant_nodes(&mut self) {}

    pub fn is_ty_exist(&self, ty: Ty<'tcx>) -> bool {
        self.node_indices.contains_key(&DepNode::Ty(ty.into()))
    }

    pub fn inner_graph(&self) -> &InnerGraph<'tcx> {
        &self.graph
    }

    pub fn statistics(&self) -> Statistics {
        let mut api_cnt = 0;
        let mut ty_cnt = 0;
        let mut generic_param_cnt = 0;
        let mut edge_cnt = 0;

        for node in self.graph.node_indices() {
            match self.graph[node] {
                DepNode::Api(..) => api_cnt += 1,
                DepNode::Ty(_) => ty_cnt += 1,
                DepNode::GenericParamDef(..) => generic_param_cnt += 1,
            }
        }

        for edge in self.graph.edge_indices() {
            edge_cnt += 1;
        }

        Statistics {
            api_count: api_cnt,
            type_count: ty_cnt,
            generic_param_count: generic_param_cnt,
            edge_cnt,
        }
    }

    pub fn is_node_exist(&self, node: &DepNode<'tcx>) -> bool {
        self.node_indices.contains_key(&node)
    }

    pub fn get_node(&mut self, node: DepNode<'tcx>) -> NodeIndex {
        if let Some(node_index) = self.node_indices.get(&node) {
            *node_index
        } else {
            let node_index = self.graph.add_node(node.clone());
            self.node_indices.insert(node, node_index);
            node_index
        }
    }

    pub fn get_index_by_node(&self, node: DepNode<'tcx>) -> Option<NodeIndex> {
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

    /// return all types that can be transformed into `ty`
    pub fn provider_tys(&self, ty: Ty<'tcx>) -> Vec<Ty<'tcx>> {
        let index = self
            .get_index_by_node(DepNode::Ty(ty.into()))
            .expect(&format!("{ty:?} should be existed in api graph"));
        let mut tys = Vec::new();

        for node_index in self.graph.neighbors_directed(index, Direction::Incoming) {
            if let DepNode::Ty(ty) = self.graph[node_index] {
                tys.push(ty.ty());
            }
        }
        tys
    }

    pub fn add_generic_api(&mut self, fn_did: DefId) -> bool {
        let args = ty::GenericArgs::identity_for_item(self.tcx, fn_did);

        if !self.add_api(fn_did, args) {
            return false;
        }

        let api_node = self.get_node(DepNode::api(fn_did, args));
        let binder_fn_sig = self.tcx.fn_sig(fn_did).instantiate_identity();

        // add generic param def to graph
        // NOTE: generics_of query only return early bound generics
        let generics = self.tcx.generics_of(fn_did);
        let early_generic_count = generics.count();
        // rap_debug!("early bound generic count = {}", early_generic_count);
        for i in 0..early_generic_count {
            let generic_param_def = generics.param_at(i, self.tcx);
            // rap_debug!("early bound generic#{i}: {:?}", generic_param_def);
            let node_index = self.get_node(DepNode::generic_param_def(
                fn_did,
                i,
                generic_param_def.name,
                !generic_param_def.kind.is_ty_or_const(),
            ));
            self.add_edge_once(api_node, node_index, DepEdge::fn2generic());
        }

        // add late bound generic
        for (i, var) in binder_fn_sig.bound_vars().iter().enumerate() {
            // rap_debug!("bound var#{i}: {var:?}");
            let (name, is_lifetime) = get_bound_var_attr(var);
            let node_index = self.get_node(DepNode::generic_param_def(
                fn_did,
                early_generic_count + i,
                name,
                is_lifetime,
            ));
            self.add_edge_once(api_node, node_index, DepEdge::fn2generic());
        }
        true
    }

    /// return true if the api is added successfully, false if it already exists.
    pub fn add_api(&mut self, fn_did: DefId, args: &[ty::GenericArg<'tcx>]) -> bool {
        let node = DepNode::api(fn_did, self.tcx.mk_args(args));
        if self.is_node_exist(&node) {
            return false;
        }
        let api_node = self.get_node(node);

        rap_trace!("[ApiDepGraph] add fn: {:?} args: {:?}", fn_did, args);

        let binder_fn_sig = self.tcx.fn_sig(fn_did).instantiate(self.tcx, args);
        let fn_sig = binder_fn_sig.skip_binder();

        // add inputs/output to graph, and compute constraints based on subtyping
        for (no, input_ty) in fn_sig.inputs().iter().enumerate() {
            let input_node = self.get_node(DepNode::ty(*input_ty));
            self.add_edge_once(input_node, api_node, DepEdge::arg(no));
        }

        let output_ty = fn_sig.output();
        let output_node = self.get_node(DepNode::ty(output_ty));
        self.add_edge_once(api_node, output_node, DepEdge::ret());

        true
    }

    /// return all transform kind for `ty` that we intersted in.
    pub fn all_transforms(&self, ty: Ty<'tcx>) -> Vec<TransformKind> {
        let mut tfs = Vec::new();
        if let Some(index) = self.get_index_by_node(DepNode::Ty(ty.into())) {
            for edge in self.graph.edges_directed(index, Direction::Outgoing) {
                if let DepEdge::Transform(kind) = edge.weight() {
                    tfs.push(*kind);
                }
            }
        }
        tfs
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
                    DepNode::GenericParamDef(..) => "color = green",
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
