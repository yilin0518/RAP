use std::collections::HashMap;
use std::io::Write;

use super::folder::*;
use crate::rap_debug;
use petgraph::graph::{EdgeIndex, NodeIndex};
use rustc_hir::def_id::DefId;
use rustc_infer::infer::region_constraints::Constraint;
use rustc_infer::infer::{self, InferCtxt, TyCtxtInferExt};
use rustc_infer::traits::ObligationCause;
use rustc_middle::ty::{self, Ty, TyCtxt, TypeFoldable};
use rustc_span::{Span, DUMMY_SP};

#[derive(Debug)]
pub enum PatternNode {
    Named(usize),
    Temp(usize),
}

#[derive(Debug)]
struct EdgePattern(PatternNode, PatternNode);

#[derive(Debug, Default)]
pub struct EdgePatterns {
    named_region_num: usize,
    temp_num: usize,
    patterns: Vec<EdgePattern>,
}

impl EdgePatterns {
    pub fn named_region_num(&self) -> usize {
        self.named_region_num
    }

    pub fn temp_num(&self) -> usize {
        self.temp_num
    }

    pub fn patterns(&self) -> &[EdgePattern] {
        &self.patterns
    }
}

#[derive(Debug)]
pub enum RegionNode {
    Static,
    Named(usize), // use in subregion graph, it is a pattern
    Temp(usize),
}

pub struct RegionGraph {
    inner: petgraph::Graph<RegionNode, ()>,
    temp_indices: Vec<NodeIndex>,
    named_indices: Vec<NodeIndex>,
    static_index: NodeIndex,
}

impl RegionGraph {
    pub fn new() -> RegionGraph {
        let mut graph = petgraph::Graph::new();
        let static_index = graph.add_node(RegionNode::Static);
        RegionGraph {
            inner: graph,
            temp_indices: Vec::new(),
            named_indices: Vec::new(),
            static_index,
        }
    }

    fn static_index(&self) -> NodeIndex {
        self.static_index
    }

    pub fn add_edges_with<'tcx>(&mut self, patterns: &EdgePatterns, subst: &[ty::Region<'tcx>]) {
        assert!(subst.len() == patterns.named_region_num());

        let mut temp = Vec::new();

        // initiate named and temp node we will use
        for _ in 0..patterns.temp_num() {
            temp.push(self.add_new_temp_node());
        }

        for pattern in patterns.patterns() {
            let get_index = |node: &PatternNode| match node {
                PatternNode::Named(i) => self.get_node_by_region(subst[*i]),
                PatternNode::Temp(i) => temp[*i],
            };
            let from = get_index(&pattern.0);
            let to = get_index(&pattern.1);
            self.add_edge(from, to);
        }
    }

    pub fn add_new_temp_node(&mut self) -> NodeIndex {
        let node = self
            .inner
            .add_node(RegionNode::Temp(self.temp_indices.len()));
        self.temp_indices.push(node);
        node
    }

    pub fn next_named_node(&mut self) -> usize {
        let named_id = self.named_indices.len();
        let index = self.inner.add_node(RegionNode::Named(named_id));
        self.named_indices.push(index);
        named_id
    }
    pub fn register_var_ty<'tcx>(&mut self, ty: Ty<'tcx>, tcx: TyCtxt<'tcx>) -> Ty<'tcx> {
        let before_num = self.named_indices.len();
        let mut folder = FreeVarFolder::new(tcx, before_num);
        let ty = ty.fold_with(&mut folder);
        for i in before_num..folder.current_offset() {
            self.named_indices
                .push(self.inner.add_node(RegionNode::Named(i)));
        }
        ty
    }
    fn get_node_by_id(&self, id: usize) -> NodeIndex {
        self.named_indices[id]
    }

    pub fn get_node_by_region(&self, region: ty::Region<'_>) -> NodeIndex {
        match region.kind() {
            ty::ReVar(vid) => self.named_indices[vid.index()],
            ty::ReStatic => self.static_index(),
            _ => {
                panic!("unexpected region kind: {:?}", region);
            }
        }
    }

    pub fn add_edge(&mut self, from: NodeIndex, to: NodeIndex) -> EdgeIndex {
        self.inner.add_edge(from, to, ())
    }

    pub fn add_edge_by_id(&mut self, from: usize, to: usize) {
        let from = self.get_node_by_id(from);
        let to = self.get_node_by_id(to);
        self.add_edge(from, to);
    }

    pub fn add_edge_by_region<'tcx>(&mut self, from: ty::Region<'tcx>, to: ty::Region<'tcx>) {
        let from = self.get_node_by_region(from);
        let to = self.get_node_by_region(to);
        self.add_edge(from, to);
    }

    pub fn dump(&self, os: &mut impl Write) -> std::result::Result<(), Box<dyn std::error::Error>> {
        let dot = petgraph::dot::Dot::new(&self.inner);
        write!(os, "{:?}", dot)?;
        Ok(())
    }
}

fn region_vid_str(vid: ty::RegionVid) -> String {
    format!("{:?}", vid)
}

fn region_str(region: ty::Region<'_>) -> String {
    region.get_name_or_anon().to_string()
}

pub fn constraint_str<'tcx>(constraint: Constraint<'tcx>) -> String {
    let (a, b) = match constraint {
        Constraint::VarSubVar(a, b) => (region_vid_str(a), region_vid_str(b)),
        Constraint::RegSubVar(a, b) => (region_str(a), region_vid_str(b)),
        Constraint::VarSubReg(a, b) => (region_vid_str(a), region_str(b)),
        Constraint::RegSubReg(a, b) => (region_str(a), region_str(b)),
    };
    format!("{} <= {}", a, b)
}

pub fn extract_constraints<'tcx>(fn_did: DefId, tcx: TyCtxt<'tcx>) -> EdgePatterns {
    let early_fn_sig = tcx.fn_sig(fn_did);
    let binder_fn_sig = early_fn_sig.instantiate_identity();
    let param_env = tcx.param_env(fn_did);

    // obtain subtyping contraints
    let infcx = tcx.infer_ctxt().build();
    let mut folder = InfcxVarFolder::new(&infcx, tcx);
    let fn_sig = tcx.liberate_late_bound_regions(fn_did, binder_fn_sig);
    let binder_with_free_vars = fn_sig.fold_with(&mut folder);

    let res = infcx
        .at(&ObligationCause::dummy(), param_env)
        .sub(infer::DefineOpaqueTypes::Yes, fn_sig, binder_with_free_vars)
        .unwrap();
    res.obligations.into_iter().for_each(|obligation| {
        rap_debug!("obligation: {obligation:?}");
    });
    // TODO: add structure contraint to infcx

    // rap_debug!("binder: {binder_with_vars:?}");
    rap_debug!("free binder: {binder_with_free_vars:?}");
    let region_constraint_data = infcx.take_and_reset_region_constraints();
    let mut map = HashMap::new();
    let mut temp_region_no = |region: ty::Region<'tcx>| -> usize {
        if region.is_var() {
            panic!("region is var");
        }
        let len = map.len();
        *map.entry(*region).or_insert(len)
    };
    let mut subgraph = EdgePatterns::default();

    for (constraint, _) in region_constraint_data.constraints {
        let edge = match constraint {
            Constraint::VarSubVar(a, b) => EdgePattern(
                PatternNode::Named(a.as_usize()),
                PatternNode::Named(b.as_usize()),
            ),
            Constraint::RegSubVar(a, b) => EdgePattern(
                PatternNode::Temp(temp_region_no(a)),
                PatternNode::Named(b.as_usize()),
            ),
            Constraint::VarSubReg(a, b) => EdgePattern(
                PatternNode::Named(a.as_usize()),
                PatternNode::Temp(temp_region_no(b)),
            ),
            Constraint::RegSubReg(a, b) => EdgePattern(
                PatternNode::Temp(temp_region_no(a)),
                PatternNode::Temp(temp_region_no(b)),
            ),
        };
        subgraph.patterns.push(edge);
    }
    subgraph.named_region_num = folder.cnt();
    subgraph.temp_num = map.len();
    subgraph
}
