pub mod debug;
pub mod default;
pub mod graph;

use std::{
    collections::{HashMap, HashSet},
    fmt::{self, Display},
    fs::File,
    io::Write,
    process::Command,
};

use crate::analysis::Analysis;
use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_index::IndexVec;
use rustc_middle::{
    mir::{Body, Local},
    ty::TyCtxt,
};
use rustc_span::Span;

#[derive(Clone)]
pub struct DataFlowGraph {
    pub nodes: GraphNodes,
    pub edges: GraphEdges,
}
pub type DataFlowGraphMap = HashMap<DefId, DataFlowGraph>;
pub struct DataFlowGraphWrapper(pub DataFlowGraph);
pub struct DataFlowGraphMapWrapper(pub HashMap<DefId, DataFlowGraph>);

pub type EdgeIdx = usize;
pub type GraphNodes = IndexVec<Local, GraphNode>;
pub type GraphEdges = IndexVec<EdgeIdx, GraphEdge>;

#[derive(Clone, Debug)]
pub struct GraphEdge {
    pub src: Local,
    pub dst: Local,
    pub op: EdgeOp,
    pub seq: usize,
}

#[derive(Clone, Debug)]
pub struct GraphNode {
    pub ops: Vec<NodeOp>,
    pub span: Span, //the corresponding code span
    pub seq: usize, //the sequence number, edges with the same seq number are added in the same batch within a statement or terminator
    pub out_edges: Vec<EdgeIdx>,
    pub in_edges: Vec<EdgeIdx>,
}

/// This trait provides features related to dataflow analysis.
pub trait DataFlowAnalysis: Analysis {
    fn get_fn_dataflow(&self, def_id: DefId) -> Option<DataFlowGraph>;
    fn get_all_dataflow(&self) -> DataFlowGraphMap;
    /// If there is a dataflow between `local1` and `local2` within the function specified by
    /// `def_id`, the function returns ture; otherwise, it returns false.
    fn has_flow_between(&self, def_id: DefId, local1: Local, local2: Local) -> bool;

    /// The function returns a set of Locals that are equivelent to the given `local`.
    fn collect_equivalent_locals(&self, def_id: DefId, local: Local) -> HashSet<Local>;
}

impl Display for DataFlowGraphWrapper {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "Nodes:")?;
        for node in &self.0.nodes {
            writeln!(f, "  {:?}", node)?;
        }
        writeln!(f, "Edges:")?;
        for edge in &self.0.edges {
            writeln!(f, "  {:?}", edge)?;
        }
        Ok(())
    }
}

impl Display for DataFlowGraphMapWrapper {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "===Print dataflow analysis resuts===")?;
        for (def_id, dfg) in &self.0 {
            writeln!(
                f,
                "DefId: {:?}\n{}",
                def_id,
                DataFlowGraphWrapper(dfg.clone())
            )?;
        }
        Ok(())
    }
}

#[derive(Clone, Debug)]
pub enum NodeOp {
    //warning: the fields are related to the version of the backend rustc version
    Nop,
    Err,
    Const(String, String),
    //Rvalue
    Use,
    Repeat,
    Ref,
    ThreadLocalRef,
    AddressOf,
    Len,
    Cast,
    BinaryOp,
    CheckedBinaryOp,
    NullaryOp,
    UnaryOp,
    Discriminant,
    Aggregate(AggKind),
    ShallowInitBox,
    CopyForDeref,
    RawPtr,
    //TerminatorKind
    Call(DefId),
    CallOperand, // the first in_edge is the func
}

#[derive(Clone, Debug)]
pub enum EdgeOp {
    Nop,
    //Operand
    Move,
    Copy,
    Const,
    //Mutability
    Immut,
    Mut,
    //Place
    Deref,
    Field(String),
    Downcast(String),
    Index,
    ConstIndex,
    SubSlice,
    SubType,
}

#[derive(Clone, Copy, Debug)]
pub enum AggKind {
    Array,
    Tuple,
    Adt(DefId),
    Closure(DefId),
    Coroutine(DefId),
    RawPtr,
}
