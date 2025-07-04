pub mod default;
pub mod visitor;

use std::collections::HashMap;
use rustc_hir::{
    def_id::DefId
};
use crate::Analysis;

pub struct CallGraph {
    pub functions: HashMap<DefId, String>, // function id, function name 
    pub fn_calls: HashMap<DefId, Vec<DefId>>, // caller_id -> Vec<(callee_id)>
}

pub trait CallGraphAnalysis: Analysis {
    fn get_callgraph(&mut self) -> CallGraph;
}

