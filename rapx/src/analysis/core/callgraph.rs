pub mod default;
pub mod visitor;

use crate::Analysis;
use rustc_hir::def_id::DefId;
use std::collections::HashMap;

pub struct CallGraph {
    pub functions: HashMap<DefId, String>, // function id, function name
    pub fn_calls: HashMap<DefId, Vec<DefId>>, // caller_id -> Vec<(callee_id)>
}

pub trait CallGraphAnalysis: Analysis {
    fn get_callgraph(&mut self) -> CallGraph;
}
