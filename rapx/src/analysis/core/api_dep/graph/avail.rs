use super::dep_edge::DepEdge;
use super::dep_node::{desc_str, DepNode};
use super::transform::TransformKind;
use super::ty_wrapper::TyWrapper;
use super::ApiDepGraph;
use super::Config;
use crate::analysis::core::api_dep::utils;
use crate::analysis::core::api_dep::visitor::FnVisitor;
use crate::analysis::utils::def_path::path_str_def_id;
use crate::rap_debug;
use crate::rap_trace;
use crate::utils::fs::rap_create_file;
use petgraph::visit::EdgeRef;
use petgraph::Direction;
use rustc_middle::ty::{self, Ty, TyCtxt};
use std::collections::HashSet;

impl<'tcx> ApiDepGraph<'tcx> {
    pub fn eligible_api_nodes_with(&self, tys: &[Ty<'tcx>]) -> Vec<DepNode<'tcx>> {
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
                        return Some(self.graph[index]);
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
}
