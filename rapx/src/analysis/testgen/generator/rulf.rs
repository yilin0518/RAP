use petgraph::visit::EdgeRef;
use petgraph::Direction;
use crate::analysis::core::api_dep;
use std::collections::{HashMap, HashSet, VecDeque};
use crate::analysis::testgen::generator::utils::is_fuzzable_ty;
use crate::analysis::testgen::generator::utils;
use petgraph::visit::IntoNodeReferences;
use crate::analysis::testgen::generator::context::Context;
use crate::analysis::testgen::stmt::ApiCall;
use crate::analysis::testgen::api_dep::DepEdge;
use rustc_middle::ty::{self, Ty, TyCtxt, TyKind, AdtDef, FieldDef};
use rustc_hir::def_id::DefId;
use crate::analysis::testgen::ContextBase;
use crate::rap_info;
use crate::rap_debug;
fn find_api_starts<'tcx>(graph: &api_dep::ApiDepGraph<'tcx>, tcx: TyCtxt<'tcx>) -> Vec<api_dep::DepNode<'tcx>> {
    let mut api_starts = Vec::new();
    for (node_idx, node) in graph.inner_graph().node_references() {
        if let api_dep::DepNode::Api(_) = node {
            let all_params_primitive = graph.inner_graph().edges_directed(node_idx, Direction::Incoming)
                .filter(|e| matches!(e.weight(), api_dep::DepEdge::Arg(_)))
                .all(|e| {
                    if let api_dep::DepNode::Ty(ty_wrapper) = &graph.inner_graph()[e.source()] {
                        is_fuzzable_ty(ty_wrapper.ty(), tcx)
                    } else {
                        false
                    }
                });
            if all_params_primitive {
                api_starts.push(node.clone());
            }
        }
    }
    api_starts
}
pub fn rulf_algorithm<'tcx>(
    tcx: TyCtxt<'tcx>,
    graph: &mut api_dep::ApiDepGraph<'tcx>,
    max_depth: usize,
    cx: &mut ContextBase<'tcx>,
){
    let mut queue = VecDeque::new();
    let visited: &mut HashSet<api_dep::DepNode<'tcx>> = &mut HashSet::new();
    // 1. find start nodes
    let api_starts = find_api_starts(graph, tcx);
    // for start_api in api_starts.iter() {
    //     rap_info!("start_api: {:?}", start_api);
    // }
    // 2. 起点入队并添加初始语句
    for start_api in api_starts {
        if let api_dep::DepNode::Api(def_id) = start_api {
            let fn_sig = utils::jump_all_binders(def_id, tcx);
            let mut args = Vec::new();
            for input_ty in fn_sig.inputs() {
                let providers = cx.all_possible_providers(*input_ty);
                let var = if providers.is_empty() {
                    panic!("no providers for start node , need input type {:?}", input_ty);
                } else {
                    providers[0]
                };
                args.push(var);
            }
            let call = ApiCall { fn_did: def_id, args };
            cx.add_call_stmt(call);
            visited.insert(start_api.clone());
            queue.push_back((start_api, 0));
        }
    }
    // 3. BFS 
    while let Some((last_api, depth)) = queue.pop_front() {
        // if depth >= max_depth {
        //     continue; // 超过最大深度，跳过
        // }
        let last_idx = graph.get_node(last_api);
        // 4. 处理生产边
        let ret_edges = graph.inner_graph().edges_directed(last_idx, Direction::Outgoing)
            .filter(|e| matches!(e.weight(), DepEdge::Ret));
        for ret_edge in ret_edges {
            let ret_type_node = &graph.inner_graph()[ret_edge.target()];
            if let api_dep::DepNode::Ty(ret_ty) = ret_type_node {
                // 5. 查找消费边
                let consumer_edges = graph.inner_graph().edges_directed(ret_edge.target(), Direction::Outgoing)
                    .filter(|e| matches!(e.weight(), DepEdge::Arg(_)));
                for consumer_edge in consumer_edges {
                    let consumer_api_idx = consumer_edge.target();
                    let consumer_api = graph.inner_graph()[consumer_api_idx].clone();
                    if let api_dep::DepNode::Api(def_id) = consumer_api {
                        if visited.contains(&consumer_api) {
                            continue;
                        }
                        // 6. 生成调用语句
                        let fn_sig = utils::jump_all_binders(def_id, tcx);
                        let mut args = Vec::new();
                        let mut satisfy_all_input = true;
                        for input_ty in fn_sig.inputs() {
                            let providers = cx.all_possible_providers(*input_ty);
                            let var = if providers.is_empty() {
                                rap_debug!("no providers for consumer node , need input type {:?}", input_ty);
                                satisfy_all_input = false;
                                break;
                            } else {
                                providers[0]
                            };
                            args.push(var);
                        }
                        if !satisfy_all_input {
                            continue;
                        }
                        let call = ApiCall { fn_did: def_id, args };
                        cx.add_call_stmt(call);
                        visited.insert(consumer_api.clone());
                        queue.push_back((consumer_api, depth + 1));
                    }
                }
            } else {
                rap_info!("ret_type_node is not DepNode::Ty");
            }
        }
    }
}