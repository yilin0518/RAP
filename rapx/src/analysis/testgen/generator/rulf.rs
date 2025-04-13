use petgraph::visit::EdgeRef;
use petgraph::Direction;
use rand::rng;
use crate::analysis::core::api_dep;
use std::collections::{HashMap, HashSet, VecDeque};
use crate::analysis::testgen::utils::is_fuzzable_ty;
use crate::analysis::testgen::utils;
use petgraph::visit::IntoNodeReferences;
use crate::analysis::testgen::context::{ApiCall, Context};
use crate::analysis::testgen::api_dep::DepEdge;
use rustc_middle::ty::{self, Ty, TyCtxt, TyKind, AdtDef, FieldDef};
use rustc_hir::def_id::DefId;
use crate::analysis::testgen::ContextBase;
use crate::rap_info;
use crate::rap_debug;
use rand::Rng; 
use rand::seq::SliceRandom; 
use rand::prelude::IndexedRandom;

use crate::analysis::testgen::context::Var;
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
pub fn rulf_algorithm<'tcx, R: Rng>(
    tcx: TyCtxt<'tcx>,
    graph: &mut api_dep::ApiDepGraph<'tcx>,
    max_depth: usize,
    cx: &mut ContextBase<'tcx>,
    rng: &mut R,
){
    let mut queue = VecDeque::new();
    let visited: &mut HashSet<api_dep::DepNode<'tcx>> = &mut HashSet::new();
    let mut type_to_api_calls: HashMap<Ty<'tcx>, Vec<Vec<DefId>>> = HashMap::new();
    // 1. find start nodes
    let api_starts = find_api_starts(graph, tcx);
    // for start_api in api_starts.iter() {
    //     rap_info!("start_api: {:?}", start_api);
    // }
    // 2. start node push to queue
    for start_api in api_starts {
        if let api_dep::DepNode::Api(def_id) = start_api {
            let fn_sig = utils::fn_sig_without_binders(def_id, tcx);
            let mut args = Vec::new();
            for input_ty in fn_sig.inputs() {
                let providers = cx.all_possible_providers(*input_ty);
                let var = if providers.is_empty() {
                    panic!("no providers for start node , need input type {:?}", input_ty);
                } else {
                    let idx = rng.random_range(0..providers.len());
                    providers[idx]
                };
                args.push(var);
            }
            let call = ApiCall { fn_did: def_id, args };
            cx.add_call_stmt(call);
            visited.insert(start_api.clone());
            queue.push_back((start_api, vec![def_id], 1));
            type_to_api_calls.entry(fn_sig.output()).or_insert_with(Vec::new).push(vec![def_id]);
        }
    }
    // 3. BFS 
    while let Some((last_api, current_seq, depth)) = queue.pop_front() {
        if depth > max_depth {
            break; // depth bigger than max_depth, stop BFS
        }
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
                // find consumers that are not visited
                let mut unvisited_consumers = Vec::new();
                for consumer_edge in consumer_edges {
                    let consumer_api_idx = consumer_edge.target();
                    let consumer_api = graph.inner_graph()[consumer_api_idx].clone();
                    if let api_dep::DepNode::Api(_) = consumer_api {
                        if !visited.contains(&consumer_api) {
                            unvisited_consumers.push(consumer_api);
                        }
                    }
                }
                // 处理未访问的消费 API
                for consumer_api in unvisited_consumers {
                    if let api_dep::DepNode::Api(def_id) = consumer_api {
                        let fn_sig = utils::fn_sig_without_binders(def_id, tcx);
                        let mut param_providers: Vec<Vec<_>> = Vec::new();
                        let mut satisfy_all_input = true;
                        for input_ty in fn_sig.inputs() {
                            let providers = cx.all_possible_providers(*input_ty);
                            if providers.is_empty() {
                                rap_debug!("no providers for consumer node now, need input type {:?}", input_ty);
                                satisfy_all_input = false;
                                break;
                            } else {
                                param_providers.push(providers);
                            }
                        }
                        if !satisfy_all_input{
                            continue;
                        }
                        let mut new_calls = Vec::new();
                        // params have diversity, generate at most 3 call seq
                        let mut generated = HashSet::new();
                        for _ in 0..3 {
                            let mut args = Vec::new();
                            let enough_param = param_providers.iter().all(|p| p.len() > 0);
                            if !enough_param {
                                break;
                            }
                            for providers in &mut param_providers {
                                let var = providers.swap_remove(rng.random_range(0..providers.len()));
                                args.push(var);
                            }

                            let call = ApiCall { fn_did: def_id, args: args.clone() };
                            if generated.insert(args) {
                                new_calls.push(call);
                            }
                        }

                        // 添加生成的调用
                        for call in new_calls {
                            cx.add_call_stmt(call);
                            let mut new_seq = current_seq.clone();
                            new_seq.push(def_id);

                            // 记录生成的调用序列
                            type_to_api_calls
                                .entry(fn_sig.output())
                                .or_insert_with(Vec::new)
                                .push(new_seq.clone());

                            visited.insert(consumer_api.clone());
                            queue.push_back((consumer_api.clone(), new_seq, depth + 1));
                        }
                    }
                }
                
            } else {
                rap_info!("ret_type_node is not DepNode::Ty");
            }
        }
    }
    // BFS 后循环处理未访问节点
    let all_api_nodes: HashSet<_> = graph.inner_graph().node_references()
    .filter_map(|(_, node)| if let api_dep::DepNode::Api(_) = node { Some(node.clone()) } else { None })
    .collect();
    let mut unvisited_api_nodes: HashSet<_> = all_api_nodes.difference(&visited).cloned().collect();
    let mut prev_unvisited_count = unvisited_api_nodes.len() + 1;

    while !unvisited_api_nodes.is_empty() && prev_unvisited_count > unvisited_api_nodes.len() {
        prev_unvisited_count = unvisited_api_nodes.len();
        let current_unvisited: Vec<_> = unvisited_api_nodes.iter().cloned().collect();
        for target_api in current_unvisited {
            if  backward_search(graph, &target_api, cx, &mut type_to_api_calls, rng, tcx) {
                visited.insert(target_api.clone());
                unvisited_api_nodes.remove(&target_api);
            }
    }
}
}


fn backward_search<'tcx, R: Rng>(
    graph: &mut api_dep::ApiDepGraph<'tcx>,
    target_api: &api_dep::DepNode<'tcx>,
    cx: &mut ContextBase<'tcx>,
    type_to_api_calls: &mut HashMap<Ty<'tcx>, Vec<Vec<DefId>>>,
    rng: &mut R,
    tcx: TyCtxt<'tcx>,
) -> bool {
    if let api_dep::DepNode::Api(def_id) = target_api {
        let fn_sig = utils::fn_sig_without_binders(*def_id, tcx);
        let mut vars = Vec::new(); // 存储参数使用的变量
        let mut dependency_seqs = Vec::new(); // 存储每个参数的依赖序列

        // 处理每个输入参数
        for input_ty in fn_sig.inputs() {
            let providers = cx.all_possible_providers(*input_ty);
            if !providers.is_empty() {
                // 当前环境有可用变量
                let idx = rng.random_range(0..providers.len());
                let var = providers[idx];
                vars.push(var);
                if let Some(api_seqs) = type_to_api_calls.get(input_ty) {
                    // 从 type_to_api_calls 中生成
                    if let Some(api_seq) = api_seqs.choose(rng) {
                        dependency_seqs.push(api_seq.clone()); // 记录依赖序列
                    } else {
                        rap_debug!("no api seq for input type {:?}", input_ty);
                        return false;
                    }
                } else {
                    rap_debug!("no api seq for input type {:?}", input_ty);
                    return false; // 无法满足参数
                }
            } else if let Some(api_seqs) = type_to_api_calls.get(input_ty) {
                // 从 type_to_api_calls 中生成
                if let Some(api_seq) = api_seqs.choose(rng) {
                    if let Some(var) = seq2call(api_seq, cx, rng, tcx) {
                        vars.push(var);
                        dependency_seqs.push(api_seq.clone()); // 记录依赖序列
                    } else {
                        return false;
                    }
                } else {
                    return false;
                }
            } else {
                return false; // 无法满足参数
            }
        }

        // 所有参数都满足，构建 target_seq
        let mut target_seq = Vec::new();
        for dep_seq in dependency_seqs {
            target_seq.extend(dep_seq); // 添加依赖序列
        }
        target_seq.push(*def_id); // 添加目标 API

        // 生成目标 API 的调用
        let call = ApiCall { fn_did: *def_id, args: vars };
        cx.add_call_stmt(call);

        // 更新 type_to_api_calls
        type_to_api_calls
            .entry(fn_sig.output())
            .or_insert_with(Vec::new)
            .push(target_seq.clone());
        true
    } else {
        false
    }
}

fn seq2call<'tcx, R: Rng>(seq: &Vec<DefId>, cx: &mut ContextBase<'tcx>, rng: &mut R, tcx: TyCtxt<'tcx>) ->Option<Var>{
    let mut ret_var:Option<Var> = None;
    // 遍历 seq 中的每个 DefId，依次生成调用
    for &def_id in seq {
        let fn_sig = utils::fn_sig_without_binders(def_id, tcx);
        let mut args = Vec::new();

        // 为每个输入类型生成参数
        for input_ty in fn_sig.inputs() {
            let providers = cx.all_possible_providers(*input_ty);
            let var = if providers.is_empty() {
                panic!("no providers for node {:?} , need input type {:?}", def_id,input_ty);
            } else {
                // 随机选择一个 provider
                let idx = rng.random_range(0..providers.len());
                providers[idx] 
            };
            args.push(var);
        }

        // 创建 ApiCall 并添加到 cx
        let call = ApiCall { fn_did: def_id, args };
        ret_var = Some(cx.add_call_stmt(call));
    }
    ret_var
}