pub mod context;
mod folder;
mod lifetime;
mod mono;
mod pattern;
mod select;

use crate::analysis::core::alias::FnRetAlias;
use crate::analysis::core::api_dep::DepNode;
use crate::analysis::core::api_dep::{graph::TransformKind, ApiDepGraph};
use crate::analysis::testgen::context::Var;
use crate::analysis::testgen::utils::{self};
use crate::{rap_debug, rap_info};
use context::LtContext;
use itertools::Itertools;
use rand::distr::weighted::WeightedIndex;
use rand::rngs::ThreadRng;
use rand::{self, Rng};
use rustc_data_structures::fx::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use std::cell::RefCell;
use std::collections::HashSet;

type FnAliasMap = FxHashMap<DefId, FnRetAlias>;

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub enum Action<'tcx> {
    Api(DepNode<'tcx>),
    Transform(Var, TransformKind),
}

pub struct LtGenBuilder<'tcx, 'a, R: Rng> {
    tcx: TyCtxt<'tcx>,
    rng: R,
    max_complexity: usize,
    max_iteration: usize,
    alias_map: &'a FnAliasMap,
    api_graph: ApiDepGraph<'tcx>,
}

impl<'tcx, 'a> LtGenBuilder<'tcx, 'a, ThreadRng> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        alias_map: &'a FnAliasMap,
        api_graph: ApiDepGraph<'tcx>,
    ) -> LtGenBuilder<'tcx, 'a, ThreadRng> {
        LtGenBuilder {
            tcx,
            rng: rand::rng(),
            max_complexity: 20,
            max_iteration: 1000,
            alias_map,
            api_graph: api_graph,
        }
    }
}

impl<'tcx, 'a, R: Rng> LtGenBuilder<'tcx, 'a, R> {
    pub fn build(self) -> LtGen<'tcx, 'a, R> {
        LtGen::new(
            self.tcx,
            self.alias_map,
            self.rng,
            self.max_complexity,
            self.max_iteration,
            self.api_graph,
        )
    }

    pub fn max_iteration(mut self, max_iteration: usize) -> Self {
        self.max_iteration = max_iteration;
        self
    }

    pub fn max_complexity(mut self, max_complexity: usize) -> Self {
        self.max_complexity = max_complexity;
        self
    }

    pub fn rng(mut self, rng: R) -> Self {
        self.rng = rng;
        self
    }
}

pub struct LtGen<'tcx, 'a, R: Rng> {
    tcx: TyCtxt<'tcx>,
    rng: RefCell<R>,
    max_complexity: usize,
    max_iteration: usize,
    pub_api: Vec<DefId>,
    alias_map: &'a FnAliasMap,
    api_graph: ApiDepGraph<'tcx>,
    covered_api: HashSet<DefId>,
}

impl<'tcx, 'a, R: Rng> LtGen<'tcx, 'a, R> {
    fn new(
        tcx: TyCtxt<'tcx>,
        alias_map: &'a FnAliasMap,
        rng: R,
        max_complexity: usize,
        max_iteration: usize,
        api_graph: ApiDepGraph<'tcx>,
    ) -> Self {
        LtGen {
            pub_api: utils::get_all_pub_apis(tcx),
            tcx,
            rng: RefCell::new(rng),
            max_complexity,
            max_iteration,
            alias_map,
            api_graph,
            covered_api: HashSet::new(),
        }
    }

    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn weight_of_actions(&self, actions: &[Action<'tcx>]) -> Vec<f32> {
        vec![1.0; actions.len()]
    }

    fn eligable_actions(&self, cx: &LtContext<'tcx, 'a>) -> Vec<Action<'tcx>> {
        let mut actions = Vec::new();

        let tys: Vec<_> = cx
            .cx()
            .available_vars()
            .map(|var| cx.cx().type_of(var))
            .collect();

        for node in self.api_graph.eligible_api_nodes_with(&tys) {
            actions.push(Action::Api(node));
        }

        for var in cx.cx().available_vars() {
            let res = self
                .api_graph
                .eligible_transform_with(&[cx.cx().type_of(var)])
                .into_iter()
                .map(|(_, kind)| Action::Transform(var, kind));
            actions.extend(res);
        }

        actions
    }

    fn next(&mut self, cx: &mut LtContext<'tcx, 'a>) -> Option<Action<'tcx>> {
        rap_debug!(
            "live vars: {}",
            cx.cx()
                .available_vars()
                .map(|var| format!("{var}: {:?}", cx.cx().type_of(var)))
                .join(", ")
        );

        rap_debug!(
            "varstate: {}",
            cx.cx()
                .vars()
                .map(|var| { format!("{} -> {}", var, cx.cx().var_state(var)) })
                .join(", ")
        );

        let tys: Vec<_> = cx
            .cx()
            .available_vars()
            .map(|var| cx.cx().type_of(var))
            .collect();

        rap_debug!(
            "live tys: {}",
            tys.iter().map(|ty| format!("{ty}")).join(", ")
        );

        let actions = self.eligable_actions(&cx);
        rap_debug!("# eligible actions = {}", actions.len());
        rap_debug!("eligible actions: {:?}", actions);

        // No action can do
        if actions.is_empty() {
            return None;
        }

        let weights = self.weight_of_actions(&actions);
        let dist = WeightedIndex::new(&weights).unwrap();
        let index = self.rng.borrow_mut().sample(dist);
        Some(actions[index])
    }

    // pub fn print_brief()

    pub fn gen(&mut self) -> LtContext<'tcx, 'a> {
        let mut lt_ctxt = LtContext::new(self.tcx, &self.alias_map);
        let (estimated, total) = self.api_graph.estimate_coverage();
        let mut count = 0;
        loop {
            count += 1;
            if count > self.max_iteration {
                rap_info!("max iteration reached, generation terminate");
                break;
            }
            rap_info!("<<<<< Iter {} >>>>>", count);
            if lt_ctxt.cx().complexity() > self.max_complexity {
                rap_info!("complexity limit reached, generation terminate");
                break;
            }

            if let Some(action) = self.next(&mut lt_ctxt) {
                match action {
                    Action::Api(node) => {
                        let (fn_did, args) = node.as_api();
                        rap_debug!(
                            "[next] select API call: {}",
                            self.tcx.def_path_str_with_args(fn_did, args)
                        );
                        if let Some(call) = self.get_eligable_call(fn_did, args, &mut lt_ctxt) {
                            self.covered_api.insert(call.fn_did());
                            lt_ctxt.add_call_stmt(call);
                            if self.rng.borrow_mut().random_ratio(1, 2) && lt_ctxt.try_inject_drop()
                            {
                                rap_debug!("successfully inject drop");
                            }
                        }
                    }
                    Action::Transform(var, kind) => {
                        rap_debug!(
                            "[next] select transform: {}: {} {}",
                            var,
                            lt_ctxt.cx().type_of(var),
                            kind
                        );
                        match kind {
                            TransformKind::Ref(mutability) => {
                                lt_ctxt.add_ref_stmt(var, mutability, None);
                            }
                            _ => {
                                panic!("not implemented yet");
                            }
                        }
                    }
                }
            } else {
                rap_info!("no eligable action, generation terminate");
                break;
            }

            rap_info!(
                "complexity={}, num_drop={}, covered/estimated/total_api={}/{}/{}",
                lt_ctxt.cx().complexity(),
                lt_ctxt.dropped_count(),
                lt_ctxt.num_covered_api(),
                estimated,
                total,
            );

            rap_info!(
                "coverage={:.3}/{:.3}/{:.3} (current/global/estimated_max)",
                lt_ctxt.num_covered_api() as f32 / total as f32,
                self.covered_api.len() as f32 / total as f32,
                estimated as f32 / total as f32
            );
        }
        lt_ctxt.try_use_all_available_vars();
        lt_ctxt
    }

    pub fn count_generic_api(&self) -> usize {
        self.pub_api
            .iter()
            .filter(|did| utils::fn_requires_monomorphization(**did, self.tcx))
            .count()
    }

    pub fn statistic_str(&self) -> String {
        let mut s = String::new();
        s.push_str(&format!("# APIs = {}\n", self.pub_api.len()));
        s.push_str(&format!("# generic APIs = {}\n", self.count_generic_api()));
        s.push_str(&format!("# covered APIs = {}\n", self.covered_api.len()));
        s.push_str("covered APIs:\n");
        s.push_str(
            &self
                .covered_api
                .iter()
                .map(|did| format!("{:?}", did))
                .join(", "),
        );
        s.push_str("\nuncovered APIs:\n");
        s.push_str(
            &self
                .pub_api
                .iter()
                .filter(|did| !self.covered_api.contains(did))
                .map(|did| format!("{:?}", did))
                .join(", "),
        );

        s
    }
}
