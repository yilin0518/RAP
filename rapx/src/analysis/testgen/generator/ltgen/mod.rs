pub mod context;
mod folder;
mod lifetime;
mod mono;
mod pattern;
mod select;

use crate::analysis::core::alias::{FnRetAlias, RetAlias};
use crate::analysis::core::api_dep::{graph::TransformKind, ApiDepGraph};
use crate::analysis::testgen::context::{ApiCall, Context, Var};
use crate::analysis::testgen::utils::{self};
use crate::{rap_debug, rap_info};
use context::LtContext;
use itertools::Itertools;
use rand::rngs::ThreadRng;
use rand::{self, Rng};
use rustc_data_structures::fx::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::{self, GenericArgs, Ty, TyCtxt, TyKind};
use std::cell::RefCell;
use std::collections::HashSet;

type FnAliasMap = FxHashMap<DefId, FnRetAlias>;

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
    api_graph: RefCell<ApiDepGraph<'tcx>>,
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
            api_graph: RefCell::new(api_graph),
            covered_api: HashSet::new(),
        }
    }

    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    pub fn api_graph(&self) -> &RefCell<ApiDepGraph<'tcx>> {
        &self.api_graph
    }

    pub fn pub_api_def_id(&self) -> &[DefId] {
        &self.pub_api
    }

    pub fn is_enable_monomorphization(&self) -> bool {
        true
        // false
    }

    fn next(&mut self, cx: &mut LtContext<'tcx, 'a>) -> bool {
        let hit = self.rng.borrow_mut().random_ratio(2, 3);

        rap_debug!(
            "live vars: {}",
            cx.cx()
                .available_vars()
                .map(|var| format!("{var}"))
                .join(", ")
        );

        if hit {
            if let Some(call) = self.choose_eligable_api(cx) {
                self.covered_api.insert(call.fn_did());
                cx.add_call_stmt(call);
                if self.rng.borrow_mut().random_ratio(1, 2) && cx.try_inject_drop() {
                    rap_debug!("successfully inject drop");
                }
                return true;
            }
        }
        if let Some((var, kind)) = self.choose_transform(cx) {
            match kind {
                TransformKind::Ref(mutability) => {
                    cx.add_ref_stmt(var, mutability);
                }
                _ => {
                    panic!("not implemented yet");
                }
            }
            return true;
        }

        false
    }

    // pub fn print_brief()

    pub fn gen(&mut self) -> LtContext<'tcx, 'a> {
        let tcx = self.tcx();
        let mut lt_ctxt = LtContext::new(self.tcx, &self.alias_map);
        let (estimated, total) = utils::estimate_max_coverage(self.api_graph.get_mut(), tcx);
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

            self.next(&mut lt_ctxt);

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
        s.push_str(&format!("#APIs = {}\n", self.pub_api.len()));
        s.push_str(&format!("#generic APIs = {}\n", self.count_generic_api()));
        s.push_str(&format!("#covered APIs = {}\n", self.covered_api.len()));
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
