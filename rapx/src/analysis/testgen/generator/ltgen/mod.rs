pub mod context;
mod lifetime_constraint;

use crate::analysis::testgen::context::{ApiCall, Context, ContextBase, Stmt};
use crate::analysis::testgen::utils;
use crate::rap_debug;
use rand::rngs::ThreadRng;
use rand::{self, Rng};
use rustc_hir::def_id::DefId;
use rustc_infer::infer::TyCtxtInferExt;
use rustc_middle::ty::{self, Ty, TyCtxt, TyKind};
use rustc_span::Span;
use std::cell::RefCell;

pub struct LtGenBuilder<'tcx, R: Rng> {
    tcx: TyCtxt<'tcx>,
    rng: R,
    max_complexity: usize,
    population_size: usize,
}

impl<'tcx> LtGenBuilder<'tcx, ThreadRng> {
    pub fn new(tcx: TyCtxt<'tcx>) -> LtGenBuilder<'tcx, ThreadRng> {
        LtGenBuilder {
            tcx,
            rng: rand::rng(),
            max_complexity: 20,
            population_size: 100,
        }
    }
}

impl<'tcx, R: Rng> LtGenBuilder<'tcx, R> {
    pub fn build(self) -> LtGen<'tcx, R> {
        LtGen::new(self.tcx, self.rng, self.max_complexity)
    }

    pub fn max_complexity(mut self, max_complexity: usize) -> Self {
        self.max_complexity = max_complexity;
        self
    }

    pub fn population_size(mut self, population_size: usize) -> Self {
        self.population_size = population_size;
        self
    }

    pub fn rng(mut self, rng: R) -> Self {
        self.rng = rng;
        self
    }
}

pub struct LtGen<'tcx, R: Rng> {
    pub_api: Vec<DefId>,
    tcx: TyCtxt<'tcx>,
    rng: RefCell<R>,
    max_complexity: usize,
    // population_size: usize,
    // vec_cx: Vec<Context<'tcx>>,
}

impl<'tcx, R: Rng> LtGen<'tcx, R> {
    fn new(tcx: TyCtxt<'tcx>, rng: R, max_complexity: usize) -> LtGen<'tcx, R> {
        LtGen {
            pub_api: utils::get_all_pub_apis(tcx),
            tcx,
            rng: RefCell::new(rng),
            max_complexity,
        }
    }

    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    pub fn pub_api_def_id(&self) -> &[DefId] {
        &self.pub_api
    }

    pub fn is_api_eligable<C: Context<'tcx>>(&self, fn_did: DefId, cx: &C) -> Option<ApiCall> {
        let tcx = self.tcx();

        let mut api_call = ApiCall {
            fn_did,
            args: Vec::new(),
        };
        rap_debug!("consider: {:?}", fn_did);

        // TODO: now only consider fn_sig without type & const parameters
        if tcx.generics_of(fn_did).requires_monomorphization(tcx) {
            return None;
        }
        let fn_sig = utils::jump_all_binders(fn_did, tcx);

        for input_ty in fn_sig.inputs().iter() {
            rap_debug!("check: {input_ty:?}");
            let providers = cx.all_possible_providers(*input_ty);
            if providers.is_empty() {
                rap_debug!("no possible providers");
                return None;
            }
            let idx = self.rng.borrow_mut().random_range(0..providers.len());
            api_call.args.push(providers[idx].clone());
        }

        Some(api_call)
    }

    fn choose_eligable_api(&self, cx: &impl Context<'tcx>) -> Option<ApiCall> {
        let mut eligable_calls = Vec::new();
        for fn_did in self.pub_api_def_id() {
            if let Some(call) = self.is_api_eligable(*fn_did, cx) {
                eligable_calls.push(call);
            }
        }
        if eligable_calls.is_empty() {
            return None;
        }
        rap_debug!("eligable calls: {eligable_calls:?}");
        let idx = self.rng.borrow_mut().random_range(0..eligable_calls.len());
        Some(eligable_calls.swap_remove(idx))
    }

    pub fn gen_in_place<C: Context<'tcx>>(&mut self, cx: &mut C) {
        while let Some(call) = self.choose_eligable_api(cx) {
            cx.add_call_stmt(call);
            if cx.complexity() >= self.max_complexity {
                break;
            }
        }
    }

    pub fn gen<C: Context<'tcx> + Clone>(&mut self, cx: &C) -> C {
        let mut new_cx = cx.clone();
        self.gen_in_place(&mut new_cx);
        new_cx
    }
}
