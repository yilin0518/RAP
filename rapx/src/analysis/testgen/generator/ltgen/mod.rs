pub mod context;
mod folder;
mod lifetime;
mod mono;
mod pattern;
mod safety;

use crate::analysis::core::alias::{FnRetAlias, RetAlias};
use crate::analysis::core::api_dep::{graph::TransformKind, ApiDepGraph};
use crate::analysis::testgen::context::{ApiCall, Context, Var};
use crate::analysis::testgen::utils::{self};
use crate::{rap_debug, rap_info};
use context::LtContext;
use pattern::PatternProvider;
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
    population_size: usize,
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
            population_size: 100,
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

    pub fn population_size(mut self, population_size: usize) -> Self {
        self.population_size = population_size;
        self
    }

    pub fn rng(mut self, rng: R) -> Self {
        self.rng = rng;
        self
    }
}

pub struct LtGen<'tcx, 'a, R: Rng> {
    pub_api: Vec<DefId>,
    tcx: TyCtxt<'tcx>,
    rng: RefCell<R>,
    max_complexity: usize,
    max_iteration: usize,
    alias_map: &'a FnAliasMap,
    pattern_provider: PatternProvider<'tcx>,
    api_graph: RefCell<ApiDepGraph<'tcx>>,
}

fn ty_project_to<'tcx>(mut ty: Ty<'tcx>, proj: &[usize], tcx: TyCtxt<'tcx>) -> Ty<'tcx> {
    for field_no in proj {
        ty = match ty.peel_refs().kind() {
            TyKind::Adt(adt_def, args) => {
                let did = adt_def
                    .all_fields()
                    .nth(*field_no)
                    .expect("field not found")
                    .did;
                tcx.type_of(did).instantiate(tcx, args)
            }
            _ => {
                panic!("not a struct type");
            }
        }
    }
    ty
}

fn get_fn_arg_ty_at<'tcx>(no: usize, fn_sig: ty::FnSig<'tcx>) -> Ty<'tcx> {
    if no == 0 {
        fn_sig.output()
    } else {
        fn_sig.inputs()[no - 1]
    }
}

fn destruct_ret_alias<'tcx>(
    fn_sig: ty::FnSig<'tcx>,
    ret_alias: &RetAlias,
    tcx: TyCtxt<'tcx>,
) -> (Ty<'tcx>, Ty<'tcx>) {
    let lhs_no = ret_alias.left_index;
    let rhs_no = ret_alias.right_index;

    (
        ty_project_to(
            get_fn_arg_ty_at(lhs_no, fn_sig),
            &ret_alias.left_field_seq,
            tcx,
        ),
        ty_project_to(
            get_fn_arg_ty_at(rhs_no, fn_sig),
            &ret_alias.right_field_seq,
            tcx,
        ),
    )
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
            pattern_provider: PatternProvider::new(tcx),
            max_complexity,
            max_iteration,
            alias_map,
            api_graph: RefCell::new(api_graph),
        }
    }

    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    pub fn pub_api_def_id(&self) -> &[DefId] {
        &self.pub_api
    }

    pub fn enable_monomorphization(&self) -> bool {
        true
        // false
    }

    pub fn is_api_eligable(
        &self,
        fn_did: DefId,
        cx: &LtContext<'tcx, '_>,
    ) -> Option<ApiCall<'tcx>> {
        let tcx = self.tcx();

        let mut api_call = ApiCall {
            fn_did,
            args: Vec::new(),
            generic_args: GenericArgs::identity_for_item(tcx, fn_did),
        };

        if tcx.generics_of(fn_did).requires_monomorphization(tcx) {
            if !self.enable_monomorphization() {
                return None;
            }
            let available_ty = cx
                .available_values()
                .iter()
                .fold(HashSet::new(), |mut set, var| {
                    set.insert(tcx.erase_regions(cx.type_of(*var)));
                    set
                });
            rap_debug!("available types: {:?}", available_ty);
            let monos = mono::get_all_concrete_mono_solution(fn_did, available_ty, tcx);
            rap_debug!("monos: {:?}", monos);
            if monos.is_empty() {
                return None;
            }
            let idx = self.rng.borrow_mut().random_range(0..monos.count());
            let args = monos.args_at(idx);
            rap_debug!("choosed mono args: {args:?}");
            api_call.generic_args = tcx.mk_args(&args.value);
            // update api_graph
            if self.api_graph.borrow_mut().add_api(fn_did, &args.value) {
                self.api_graph.borrow_mut().update_transform_edges();
            }
        }
        let fn_sig =
            utils::fn_sig_with_generic_args(api_call.fn_did(), api_call.generic_args(), tcx);

        rap_debug!("check eligible api: {fn_did:?}");
        for input_ty in fn_sig.inputs().iter() {
            rap_debug!("input_ty = {input_ty}");
            let providers = cx.all_possible_providers(*input_ty);
            if providers.is_empty() {
                rap_debug!("no possible providers");
                return None;
            }
            rap_debug!("providers: {providers:?}");
            let idx = self.rng.borrow_mut().random_range(0..providers.len());
            api_call.args.push(providers[idx].clone());
        }

        Some(api_call)
    }

    fn choose_eligable_api(&mut self, cx: &LtContext<'tcx, 'a>) -> Option<ApiCall<'tcx>> {
        let mut eligable_calls = Vec::new();
        rap_debug!("available vars: {:?}", cx.available_values());
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

    fn choose_transform(&self, cx: &mut LtContext<'tcx, 'a>) -> Option<(Var, TransformKind)> {
        let mut vec: Vec<(Var, TransformKind)> = Vec::new();
        for var in cx.available_values() {
            let ty = cx.type_of(*var);
            for transform in self.api_graph.borrow().all_transforms(ty) {
                vec.push((*var, transform));
            }
        }
        rap_debug!("transform candidates: {vec:?}");
        if vec.is_empty() {
            return None;
        }
        let idx = self.rng.borrow_mut().random_range(0..vec.len());
        Some(vec.swap_remove(idx))
    }

    fn next(&mut self, cx: &mut LtContext<'tcx, 'a>) -> bool {
        let hit = self.rng.borrow_mut().random_ratio(2, 3);

        if hit {
            if let Some(call) = self.choose_eligable_api(cx) {
                // if self.is_api_vulnerable(call.fn_did()) {
                //     rap_info!("{:?} maybe vulnerable", call.fn_did());
                // }
                cx.add_call_stmt(call);
                if cx.try_inject_drop() {
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
        let mut cx = LtContext::new(self.tcx, &self.alias_map);
        let (estimated, total) = utils::estimate_max_coverage(self.api_graph.get_mut(), tcx);
        let mut count = 0;
        loop {
            count += 1;
            if count > self.max_iteration {
                rap_info!("max iteration reached, generation terminate");
                break;
            }
            rap_info!("<<<<< Iter {} >>>>>", count);
            if cx.complexity() > self.max_complexity {
                rap_info!("complexity limit reached, generation terminate");
                break;
            }
            self.next(&mut cx);

            // if !self.next_operation(&mut cx) {
            //     rap_info!("no more operation can be performed, generation terminate");
            //     break;
            // }
            rap_info!(
                "complexity={}, num_drop={}, covered/estimated/total_api={}/{}/{}",
                cx.complexity(),
                cx.dropped_count(),
                cx.num_covered_api(),
                estimated,
                total,
            );

            rap_info!(
                "coverage={:.3}/{:.3} (current/estimated_max)",
                cx.num_covered_api() as f32 / total as f32,
                estimated as f32 / total as f32
            );
        }

        // dump debug files

        let mut file = std::fs::File::create("region_graph.dot").unwrap();
        // cx.region_graph().dump(&mut std::io::stdout()).unwrap();
        cx.region_graph().dump(&mut file).unwrap();

        self.api_graph.borrow().dump_to_dot("api_graph.dot", tcx);
        cx
    }
}
