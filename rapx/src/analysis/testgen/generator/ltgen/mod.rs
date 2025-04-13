pub mod context;
mod folder;
mod lifetime;

use crate::analysis::core::alias::{FnRetAlias, RetAlias};
use crate::analysis::testgen::context::{ApiCall, Context};
use crate::analysis::testgen::utils::{self, get_all_pub_apis};
use crate::rap_debug;
use context::LtContext;
use lifetime::EdgePatterns;
use rand::rngs::ThreadRng;
use rand::{self, Rng};
use rustc_data_structures::fx::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_infer::infer::TyCtxtInferExt;
use rustc_middle::mir::tcx;
use rustc_middle::ty::{self, Ty, TyCtxt, TyKind};
use rustc_span::Span;
use std::cell::RefCell;
use std::collections::HashMap;

type FnAliasMap = FxHashMap<DefId, FnRetAlias>;
type RegionSubgraphMap = HashMap<DefId, EdgePatterns>;

pub fn initialize_subgraph_map<'tcx>(tcx: TyCtxt<'tcx>) -> RegionSubgraphMap {
    let mut map = HashMap::new();
    for fn_did in get_all_pub_apis(tcx) {
        if utils::fn_requires_monomorphization(fn_did, tcx) {
            continue;
        }
        map.insert(fn_did, lifetime::extract_constraints(fn_did, tcx));
    }
    map
}

pub struct LtGenBuilder<'tcx, 'a, R: Rng> {
    tcx: TyCtxt<'tcx>,
    rng: R,
    max_complexity: usize,
    alias_map: &'a FnAliasMap,
    population_size: usize,
}

impl<'tcx, 'a> LtGenBuilder<'tcx, 'a, ThreadRng> {
    pub fn new(tcx: TyCtxt<'tcx>, alias_map: &'a FnAliasMap) -> LtGenBuilder<'tcx, 'a, ThreadRng> {
        LtGenBuilder {
            tcx,
            rng: rand::rng(),
            max_complexity: 20,
            population_size: 100,
            alias_map,
        }
    }
}

impl<'tcx, 'a, R: Rng> LtGenBuilder<'tcx, 'a, R> {
    pub fn build(mut self) -> LtGen<'tcx, 'a, R> {
        LtGen::new(self.tcx, self.alias_map, self.rng, self.max_complexity)
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
    alias_map: &'a FnAliasMap,
    subgraph_map: HashMap<DefId, lifetime::EdgePatterns>,
}

fn get_ty_by_no<'tcx>(no: usize, proj: &[usize], fn_did: DefId, tcx: TyCtxt<'tcx>) -> Ty<'tcx> {
    rap_debug!("get no.{} from {:?}", no, fn_did);
    rap_debug!("proj: {:?}", proj);
    let fn_sig = utils::fn_sig_without_binders(fn_did, tcx);
    let mut ty = if no == 0 {
        fn_sig.output()
    } else {
        fn_sig.inputs()[no - 1]
    };

    if !proj.is_empty() {
        for field_no in proj {
            ty = match ty.peel_refs().kind() {
                TyKind::Adt(adt_def, _) => {
                    let did = adt_def
                        .all_fields()
                        .nth(*field_no)
                        .expect("field not found")
                        .did;
                    tcx.type_of(did).instantiate_identity()
                }
                _ => {
                    panic!("not a struct type");
                }
            }
        }
    }
    ty
}

fn destruct_ret_alias<'tcx>(
    fn_did: DefId,
    ret_alias: &RetAlias,
    tcx: TyCtxt<'tcx>,
) -> (Ty<'tcx>, Ty<'tcx>) {
    let lhs_no = ret_alias.left_index;
    let rhs_no = ret_alias.right_index;
    (
        get_ty_by_no(lhs_no, &ret_alias.left_field_seq, fn_did, tcx),
        get_ty_by_no(rhs_no, &ret_alias.right_field_seq, fn_did, tcx),
    )
}

impl<'tcx, 'a, R: Rng> LtGen<'tcx, 'a, R> {
    fn new(tcx: TyCtxt<'tcx>, alias_map: &'a FnAliasMap, rng: R, max_complexity: usize) -> Self {
        LtGen {
            pub_api: utils::get_all_pub_apis(tcx),
            tcx,
            rng: RefCell::new(rng),
            max_complexity,
            alias_map,
            subgraph_map: initialize_subgraph_map(tcx),
        }
    }

    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    pub fn pub_api_def_id(&self) -> &[DefId] {
        &self.pub_api
    }

    pub fn is_api_vulnerable(&self, did: DefId) -> bool {
        if let Some(fn_ret_alias) = self.alias_map.get(&did) {
            let mut is_vulnerable = false;
            for ret_alias in fn_ret_alias.aliases() {
                let (lhs_ty, rhs_ty) = destruct_ret_alias(did, ret_alias, self.tcx());

                let lhs_result = utils::ty_check_ptr(lhs_ty, self.tcx());
                let rhs_result = utils::ty_check_ptr(rhs_ty, self.tcx());
                let has_unsafe_ptr = lhs_result.has_unsafe_ptr || rhs_result.has_unsafe_ptr;
                let has_ptr = lhs_result.has_any_ptr || rhs_result.has_any_ptr;
                is_vulnerable = is_vulnerable || (has_unsafe_ptr && has_ptr);
                rap_debug!("{did:?} is_vulnerable={is_vulnerable} lhs: {lhs_ty}, rhs: {rhs_ty}");
            }
            is_vulnerable
        } else {
            false
        }
    }

    pub fn check_all_vulnerable_api(&self) -> Vec<DefId> {
        let mut vulnerable_apis = Vec::new();
        for fn_did in self.pub_api_def_id() {
            if self.is_api_vulnerable(*fn_did) {
                vulnerable_apis.push(*fn_did);
            }
        }
        vulnerable_apis
    }

    pub fn is_api_eligable<C: Context<'tcx>>(&self, fn_did: DefId, cx: &C) -> Option<ApiCall> {
        let tcx = self.tcx();

        let mut api_call = ApiCall {
            fn_did,
            args: Vec::new(),
        };

        // TODO: now only consider fn_sig without type & const parameters
        if tcx.generics_of(fn_did).requires_monomorphization(tcx) {
            return None;
        }
        let fn_sig = utils::fn_sig_without_binders(fn_did, tcx);

        for input_ty in fn_sig.inputs().iter() {
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

    pub fn gen_in_place(&mut self, cx: &mut LtContext<'tcx, '_>) {
        let mut cnt = 0;
        while let Some(call) = self.choose_eligable_api(cx) {
            cx.add_call_stmt(call);

            let mut file = std::fs::File::create("region_graph.dot").unwrap();
            // let mut graph_content = String::new();
            cx.region_graph().dump(&mut std::io::stdout()).unwrap();
            cx.region_graph().dump(&mut file).unwrap();
            // rap_debug!("region graph:\n{}", graph_content);

            cnt = cnt + 1;
            if cnt >= 1 {
                break;
            }
            if cx.complexity() >= self.max_complexity {
                break;
            }
        }
    }
}
