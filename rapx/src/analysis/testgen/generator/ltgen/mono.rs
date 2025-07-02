use crate::analysis::testgen::utils::{self, fn_sig_with_generic_args};
use crate::{rap_debug, rap_info, rap_trace};
use rustc_hir::def_id::DefId;
use rustc_hir::LangItem;
use rustc_infer::infer::{DefineOpaqueTypes, TyCtxtInferExt as _};
use rustc_infer::infer::{InferCtxt, TyCtxtInferExt};
use rustc_infer::traits::{Obligation, ObligationCause};
use rustc_middle::ty::{self, Ty, TyCtxt, TypeVisitableExt};
use rustc_span::DUMMY_SP;
use rustc_trait_selection::traits::query::evaluate_obligation::InferCtxtExt as _;
use std::collections::HashSet;

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct Mono<'tcx> {
    pub value: Vec<ty::GenericArg<'tcx>>,
}

impl<'tcx> FromIterator<ty::GenericArg<'tcx>> for Mono<'tcx> {
    fn from_iter<T>(iter: T) -> Self
    where
        T: IntoIterator<Item = ty::GenericArg<'tcx>>,
    {
        Mono {
            value: iter.into_iter().collect(),
        }
    }
}

impl<'tcx> Mono<'tcx> {
    pub fn new(identity: &[ty::GenericArg<'tcx>]) -> Self {
        Mono {
            value: Vec::from(identity),
        }
    }

    fn has_infer_types(&self) -> bool {
        self.value.iter().any(|arg| match arg.kind() {
            ty::GenericArgKind::Type(ty) => ty.has_infer_types(),
            _ => false,
        })
    }

    fn get_mut(&mut self, idx: usize) -> &mut ty::GenericArg<'tcx> {
        &mut self.value[idx]
    }

    fn merge(&self, other: &Mono<'tcx>, tcx: TyCtxt<'tcx>) -> Option<Mono<'tcx>> {
        rap_trace!("[Mono::merge] self: {:?} other: {:?}", self, other);
        assert!(self.value.len() == other.value.len());
        let mut res = Vec::new();
        for i in 0..self.value.len() {
            let arg = self.value[i];
            let other_arg = other.value[i];
            let new_arg = if let Some(ty) = arg.as_type() {
                let other_ty = other_arg.expect_ty();
                if ty.is_ty_var() && other_ty.is_ty_var() {
                    arg
                } else if ty.is_ty_var() {
                    other_arg
                } else if other_ty.is_ty_var() {
                    arg
                } else if utils::is_ty_eq(ty, other_ty, tcx) {
                    arg
                } else {
                    return None;
                }
            } else {
                arg
            };
            res.push(new_arg);
        }
        Some(Mono { value: res })
    }

    fn fill_unbound_var(&self, tcx: TyCtxt<'tcx>) -> Vec<Mono<'tcx>> {
        let candidates = get_candidates(tcx);
        let mut res = vec![self.clone()];

        for (i, arg) in self.value.iter().enumerate() {
            if let Some(ty) = arg.as_type() {
                if ty.is_ty_var() {
                    let mut last = Vec::new();
                    std::mem::swap(&mut res, &mut last);
                    last.into_iter().for_each(|mono| {
                        for candidate in &candidates {
                            let mut new_mono = mono.clone();
                            *new_mono.get_mut(i) = (*candidate).into();
                            res.push(new_mono);
                        }
                    });
                }
            }
        }
        res
    }
}

#[derive(Clone, Debug)]
pub struct MonoSet<'tcx> {
    pub monos: Vec<Mono<'tcx>>,
}

impl<'tcx> MonoSet<'tcx> {
    pub fn all(identity: &[ty::GenericArg<'tcx>]) -> MonoSet<'tcx> {
        MonoSet {
            monos: vec![Mono::new(identity)],
        }
    }

    pub fn count(&self) -> usize {
        self.monos.len()
    }

    pub fn args_at(&self, no: usize) -> &Mono<'tcx> {
        &self.monos[no]
    }

    pub fn is_empty(&self) -> bool {
        self.monos.is_empty()
    }

    pub fn new() -> MonoSet<'tcx> {
        MonoSet { monos: Vec::new() }
    }

    pub fn insert(&mut self, mono: Mono<'tcx>) {
        self.monos.push(mono);
    }

    pub fn merge(&mut self, other: &MonoSet<'tcx>, tcx: TyCtxt<'tcx>) -> MonoSet<'tcx> {
        rap_trace!("[MonoSet::merge] self: {:?} other: {:?}", self, other);
        let mut res = MonoSet::new();

        for args in self.monos.iter() {
            for other_args in other.monos.iter() {
                let merged = args.merge(other_args, tcx);
                if let Some(mono) = merged {
                    res.insert(mono);
                }
            }
        }
        rap_trace!("[MonoSet::merge] result: {:?}", res);
        res
    }

    fn filter_unbound_solution(mut self) -> Self {
        self.monos.retain(|mono| mono.has_infer_types());
        self
    }

    fn instantiate_unbound(&self, tcx: TyCtxt<'tcx>) -> Self {
        let mut res = MonoSet::new();
        for mono in &self.monos {
            let filled = mono.fill_unbound_var(tcx);
            res.monos.extend(filled);
        }
        res
    }

    fn erase_region_var(&mut self, tcx: TyCtxt<'tcx>) {
        for mono in &mut self.monos {
            mono.value
                .iter_mut()
                .for_each(|arg| *arg = tcx.erase_regions(*arg))
        }
    }

    fn filter_by_trait_bound(mut self, fn_did: DefId, tcx: TyCtxt<'tcx>) -> Self {
        let early_fn_sig = tcx.fn_sig(fn_did);
        self.monos
            .retain(|args| is_args_fit_trait_bound(fn_did, &args.value, tcx));
        self
    }
}

/// try to unfiy lhs = rhs,
/// e.g.,
/// try_unify(Vec<T>, Vec<i32>, ...) = Some(i32)
/// try_unify(Vec<T>, i32, ...) = None
fn unify_ty<'tcx>(
    lhs: Ty<'tcx>,
    rhs: Ty<'tcx>,
    identity: &[ty::GenericArg<'tcx>],
    infcx: &InferCtxt<'tcx>,
    cause: &ObligationCause<'tcx>,
    param_env: ty::ParamEnv<'tcx>,
) -> Option<Mono<'tcx>> {
    infcx.probe(|_| {
        match infcx
            .at(cause, param_env)
            .eq(DefineOpaqueTypes::Yes, lhs, rhs)
        {
            Ok(infer_ok) => {
                rap_debug!("[infer_ok] {} = {} : {:?}", lhs, rhs, infer_ok);
                let mono = identity
                    .iter()
                    .map(|arg| match arg.kind() {
                        ty::GenericArgKind::Lifetime(region) => {
                            infcx.resolve_vars_if_possible(region).into()
                        }
                        ty::GenericArgKind::Type(ty) => infcx.resolve_vars_if_possible(ty).into(),
                        ty::GenericArgKind::Const(ct) => infcx.resolve_vars_if_possible(ct).into(),
                    })
                    .collect();
                // infcx.resolve
                Some(mono)
            }
            Err(e) => {
                rap_trace!("[infer_err] {} = {} : {:?}", lhs, rhs, e);
                None
            }
        }
    })
}

fn is_args_fit_trait_bound<'tcx>(
    fn_did: DefId,
    args: &[ty::GenericArg<'tcx>],
    tcx: TyCtxt<'tcx>,
) -> bool {
    let args = tcx.mk_args(args);
    rap_info!(
        "fn: {:?} args: {:?} identity: {:?}",
        fn_did,
        args,
        ty::GenericArgs::identity_for_item(tcx, fn_did)
    );
    let infcx = tcx.infer_ctxt().build(ty::TypingMode::PostAnalysis);
    let pred = tcx.predicates_of(fn_did);
    let inst_pred = pred.instantiate(tcx, args);
    let param_env = tcx.param_env(fn_did);
    rap_trace!("[trait bound] {fn_did:?} {args:?} {param_env:?} {inst_pred:?}");

    for pred in inst_pred.predicates.iter() {
        let obligation = Obligation::new(
            tcx,
            ObligationCause::dummy(),
            param_env,
            pred.as_predicate(),
        );

        let res = infcx.evaluate_obligation(&obligation);
        rap_trace!("{obligation:?}");
        rap_trace!("{res:?}");
        match res {
            Ok(eva) => {
                if !eva.may_apply() {
                    return false;
                }
            }
            Err(_) => {
                rap_trace!("[trait bound] check fail");
                return false;
            }
        }
    }
    rap_trace!("[trait bound] check succ");
    true
}

fn get_mono_set<'tcx>(
    fn_did: DefId,
    available_ty: &HashSet<Ty<'tcx>>,
    tcx: TyCtxt<'tcx>,
) -> MonoSet<'tcx> {
    let infcx = tcx
        .infer_ctxt()
        .ignoring_regions()
        .build(ty::TypingMode::PostAnalysis);
    let param_env = tcx.param_env(fn_did);
    let dummy_cause = ObligationCause::dummy();
    let fresh_args = infcx.fresh_args_for_item(DUMMY_SP, fn_did);
    // This replace generic types to infer var, e.g. fn(Vec<T>, i32) => fn(Vec<?0>, i32)
    let fn_sig = fn_sig_with_generic_args(fn_did, fresh_args, tcx);
    let generics = tcx.generics_of(fn_did);

    // Print fresh_args for debugging
    for i in 0..fresh_args.len() {
        rap_trace!(
            "arg#{}: {:?} -> {:?}",
            i,
            generics.param_at(i, tcx).name,
            fresh_args[i]
        );
    }

    let mut s = MonoSet::all(&fresh_args);

    rap_trace!("[solve] initialize s: {:?}", s);

    for input_ty in fn_sig.inputs().iter() {
        if !input_ty.has_infer_types() {
            continue;
        }
        let reachable_set = available_ty
            .iter()
            .fold(MonoSet::new(), |mut reachable_set, ty| {
                if let Some(mono) =
                    unify_ty(*input_ty, *ty, &fresh_args, &infcx, &dummy_cause, param_env)
                {
                    reachable_set.insert(mono);
                }
                reachable_set
            });
        s = s.merge(&reachable_set, tcx)
    }

    rap_trace!("[solve] after input types: {:?}", s);

    let mut res = MonoSet::new();

    for mono in s.monos {
        solve_unbound_generic_type(
            fn_did,
            mono,
            &mut res,
            // &fresh_args,
            &infcx,
            &dummy_cause,
            param_env,
            tcx,
        );
    }

    // erase infer region var
    res.erase_region_var(tcx);

    res
}

fn solve_unbound_generic_type<'tcx>(
    did: DefId,
    mono: Mono<'tcx>,
    res: &mut MonoSet<'tcx>,
    // identity: &[ty::GenericArg<'tcx>],
    infcx: &InferCtxt<'tcx>,
    cause: &ObligationCause<'tcx>,
    param_env: ty::ParamEnv<'tcx>,
    tcx: TyCtxt<'tcx>,
) {
    let args = tcx.mk_args(&mono.value);
    let preds = tcx.predicates_of(did).instantiate(tcx, args);
    let mut mset = MonoSet::all(args);
    for pred in preds.predicates.iter() {
        if let Some(trait_pred) = pred.as_trait_clause() {
            rap_trace!("[solve_unbound] pred: {:?}", trait_pred);

            let trait_pred = trait_pred.skip_binder();

            let trait_def_id = trait_pred.trait_ref.def_id;
            // ignore Sized trait
            if tcx.is_lang_item(trait_def_id, LangItem::Sized) {
                continue;
            }

            let mut p = MonoSet::new();
            for impl_did in tcx.all_impls(trait_def_id) {
                let impl_trait_ref = tcx.impl_trait_ref(impl_did).unwrap().skip_binder();
                if let Some(mono) = unify_trait(
                    trait_pred.trait_ref,
                    impl_trait_ref,
                    args,
                    &infcx,
                    &cause,
                    param_env,
                    tcx,
                ) {
                    p.insert(mono);
                }
            }
            mset = mset.merge(&p, tcx);
            rap_trace!("[solve_unbound] mset: {:?}", mset);
        }
    }

    rap_trace!("[solve_unbound] (final) mset: {:?}", mset);
    for mono in mset.monos {
        res.insert(mono);
    }
}

/// only handle the case that rhs does not have any infer types
/// e.g., `<T as Into<U>> == <Foo as Into<Bar>> => Some(T=Foo, U=Bar))`
fn unify_trait<'tcx>(
    lhs: ty::TraitRef<'tcx>,
    rhs: ty::TraitRef<'tcx>,
    identity: &[ty::GenericArg<'tcx>],
    infcx: &InferCtxt<'tcx>,
    cause: &ObligationCause<'tcx>,
    param_env: ty::ParamEnv<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> Option<Mono<'tcx>> {
    rap_trace!("[unify_trait] lhs: {:?}, rhs: {:?}", lhs, rhs);
    if lhs.def_id != rhs.def_id {
        return None;
    }
    assert!(lhs.args.len() == rhs.args.len());
    let mut s = Mono::new(identity);
    for (lhs_arg, rhs_arg) in lhs.args.iter().zip(rhs.args.iter()) {
        if let (Some(lhs_ty), Some(rhs_ty)) = (lhs_arg.as_type(), rhs_arg.as_type()) {
            if rhs_ty.has_infer_types() {
                // if rhs has infer types, we cannot unify it with lhs

                return None;
            }
            let mono = unify_ty(lhs_ty, rhs_ty, identity, infcx, cause, param_env)?;
            rap_trace!("[unify_trait] unified mono: {:?}", mono);
            s = s.merge(&mono, tcx)?;
        }
    }
    Some(s)
}

pub fn get_all_concrete_mono_solution<'tcx>(
    fn_did: DefId,
    mut available_ty: HashSet<Ty<'tcx>>,
    tcx: TyCtxt<'tcx>,
) -> MonoSet<'tcx> {
    // 1. prepare available types
    add_prelude_tys(&mut available_ty, tcx);
    add_transform_tys(&mut available_ty, tcx);
    rap_debug!("[mono] input => {fn_did:?}: {available_ty:?}");

    // 2. get mono set from available types
    let ret = get_mono_set(fn_did, &available_ty, tcx).instantiate_unbound(tcx);

    // 3. check trait bound
    let ret = ret.filter_by_trait_bound(fn_did, tcx);
    rap_debug!("possible mono solution for {fn_did:?}: {ret:?}");
    ret
}

pub fn add_transform_tys<'tcx>(available_ty: &mut HashSet<Ty<'tcx>>, tcx: TyCtxt<'tcx>) {
    let mut new_tys = Vec::new();
    available_ty.iter().for_each(|ty| {
        new_tys.push(Ty::new_ref(
            tcx,
            tcx.lifetimes.re_erased,
            *ty,
            ty::Mutability::Not,
        ));
        new_tys.push(Ty::new_ref(
            tcx,
            tcx.lifetimes.re_erased,
            *ty,
            ty::Mutability::Mut,
        ));
    });
    new_tys.into_iter().for_each(|ty| {
        available_ty.insert(ty);
    });
}

pub fn add_prelude_tys<'tcx>(available_ty: &mut HashSet<Ty<'tcx>>, tcx: TyCtxt<'tcx>) {
    let prelude_tys = [
        tcx.types.bool,
        tcx.types.char,
        tcx.types.f32,
        tcx.types.f64,
        tcx.types.i8,
        tcx.types.i32,
        tcx.types.u8,
        tcx.types.u32,
        tcx.types.usize,
        tcx.types.isize,
    ];
    prelude_tys.iter().for_each(|ty| {
        available_ty.insert(*ty);
    });
}

pub fn eliminate_infer_var<'tcx>(
    fn_did: DefId,
    args: &[ty::GenericArg<'tcx>],
    tcx: TyCtxt<'tcx>,
) -> Vec<ty::GenericArg<'tcx>> {
    let mut res = Vec::new();
    let identity = ty::GenericArgs::identity_for_item(tcx, fn_did);
    for (i, arg) in args.iter().enumerate() {
        if let Some(ty) = arg.as_type() {
            if ty.is_ty_var() {
                res.push(identity[i]);
            } else {
                res.push(*arg);
            }
        } else {
            res.push(*arg);
        }
    }
    res
}

pub fn get_candidates<'tcx>(tcx: TyCtxt<'tcx>) -> Vec<Ty<'tcx>> {
    // for (trait_id, impls) in tcx.all_local_trait_impls(()).iter(){

    // }
    vec![
        tcx.types.bool,
        tcx.types.char,
        tcx.types.u8,
        tcx.types.i8,
        tcx.types.i32,
        tcx.types.u32,
        tcx.types.i64,
        tcx.types.u64,
        tcx.types.f32,
        tcx.types.f64,
    ]
}

// pub fn determine_unbound_args<'tcx>(
//     fn_did: DefId,
//     args: &[ty::GenericArg<'tcx>],
//     tcx: TyCtxt<'tcx>,
// ) {
//     let args = eliminate_infer_var(fn_did, args, tcx);
//     let fn_sig = utils::fn_sig_with_generic_args(fn_did, &args, tcx);

//     let preds = tcx.predicates_of(fn_did);
//     let preds = preds.instantiate(tcx, tcx.mk_args(&args));

//     // init infer env
//     let param_env = tcx.param_env(fn_did);
//     let infcx = tcx.infer_ctxt().build(ty::TypingMode::PostAnalysis);

//     let candidates = get_candidates(tcx);

//     for pred in preds.predicates.iter() {
//         pred.as_predicate();
//     }

//     // let impls = tcx.trait_impls_of()

//     // let fcx = FulfillmentCtxt::new(&infcx);
//     // let tcx.trait_impls_of(key)
//     // infcx.instantiate_binder_with_fresh_vars(span, lbrct, value)
// }
