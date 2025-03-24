use rustc_hir::{def_id::DefId, BodyOwnerKind};
use rustc_infer::{
    infer::TyCtxtInferExt,
    traits::{Obligation, ObligationCause},
};
use rustc_middle::ty::{self, FnSig, ParamEnv, Ty, TyCtxt, TyKind};
use rustc_trait_selection::traits::query::evaluate_obligation::InferCtxtExt;

pub fn is_api_public(fn_def_id: impl Into<DefId>, tcx: TyCtxt<'_>) -> bool {
    matches!(tcx.visibility(fn_def_id.into()), ty::Visibility::Public)
}

/// return all DefId of all pub APIs
pub fn get_all_pub_apis(tcx: TyCtxt<'_>) -> Vec<DefId> {
    let mut apis = Vec::new();

    for local_def_id in tcx.hir().body_owners() {
        if matches!(tcx.hir().body_owner_kind(local_def_id), BodyOwnerKind::Fn)
            && is_api_public(local_def_id, tcx)
        {
            apis.push(local_def_id.to_def_id());
        }
    }
    apis
}

pub fn is_ty_impl_copy<'tcx>(ty: Ty<'tcx>, tcx: TyCtxt<'tcx>) -> bool {
    let infcx = tcx.infer_ctxt().build();
    let param_env = ParamEnv::reveal_all();
    let copy_trait = tcx.require_lang_item(rustc_hir::LangItem::Copy, None);

    let copy_pred = ty::TraitRef::new(tcx, copy_trait, vec![ty]);
    let obligation = Obligation::new(tcx, ObligationCause::dummy(), param_env, copy_pred);

    infcx.predicate_must_hold_modulo_regions(&obligation)
}

pub fn is_fuzzable_ty(ty: Ty<'_>) -> bool {
    // TODO: determine whether ADT is fuzzable
    match ty.kind() {
        TyKind::Bool
        | TyKind::Char
        | TyKind::Str
        | TyKind::Int(_)
        | TyKind::Uint(_)
        | TyKind::Float(_)
        | TyKind::Infer(
            ty::InferTy::IntVar(_)
            | ty::InferTy::FloatVar(_)
            | ty::InferTy::FreshIntTy(_)
            | ty::InferTy::FreshFloatTy(_),
        ) => true,
        TyKind::Ref(_, x, _) | TyKind::Array(x, _) | TyKind::Slice(x) => {
            is_fuzzable_ty(x.peel_refs())
        }
        TyKind::Tuple(tys) => {
            for ty in tys.iter() {
                if !is_fuzzable_ty(ty.peel_refs()) {
                    return false;
                }
            }
            true
        }
        _ => false,
    }
}

pub fn jump_all_binders<'tcx>(fn_did: DefId, tcx: TyCtxt<'tcx>) -> FnSig<'tcx> {
    let early_fn_sig = tcx.fn_sig(fn_did);
    let binder_fn_sig = early_fn_sig.instantiate_identity();
    tcx.liberate_late_bound_regions(fn_did, binder_fn_sig)  
}
