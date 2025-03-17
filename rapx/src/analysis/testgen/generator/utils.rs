use rustc_hir::{def_id::DefId, BodyOwnerKind};
use rustc_middle::ty::{self, Ty, TyCtxt, TyKind};

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
