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
    let param_env = ParamEnv::reveal_all();
    // let infcx = tcx.infer_ctxt().build();
    // let copy_trait = tcx.require_lang_item(rustc_hir::LangItem::Copy, None);
    // let copy_pred = ty::TraitRef::new(tcx, copy_trait, vec![ty]);
    // let obligation = Obligation::new(tcx, ObligationCause::dummy(), param_env, copy_pred);
    // infcx.predicate_must_hold_modulo_regions(&obligation)

    ty.is_copy_modulo_regions(tcx, param_env)
}

pub fn is_ty_eq<'tcx>(ty1: Ty<'tcx>, ty2: Ty<'tcx>, tcx: TyCtxt<'tcx>) -> bool {
    let infcx = tcx.infer_ctxt().build();
    let env = ParamEnv::reveal_all();
    // TODO: How to deal with lifetime?
    let res = infcx.at(&ObligationCause::dummy(), env).eq(
        rustc_infer::infer::DefineOpaqueTypes::Yes,
        ty1,
        ty2,
    );
    res.is_ok()
}

pub fn is_fuzzable_ty<'tcx>(ty: Ty<'tcx>, tcx: TyCtxt<'tcx>) -> bool {
    match ty.kind() {
        // Basical data type
        TyKind::Bool
        | TyKind::Char
        | TyKind::Int(_)
        | TyKind::Uint(_)
        | TyKind::Float(_)
        | TyKind::Str => true,

        // Infer
        TyKind::Infer(
            ty::InferTy::IntVar(_)
            | ty::InferTy::FreshIntTy(_)
            | ty::InferTy::FloatVar(_)
            | ty::InferTy::FreshFloatTy(_),
        ) => true,

        // Reference, Array, Slice
        TyKind::Ref(_, inner_ty, _) | TyKind::Array(inner_ty, _) | TyKind::Slice(inner_ty) => {
            is_fuzzable_ty(inner_ty.peel_refs(), tcx)
        }

        // Tuple
        TyKind::Tuple(tys) => tys
            .iter()
            .all(|inner_ty| is_fuzzable_ty(inner_ty.peel_refs(), tcx)),

        // ADT
        TyKind::Adt(adt_def, substs) => {
            if adt_def.is_struct() {
                // 检查所有字段是否为 pub 且类型可 Fuzz
                adt_def.all_fields().all(|field| {
                    field.vis.is_public() && // 字段必须是 pub
                    is_fuzzable_ty(field.ty(tcx, substs).peel_refs(), tcx)
                })
            } else if adt_def.is_enum() {
                adt_def.variants().iter().all(|variant| {
                    variant
                        .fields
                        .iter()
                        .all(|field| is_fuzzable_ty(field.ty(tcx, substs).peel_refs(), tcx))
                })
            } else {
                false // union 暂不处理
            }
        }

        // 其他类型默认不可 Fuzz
        _ => false,
    }
}

pub fn jump_all_binders<'tcx>(fn_did: DefId, tcx: TyCtxt<'tcx>) -> FnSig<'tcx> {
    let early_fn_sig = tcx.fn_sig(fn_did);
    let binder_fn_sig = early_fn_sig.instantiate_identity();
    tcx.liberate_late_bound_regions(fn_did, binder_fn_sig)
}
