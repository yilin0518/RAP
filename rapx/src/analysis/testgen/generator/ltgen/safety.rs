use std::collections::HashSet;

use rustc_middle::ty::{Ty, TyCtxt, TyKind};

use crate::{analysis::testgen::utils::visit_ty_while, rap_trace};

/// check whether 'lhs : 'rhs is possible.
///
/// condition: exist an `T`, that lhs_ty contains
/// `&T`/`*T` and rhs_ty contains `T`
pub fn check_possibility<'tcx>(lhs_ty: Ty<'tcx>, rhs_ty: Ty<'tcx>, tcx: TyCtxt<'tcx>) -> bool {
    let mut set = HashSet::new();
    let mut ret = false;
    visit_ty_while(rhs_ty, tcx, &mut |ty| {
        set.insert(tcx.erase_regions(ty));
        true
    });
    visit_ty_while(lhs_ty, tcx, &mut |ty| {
        match ty.kind() {
            TyKind::RawPtr(inner_ty, _) | TyKind::Ref(_, inner_ty, _) => {
                if set.contains(inner_ty) {
                    rap_trace!("[check_possibility] find {ty} -> {inner_ty}");
                    ret = true;
                    return false;
                }
            }
            _ => {}
        }
        true
    });
    ret
}
