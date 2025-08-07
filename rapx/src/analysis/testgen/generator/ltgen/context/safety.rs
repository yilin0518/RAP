use super::super::folder::extract_rids;
use super::super::lifetime::Rid;
use super::super::utils;
use super::LtContext;
use crate::analysis::core::alias::RetAlias;
use crate::analysis::testgen::context::{Stmt, Var};
use crate::{rap_debug, rap_trace};
use rustc_middle::ty::{self, Ty, TyCtxt, TyKind};
use std::collections::{HashMap, HashSet};

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

/// check whether 'lhs : 'rhs is possible.
///
/// condition: exist a `T`, that lhs_ty contains
/// `&T`/`*T` and rhs_ty contains `T`
pub fn check_possibility<'tcx>(lhs_ty: Ty<'tcx>, rhs_ty: Ty<'tcx>, tcx: TyCtxt<'tcx>) -> bool {
    let mut set = HashSet::new();
    let mut ret = false;
    utils::visit_ty_while(rhs_ty, tcx, &mut |ty| {
        rap_trace!("[check_possibility] add {ty}");
        set.insert(tcx.erase_regions(ty));
        true
    });
    utils::visit_ty_while(lhs_ty, tcx, &mut |ty| {
        match ty.kind() {
            TyKind::RawPtr(inner_ty, _) | TyKind::Ref(_, inner_ty, _) => {
                rap_trace!("[check_possibility] check {ty}");
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
    rap_trace!("[check_possibility] ret = {ret}");
    ret
}

impl<'tcx, 'a> LtContext<'tcx, 'a> {
    /// This function returns a set that indicates rids the var may point to
    pub fn detect_potential_point_to(
        &self,
        stmt: &Stmt<'tcx>,
    ) -> Option<HashMap<Var, HashSet<Rid>>> {
        let mut ret = HashMap::new();
        let tcx = self.tcx;

        let call = stmt.as_apicall();

        let fn_sig = stmt.mk_fn_sig_with_var_tys(&self.cx);

        rap_debug!("analysis alias for: {:?} {:?}", call.fn_did, fn_sig);

        let mut check_potential_region_leak = |lhs_var, lhs_ty, rhs_var, rhs_ty| {
            rap_debug!(
                "[check_potential_region_leak] lhs_var = {}: {}, rhs_var = {}: {}",
                lhs_var,
                lhs_ty,
                rhs_var,
                rhs_ty
            );

            let mut rhs_ty_rids = extract_rids(rhs_ty, tcx);
            rap_debug!("rhs rids: {:?}", rhs_ty_rids);

            // if rhs_ty does not bind with any lifetime,
            // this maybe imply that lhs is a reference of rhs (e.g., lhs=&rhs.f)
            // the coresponding lifetime binding 'lhs->'rhs should be added
            // FIXME: the field-sensitive alias analysis is not exactly possible,
            // so we may miss some 'lhs -> 'rhs lifetime bindings
            if rhs_ty_rids.is_empty() && check_possibility(lhs_ty, rhs_ty, tcx) {
                rhs_ty_rids.push(self.rid_of(rhs_var));
            }
            let lhs_rid = self.rid_of(lhs_var);
            let entry: &mut HashSet<Rid> = ret.entry(lhs_var).or_default();

            // add all unsafe regions into entry
            rhs_ty_rids.into_iter().for_each(|rid| {
                if !self.region_graph().prove(lhs_rid, rid) {
                    entry.insert(rid);
                }
            });
        };

        for alias in self
            .alias_map
            .get(&call.fn_did())
            .expect(&format!("{:?} do not have alias infomation", call.fn_did()))
            .aliases()
        {
            rap_debug!("alias: {}", alias);
            // ths alias is symmetric, that is, if (a,b) exists, then (b,a) must exist
            let (lhs_ty, rhs_ty) = destruct_ret_alias(fn_sig, alias, self.tcx);
            let lhs_var = stmt.as_call_arg_at(alias.left_index);
            let rhs_var = stmt.as_call_arg_at(alias.right_index);
            check_potential_region_leak(lhs_var, lhs_ty, rhs_var, rhs_ty);
        }
        if ret.is_empty() {
            return None;
        }
        Some(ret)
    }

    pub fn try_inject_drop(&mut self) -> bool {
        let stmt = self.cx.stmts().last().unwrap();

        if !stmt.kind().is_call() {
            return false;
        }

        let fn_did = stmt.as_apicall().fn_did();

        if !self.alias_map.contains_key(&fn_did) {
            self.lack_of_alias.push(fn_did);
            return false;
        }

        // reborrow stmt here, since we need borrow mutable reference for lack_of_alias
        let stmt = self.cx.stmts().last().unwrap();

        let mut success = false;

        if let Some(vec) = self.detect_potential_point_to(&stmt) {
            for (var, rids) in vec {
                rap_debug!("[unsafe] variable {} lack of binding with {:?}", var, rids);
                for rid in rids {
                    let mut src_rids = Vec::new();
                    self.region_graph.for_each_source(rid, &mut |rid| {
                        if !self.region_graph.is_static(rid) {
                            src_rids.push(rid)
                        }
                    });

                    let dropped_var: Vec<Var> = src_rids
                        .into_iter()
                        .map(|rid| self.region_graph.get_node(rid).as_var())
                        .filter(|var| !self.cx.var_state(*var).is_dead())
                        .collect();

                    if !dropped_var.is_empty() {
                        success = true;
                    }

                    for var in dropped_var.iter() {
                        self.add_drop_stmt(*var);
                    }
                    rap_debug!("[unsafe] drop var: {:?}", dropped_var);
                }
            }
        }

        success
    }
}
