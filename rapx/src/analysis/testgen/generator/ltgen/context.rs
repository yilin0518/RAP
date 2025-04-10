use super::lifetime_constraint::constraint_str;
use crate::analysis::testgen::context::{Context, HoldTyCtxt, StmtBody};
use crate::analysis::testgen::context::{Stmt, StmtKind, Var};
use crate::analysis::testgen::utils;
use crate::rap_debug;
use rustc_infer::infer::{self, InferCtxt, TyCtxtInferExt};
use rustc_infer::traits::ObligationCause;
use rustc_middle::ty::{self, Ty, TyCtxt, TyKind};
use rustc_span::DUMMY_SP;

use std::collections::{HashMap, HashSet};

pub struct LtContext<'tcx> {
    stmts: Vec<Stmt>,
    available: HashSet<Var>,
    var_ty: HashMap<Var, Ty<'tcx>>,
    var_is_mut: HashMap<Var, ty::Mutability>,
    tcx: TyCtxt<'tcx>,
    infcx: InferCtxt<'tcx>,
    param_env: ty::ParamEnv<'tcx>,
    ref_map: HashMap<usize, Var>, // inference id => var
}

impl<'tcx> StmtBody for LtContext<'tcx> {
    fn stmts(&self) -> &[Stmt] {
        &self.stmts
    }
    fn add_stmt(&mut self, stmt: Stmt) {
        let var = stmt.place();
        let var_ty = self.type_of(var);
        let dummy = ObligationCause::dummy();
        let infcx = self.infcx.at(&dummy, self.param_env);
        let define_opaque_types = infer::DefineOpaqueTypes::Yes;

        // maintain lifetime relationship between ref and var
        match stmt.kind() {
            StmtKind::Call(api_call) => {
                let fn_sig = utils::jump_all_binders(api_call.fn_did(), self.tcx());

                let _ = infcx
                    .sub(define_opaque_types, fn_sig.output(), var_ty)
                    .unwrap();

                for (arg, arg_ty) in api_call.args().iter().zip(fn_sig.inputs()) {
                    let _ = infcx
                        .sup(define_opaque_types, *arg_ty, self.type_of(*arg))
                        .unwrap();
                }
            }
            StmtKind::Ref(inner_var, mutability) => {
                let id = match var_ty.kind() {
                    TyKind::Ref(region, _, _) => match region.kind() {
                        ty::RegionKind::ReVar(vid) => vid.index(),
                        _ => {
                            panic!("unexpected region: {:?}", region);
                        }
                    },
                    _ => {
                        panic!("unexpected type: {:?}", var_ty);
                    }
                };
                self.ref_map.insert(id, **inner_var);
            }
            StmtKind::Deref(var) => {
                todo!()
            }
            _ => {}
        }
        self.stmts.push(stmt);
    }

    fn lift_mutability(&mut self, var: Var, mutability: ty::Mutability) {
        if matches!(mutability, ty::Mutability::Mut) {
            self.var_is_mut.insert(var, ty::Mutability::Mut);
        }
    }

    fn var_mutability(&self, var: Var) -> ty::Mutability {
        *self.var_is_mut.get(&var).unwrap_or(&ty::Mutability::Not)
    }
}

impl<'tcx> HoldTyCtxt<'tcx> for LtContext<'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }
}

impl<'tcx> Context<'tcx> for LtContext<'tcx> {
    fn available_values(&self) -> &HashSet<Var> {
        &self.available
    }

    fn mk_var(&mut self, ty: Ty<'tcx>, is_input: bool) -> Var {
        let next_var = Var(self.var_ty.len(), is_input);
        self.var_ty.insert(next_var, ty);
        self.available.insert(next_var);
        next_var
    }

    fn remove_var(&mut self, var: Var) {
        self.available.remove(&var);
    }

    fn type_of(&self, var: Var) -> Ty<'tcx> {
        *self.var_ty.get(&var).expect("no type for var")
    }

    fn ref_region_ty(&self, var: Var) -> ty::Region<'tcx> {
        self.infcx
            .next_region_var(infer::RegionVariableOrigin::BorrowRegion(DUMMY_SP))
    }
}

impl<'tcx> LtContext<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            stmts: Vec::new(),
            available: HashSet::new(),
            var_ty: HashMap::new(),
            tcx,
            infcx: tcx.infer_ctxt().build(),
            param_env: ty::ParamEnv::empty(),
            ref_map: HashMap::new(),
            var_is_mut: HashMap::new(),
        }
    }

    pub fn debug_constraint(&self) {
        let region_constraint_data = self.infcx.take_and_reset_region_constraints();

        for (constraint, _origin) in region_constraint_data.constraints {
            rap_debug!("constraint: {}", constraint_str(constraint, self.tcx()));
        }
    }
}
