use super::stmt::{ApiCall, Stmt, StmtKind, Var, DUMMY_INPUT_VAR};
use super::utils;
use crate::rap_debug;
use crate::rustc_infer::infer::TyCtxtInferExt;
use rustc_hir::def_id::DefId;
use rustc_infer::traits::{Obligation, ObligationCause};
use rustc_middle::ty::{self, ParamEnv, Ty, TyCtxt, TyKind};
use rustc_span::{Span, DUMMY_SP};
use rustc_trait_selection::traits::query::evaluate_obligation::InferCtxtExt;
use rustc_type_ir::RegionKind::ReErased;
use std::{
    collections::{HashMap, HashSet},
    rc::Rc,
};

pub trait StmtBody {
    fn stmts(&self) -> &[Stmt];
    fn add_stmt(&mut self, stmt: Stmt);
}

pub trait Context<'tcx>: StmtBody {
    fn tcx(&self) -> TyCtxt<'tcx>;

    fn complexity(&self) -> usize {
        self.stmts().len()
    }

    fn mk_var(&mut self, ty: Ty<'tcx>, is_input: bool) -> Var;

    fn remove_var(&mut self, var: Var);

    fn type_of(&self, var: Var) -> Ty<'tcx>;

    fn available_values(&self) -> &HashSet<Var>;

    // if the output_ty of expr does not implement Copy, we need to remove the expr from the available set
    fn remove_var_from_available(&mut self, var: Var) -> bool {
        let tcx = self.tcx();
        if var == DUMMY_INPUT_VAR {
            return false;
        }
        if !self.available_values().contains(&var) {
            panic!("var {:?} not in available set", var);
        }

        let output_ty = self.type_of(var);
        let is_mut_ref =
            output_ty.is_ref() && matches!(output_ty.ref_mutability(), Some(ty::Mutability::Mut));

        if !is_mut_ref && utils::is_ty_impl_copy(output_ty, tcx) {
            return false;
        }

        self.remove_var(var);
        true
    }

    fn all_possible_providers(&self, ty: Ty<'tcx>) -> Vec<Var> {
        let mut ret = Vec::new();
        if utils::is_fuzzable_ty(ty, self.tcx()) {
            ret.push(DUMMY_INPUT_VAR);
        }
        for val in self.available_values() {
            if utils::is_ty_eq(ty, self.type_of(*val), self.tcx()) {
                ret.push(val.clone());
            }
        }
        ret
    }

    fn add_input_stmt(&mut self, ty: Ty<'tcx>) -> Var {
        let var;
        if let ty::Ref(_, inner_ty, mutability) = ty.kind() {
            let inner_var = self.add_input_stmt(*inner_ty);
            var = self.mk_var(ty, false);
            self.add_stmt(Stmt::ref_(var, inner_var, *mutability));
        } else {
            var = self.mk_var(ty, true);
            self.add_stmt(Stmt::input(var));
        }
        var
    }

    fn add_call_stmt(&mut self, mut call: ApiCall) -> Var {
        let tcx = self.tcx();
        let fn_sig = utils::jump_all_binders(call.fn_did, tcx);
        let output_ty = fn_sig.output();
        for idx in 0..fn_sig.inputs().len() {
            let arg = call.args[idx];
            let input_ty = fn_sig.inputs()[idx];
            self.remove_var_from_available(arg);
            if arg == DUMMY_INPUT_VAR {
                let var = self.add_input_stmt(input_ty);
                call.args[idx] = var;
            }
        }
        let var = self.mk_var(output_ty, false);
        let stmt = Stmt {
            kind: StmtKind::Call(call),
            place: var,
        };
        self.add_stmt(stmt);
        var
    }

    fn ref_region_ty(&self, var: Var) -> ty::Region<'tcx> {
        self.tcx().lifetimes.re_erased
    }

    fn add_ref_stmt(&mut self, var: Var, mutability: ty::Mutability) -> Var {
        let ref_ty = ty::Ty::new_ref(
            self.tcx(),
            self.ref_region_ty(var),
            self.type_of(var),
            mutability,
        );
        let new_var = self.mk_var(ref_ty, false);
        self.add_stmt(Stmt::ref_(new_var, var, mutability));
        new_var
    }
}

#[derive(Clone)]
pub struct ContextBase<'tcx> {
    stmts: Vec<Stmt>,
    available: HashSet<Var>,
    var_ty: HashMap<Var, Ty<'tcx>>,
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> ContextBase<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> ContextBase<'tcx> {
        ContextBase {
            stmts: Vec::new(),
            available: HashSet::new(),
            var_ty: HashMap::new(),
            tcx,
        }
    }

    pub fn type_of(&self, var: Var) -> Ty<'tcx> {
        *self.var_ty.get(&var).expect("no type for var")
    }
}

impl<'tcx> StmtBody for ContextBase<'tcx> {
    fn stmts(&self) -> &[Stmt] {
        &self.stmts
    }
    fn add_stmt(&mut self, stmt: Stmt) {
        self.stmts.push(stmt);
    }
}

impl<'tcx> Context<'tcx> for ContextBase<'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

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
        self.var_ty[&var]
    }
}
