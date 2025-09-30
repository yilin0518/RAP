mod stmt;
mod var;
use super::utils::{self};
use rustc_middle::ty::{self, Ty, TyCtxt};
use std::collections::HashMap;
pub use stmt::{ApiCall, Stmt, StmtKind, UseKind};
pub use var::{Var, VarState, DUMMY_INPUT_VAR};

#[derive(Clone)]
pub struct Context<'tcx> {
    stmts: Vec<Stmt<'tcx>>,
    var_ty: HashMap<Var, Ty<'tcx>>,
    var_mut: HashMap<Var, ty::Mutability>,
    var_state: HashMap<Var, VarState>,
    num_apicall: usize,
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> Context<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Context<'tcx> {
        Context {
            stmts: Vec::new(),
            var_ty: HashMap::new(),
            var_mut: HashMap::new(),
            var_state: HashMap::new(),
            num_apicall: 0,
            tcx,
        }
    }

    pub fn num_apicall(&self) -> usize {
        self.num_apicall
    }

    pub fn num_stmt(&self) -> usize {
        self.stmts.len()
    }

    pub fn stmts(&self) -> &[Stmt<'tcx>] {
        &self.stmts
    }

    pub fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    pub fn add_stmt(&mut self, stmt: Stmt<'tcx>) -> &Stmt<'tcx> {
        if stmt.kind().is_call() {
            self.num_apicall += 1;
        }
        self.stmts.push(stmt);
        self.stmts.last().unwrap()
    }

    pub fn vars(&self) -> impl Iterator<Item = Var> + '_ {
        self.var_state.keys().copied()
    }

    fn lift_mutability(&mut self, var: Var, mutability: ty::Mutability) {
        if matches!(mutability, ty::Mutability::Mut) {
            self.var_mut.insert(var, ty::Mutability::Mut);
        }
    }

    pub fn var_mutability(&self, var: Var) -> ty::Mutability {
        *self.var_mut.get(&var).unwrap_or(&ty::Mutability::Not)
    }

    pub fn type_of(&self, var: Var) -> Ty<'tcx> {
        self.var_ty[&var]
    }

    pub fn var_state(&self, var: Var) -> VarState {
        self.var_state[&var]
    }

    pub fn set_var_moved(&mut self, var: Var) -> VarState {
        self.set_var_state(var, VarState::Moved)
    }

    pub fn set_var_state(&mut self, var: Var, state: VarState) -> VarState {
        assert!(!matches!(state, VarState::Borrowed(..)));
        let old_state = self
            .var_state
            .insert(var, state)
            .expect("var are expected always have a var state");
        if old_state == VarState::Moved {
            unreachable!("try to change the varstate of moved var {var} to {state}");
        }
        old_state
    }

    pub fn set_var_borrowed(&mut self, var: Var, mutability: ty::Mutability) -> VarState {
        self.lift_mutability(var, mutability);
        self.var_state
            .insert(var, VarState::Borrowed(mutability))
            .expect("var are expected always have a var state")
    }

    pub fn available_vars(&self) -> impl Iterator<Item = Var> + '_ {
        let iter = self
            .var_state
            .iter()
            .filter_map(|(var, state)| match state {
                VarState::Live | VarState::Borrowed(_) => Some(*var),
                _ => None,
            });
        iter
    }

    pub fn all_possible_providers(&self, ty: Ty<'tcx>) -> Vec<Var> {
        let mut ret = Vec::new();
        if utils::is_fuzzable_ty(ty, self.tcx) {
            ret.push(DUMMY_INPUT_VAR);
        }
        for var in self.available_vars() {
            if utils::is_ty_eq(ty, self.type_of(var), self.tcx) {
                ret.push(var.clone());
            }
        }
        ret
    }

    pub fn mk_var(&mut self, ty: Ty<'tcx>, is_input: bool) -> Var {
        let next_var = Var(self.var_ty.len() + 1, is_input);
        self.var_ty.insert(next_var, ty);
        self.var_mut.insert(next_var, ty::Mutability::Not);
        // if the type of var is unit, the var should never be used.
        self.var_state.insert(
            next_var,
            if !ty.is_unit() {
                VarState::Live
            } else {
                VarState::Moved
            },
        );
        next_var
    }
}
