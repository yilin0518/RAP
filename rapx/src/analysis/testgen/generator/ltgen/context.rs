use super::super::context::{Context, ContextBase, StmtBody};
use super::super::stmt::{Stmt, StmtKind, Var};

use rustc_infer::infer::at::At;
use rustc_infer::infer::{self, InferCtxt, TyCtxtInferExt};
use rustc_infer::traits::ObligationCause;
use rustc_middle::ty::{self, Ty, TyCtxt, TyKind};
use rustc_span::DUMMY_SP;
use rustc_trait_selection::infer::InferCtxtExt;

use std::collections::{HashMap, HashSet};

pub struct LtContext<'tcx> {
    stmts: Vec<Stmt>,
    available: HashSet<Var>,
    var_ty: HashMap<Var, Ty<'tcx>>,
    tcx: TyCtxt<'tcx>,
    infcx: InferCtxt<'tcx>,
}

impl<'tcx> StmtBody for LtContext<'tcx> {
    fn stmts(&self) -> &[Stmt] {
        &self.stmts
    }
    fn add_stmt(&mut self, stmt: Stmt) {
        let place = stmt.place();
        let ty = self.type_of(place);
        let kind = stmt.kind();

        match kind {
            StmtKind::Call(api_call) => {
                todo!()
            }
            StmtKind::Ref(var, mutability) => {
                todo!()
            }
            StmtKind::Deref(var) => {
                todo!()
            }
            _ => {}
        }
        self.stmts.push(stmt);
    }
}

impl<'tcx> Context<'tcx> for LtContext<'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn available_values(&self) -> &HashSet<Var> {
        &self.available
    }

    fn mk_var(&mut self, ty: Ty<'tcx>, is_input: bool) -> Var {
        let next_var = Var(self.var_ty.len(), is_input);
        self.var_ty.insert(next_var, ty);
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
        let infcx = tcx.infer_ctxt().build();
        Self {
            stmts: Vec::new(),
            available: HashSet::new(),
            var_ty: HashMap::new(),
            tcx,
            infcx,
        }
    }
}