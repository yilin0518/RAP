use rustc_hir::def_id::DefId;
use rustc_middle::ty::{self, Ty};
use std::fmt;
use std::fmt::Display;
use std::rc::Rc;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]

pub struct Var(pub usize, pub bool); // bool is true if the var is an input var

impl Display for Var {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "v{}", self.0)
    }
}

pub static DUMMY_INPUT_VAR: Var = Var(0, true);

#[derive(Debug, Clone, Eq, Hash, PartialEq)]
pub struct ApiCall {
    pub fn_did: DefId,
    pub args: Vec<Var>,
}

// pub type StmtRef<'tcx> = Rc<Stmt<'tcx>>;

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum StmtKind {
    Input,
    Call(ApiCall),
    Split(usize, Vec<Var>),        // (a, b) -> a, b
    Concat(Vec<Var>),              // a, b -> (a, b)
    Ref(Box<Var>, ty::Mutability), // a -> &a
    Deref(Box<Var>),               // &a -> a
}

impl StmtKind {
    pub fn is_input(&self) -> bool {
        matches!(self, StmtKind::Input)
    }
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Stmt {
    pub kind: StmtKind,
    pub place: Var,
}

impl Stmt {
    // pub fn input(ty: Ty<'tcx>) -> StmtRef<'tcx> {
    //     Rc::new(Stmt {
    //         kind: StmtKind::Input,
    //         retval: None,
    //         output_ty: ty,
    //     })
    // }

    pub fn call(call: ApiCall, retval: Var) -> Stmt {
        Stmt {
            kind: StmtKind::Call(call),
            place: retval,
        }
    }

    // pub fn split(idx: usize, args: Vec<Var>, output_ty: Ty<'tcx>) -> StmtRef<'tcx> {
    //     Rc::new(Stmt {
    //         kind: StmtKind::Split(idx, args),
    //         retval: None,
    //         output_ty,
    //     })
    // }

    // pub fn concat(args: Vec<Var>, output_ty: Ty<'tcx>) -> StmtRef<'tcx> {
    //     Rc::new(Stmt {
    //         kind: StmtKind::Concat(args),
    //         retval: None,
    //         output_ty,
    //     })
    // }

    // pub fn ref_expr(
    //     expr: StmtRef<'tcx>,
    //     mutability: ty::Mutability,
    //     output_ty: Ty<'tcx>,
    // ) -> StmtRef<'tcx> {
    //     Rc::new(Stmt {
    //         kind: StmtKind::Ref(Box::new(expr), mutability),
    //         output_ty,
    //     })
    // }

    // pub fn deref_expr(expr: StmtRef<'tcx>, output_ty: Ty<'tcx>) -> StmtRef<'tcx> {
    //     Rc::new(Stmt {
    //         kind: StmtKind::Deref(Box::new(expr)),
    //         output_ty,
    //     })
    // }

    pub fn kind(&self) -> StmtKind {
        self.kind.clone()
    }
}
