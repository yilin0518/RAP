use super::context::stmt::{Stmt, StmtKind};
use super::context::Context;
use std::collections::{HashMap, HashSet};
use std::fmt::{self, Display};

use rustc_middle::ty::TyCtxt;
pub trait Synthesizer<'tcx> {
    fn syn(&mut self, cx: Context<'tcx>, tcx: TyCtxt<'tcx>) -> String;
}

pub struct FuzzDriverSynImpl<'tcx> {
    phantom: std::marker::PhantomData<&'tcx ()>,
}

impl<'tcx> FuzzDriverSynImpl<'tcx> {
    // fn serialize<'tcx>(&mut self, cx: Context<'tcx>, tcx: TyCtxt<'tcx>) -> String {}
    pub fn new() -> Self {
        Self {
            phantom: std::marker::PhantomData,
        }
    }

    fn stmt_kind_str(&mut self, kind: StmtKind, cx: &Context<'tcx>) -> String {
        match kind {
            StmtKind::Call(call) => {
                format!(
                    "{}({})",
                    cx.tcx().def_path_str(call.fn_did),
                    call.args
                        .iter()
                        .map(|arg| arg.to_string())
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
            StmtKind::Input => {
                format!("input()")
            }
            _ => todo!(),
        }
    }

    fn stmt_str(&mut self, stmt: Stmt, cx: &Context<'tcx>) -> String {
        let var = stmt.place;
        let var_ty = cx.type_of(var);
        let expr_str = self.stmt_kind_str(stmt.kind, cx);
        if !var_ty.is_unit() {
            format!("let {}: {} = {};", var, var_ty, expr_str)
        } else {
            format!("{};", expr_str)
        }
    }
}

impl<'tcx> Synthesizer<'tcx> for FuzzDriverSynImpl<'tcx> {
    fn syn(&mut self, cx: Context<'tcx>, tcx: TyCtxt<'tcx>) -> String {
        let mut ret = String::new();
        ret.push_str("fn main() {\n");
        let indent = "    ";
        for stmt in cx.stmts() {
            ret.push_str(indent);
            ret.push_str(&self.stmt_str(stmt.clone(), &cx));
            ret.push_str("\n");
        }
        ret.push_str("}\n");
        ret
    }
}
