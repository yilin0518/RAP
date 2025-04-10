pub mod input;

use super::context::{Context, ContextBase, StmtBody};
use super::context::{Stmt, StmtKind, Var};
use input::{InputGen, SillyInputGen};
use std::collections::{HashMap, HashSet};
use std::fmt::{self, Display};

use chrono::format;
use rustc_middle::ty::{self, Ty, TyCtxt, TyKind};

pub struct SynOption {
    pub crate_name: String,
}

pub trait Synthesizer<'tcx> {
    fn syn<C: Context<'tcx>>(&mut self, cx: C, tcx: TyCtxt<'tcx>) -> String;
}

pub struct FuzzDriverSynImpl<I: InputGen> {
    input_gen: I,
    option: SynOption,
}

impl<I: InputGen> FuzzDriverSynImpl<I> {
    pub fn new(input_gen: I, option: SynOption) -> Self {
        Self { input_gen, option }
    }

    fn stmt_kind_str<'tcx>(&mut self, stmt: &Stmt, cx: &impl Context<'tcx>) -> String {
        match stmt.kind() {
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
                let ty = cx.type_of(stmt.place).peel_refs();
                self.input_gen.gen(ty, cx.tcx()).to_string()
            }
            StmtKind::Ref(var, mutability) => {
                format!("{}{}", mutability.ref_prefix_str(), self.var_str(**var))
            }
            StmtKind::Deref(var) => {
                format!("*{}", self.var_str(**var))
            }
            _ => todo!(),
        }
    }

    fn var_str(&self, var: Var) -> String {
        format!("{}", var)
    }

    fn ty_str<'tcx>(&self, ty: Ty<'tcx>) -> String {
        if ty.is_slice(){
            if let TyKind::Slice(inner_ty) = ty.kind(){
                format!("[{}; 3]", self.ty_str(*inner_ty))
            }
            else{
                format!("{}", ty)
            }
        }
        else{
            format!("{}", ty)
        }
    }

    fn stmt_str<'tcx>(&mut self, stmt: Stmt, cx: &impl Context<'tcx>) -> String {
        let var = stmt.place;
        let var_ty = cx.type_of(var);
        let stmt_str = self.stmt_kind_str(&stmt, cx);
        if !var_ty.is_unit() {
            format!(
                "let {}{}: {} = {};",
                cx.var_mutability(var).prefix_str(),
                self.var_str(var),
                self.ty_str(cx.tcx().erase_regions(var_ty)),
                stmt_str
            )
        } else {
            format!("{};", stmt_str)
        }
    }

    fn header_str(&self) -> String {
        format!(
            "extern crate {};\nuse {}::*;",
            self.option.crate_name, self.option.crate_name
        )
    }

    fn main_str<'tcx>(&mut self, cx: &impl Context<'tcx>) -> String {
        let mut ret = String::new();
        ret.push_str("fn main() {\n");
        let indent = "    ";
        for stmt in cx.stmts() {
            ret.push_str(indent);
            ret.push_str(&self.stmt_str(stmt.clone(), cx));
            ret.push_str("\n");
        }
        ret.push_str("}\n");
        ret
    }
}

impl<'tcx, I: InputGen> Synthesizer<'tcx> for FuzzDriverSynImpl<I> {
    fn syn<C: Context<'tcx>>(&mut self, cx: C, tcx: TyCtxt<'tcx>) -> String {
        format!("{}\n{}", self.header_str(), self.main_str(&cx))
    }
}
