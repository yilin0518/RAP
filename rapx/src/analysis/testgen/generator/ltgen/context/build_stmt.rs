use crate::analysis::testgen::context::{ApiCall, UseKind, VarState, DUMMY_INPUT_VAR};
use crate::analysis::testgen::context::{Stmt, Var};
use crate::analysis::testgen::generator::ltgen::context::LtContext;
use crate::analysis::testgen::generator::ltgen::folder::RidExtractFolder;
use crate::analysis::testgen::generator::ltgen::lifetime::RegionNode;
use crate::analysis::testgen::utils;
use crate::{rap_debug, rap_trace};
use rustc_hir::LangItem;
use rustc_middle::ty::{self, Ty, TyCtxt, TyKind, TypeFoldable};
use rustc_span::sym;
use std::collections::VecDeque;

fn static_str_ref<'tcx>(tcx: TyCtxt<'tcx>) -> Ty<'tcx> {
    Ty::new_ref(
        tcx,
        tcx.lifetimes.re_static,
        tcx.types.str_,
        ty::Mutability::Not,
    )
}

impl<'tcx, 'a> LtContext<'tcx, 'a> {
    /// from is exclusive
    fn set_implicit_drop_state_from(&mut self, from: Var) {
        let mut q = VecDeque::from([self.rid_of(from).into()]);
        let mut visited = vec![false; self.region_graph.total_node_count()];
        visited[self.rid_of(from).index()] = true;
        while let Some(rid) = q.pop_front() {
            if let RegionNode::Named(var) = self.region_graph.get_node(rid) {
                if from != var && self.cx.var_state(var).is_dead() {
                    continue;
                }
                self.cx.set_var_state(var, VarState::Dropped);
                rap_debug!("implicitly set var {} dropped", var);
            }
            for next_idx in self
                .region_graph
                .inner()
                .neighbors_directed(rid.into(), petgraph::Direction::Incoming)
            {
                if !visited[next_idx.index()] {
                    visited[next_idx.index()] = true;
                    q.push_back(next_idx.into());
                }
            }
        }
    }

    fn borrow_var(&mut self, var: Var, mutability: ty::Mutability) {
        match self.cx.set_var_borrowed(var, mutability) {
            VarState::Borrowed(ty::Mutability::Not) => {
                if mutability.is_mut() {
                    self.set_implicit_drop_state_from(var);
                }
            }
            VarState::Borrowed(ty::Mutability::Mut) => {
                self.set_implicit_drop_state_from(var);
            }
            _ => {}
        }
    }

    pub fn add_drop_stmt(&mut self, dropped: Var) {
        if !self
            .cx
            .set_var_state(dropped, VarState::Dropped)
            .is_dropped()
        {
            let var = self.mk_var(self.tcx.types.unit, false);
            self.cx.add_stmt(Stmt::drop_(var, dropped));
            self.set_implicit_drop_state_from(dropped);
        }
    }

    pub fn add_use_stmt(&mut self, var: Var, use_kind: UseKind) -> Var {
        let retvar = self.mk_var(self.tcx.types.unit, false);
        self.cx.add_stmt(Stmt::use_(retvar, var, use_kind));
        retvar
    }

    pub fn add_box_stmt(&mut self, boxed: Var) -> Var {
        self.cx.set_var_state(boxed, VarState::Moved);
        let ty = self.cx.type_of(boxed);
        let var = self.mk_var(Ty::new_box(self.tcx, ty), false);
        self.cx.add_stmt(Stmt::box_(var, boxed));
        var
    }

    /// deref should explicitly annotate the type of deref var
    /// &'a T -> &'a U
    pub fn add_deref_stmt(
        &mut self,
        derefed: Var,
        ty: Ty<'tcx>,
        mutability: ty::Mutability,
    ) -> Var {
        self.borrow_var(derefed, mutability);
        let ref_ty = Ty::new_ref(self.tcx, self.region_of(derefed), ty, mutability);
        let var = self.mk_var(ref_ty, false);
        self.cx.add_stmt(Stmt::deref_(var, derefed, mutability));
        var
    }

    pub fn add_input_stmt(&mut self, ty: Ty<'tcx>) -> Var {
        let var;

        match ty.kind() {
            ty::Adt(def, args) => {
                if self.tcx.is_lang_item(def.did(), LangItem::String) {
                    let inner_var = self.add_input_stmt(static_str_ref(self.tcx));
                    var = self.mk_var(ty, false);
                    self.cx.add_stmt(Stmt::special_call(
                        "String::from".to_owned(),
                        vec![inner_var],
                        var,
                    ));
                    return var;
                } else if self.tcx.is_diagnostic_item(sym::Vec, def.did()) {
                    let inner_ty = args.type_at(0);
                    let inner_var = self.add_input_stmt(Ty::new_array(self.tcx, inner_ty, 3)); // FIXME: vec length is fixed to 3
                    var = self.mk_var(ty, false);
                    self.cx.add_stmt(Stmt::special_call(
                        "Vec::from".to_owned(),
                        vec![inner_var],
                        var,
                    ));
                    return var;
                }
            }
            _ => {}
        }

        if let ty::Ref(_, inner_ty, mutability) = ty.kind() {
            match (inner_ty.kind(), mutability) {
                (TyKind::Str, ty::Mutability::Not) => {
                    var = self.mk_var(static_str_ref(self.tcx), true);
                    self.cx.add_stmt(Stmt::input(var));
                }
                (TyKind::Slice(slice_ty), _) => {
                    let inner_var = self.add_input_stmt(Ty::new_array(self.tcx, *slice_ty, 3));
                    let boxed = self.add_box_stmt(inner_var);
                    let var_ty = self.cx.type_of(inner_var);
                    let var_inner_ty = match var_ty.kind() {
                        TyKind::Array(inner_ty, _) => Ty::new_slice(self.tcx, *inner_ty),
                        _ => panic!("type should be array"),
                    };
                    var = self.add_deref_stmt(boxed, var_inner_ty, *mutability);
                }
                (TyKind::Str, ty::Mutability::Mut) => {
                    // FIXME: &mut str can be generated by input, but this usage is really rere.
                    // For now we just panic and expect it never happens.
                    panic!("&mut str is not supported yet");
                }
                _ => {
                    let inner_var = self.add_input_stmt(*inner_ty);
                    let boxed = self.add_box_stmt(inner_var);
                    var = self.add_deref_stmt(boxed, self.cx.type_of(inner_var), *mutability);
                }
            }
        } else {
            var = self.mk_var(ty, true);
            self.cx.add_stmt(Stmt::input(var));
        }
        var
    }

    pub fn is_var_impl_copy(&self, var: Var) -> bool {
        if var == DUMMY_INPUT_VAR {
            return true;
        }
        utils::is_ty_impl_copy(self.cx.type_of(var), self.tcx)
    }

    pub fn add_call_stmt(&mut self, mut call: ApiCall<'tcx>) -> Var {
        let tcx = self.tcx;
        let fn_did = call.fn_did;
        let fn_sig = utils::fn_sig_with_generic_args(fn_did, call.generic_args(), tcx);

        let output_ty = fn_sig.output();
        for idx in 0..fn_sig.inputs().len() {
            let arg = call.args[idx];
            let input_ty = fn_sig.inputs()[idx];
            if arg == DUMMY_INPUT_VAR {
                let var = self.add_input_stmt(input_ty);
                call.args[idx] = var;
                self.cx.set_var_state(var, VarState::Moved);
                continue;
            }

            // if var: Copy, simply copy the var
            if utils::is_ty_impl_copy(self.cx.type_of(arg), tcx) {
                continue;
            }

            // if the var is not copy, the ownership of the var is moved into the call
            self.cx.set_var_state(arg, VarState::Moved);
        }

        let var = self.mk_var(output_ty, false);
        let stmt = Stmt::call(call, var);

        self.covered_api.insert(fn_did);

        let real_fn_sig = stmt.mk_fn_sig_with_var_tys(&self.cx);
        rap_trace!("stmt: {:?}", stmt);
        rap_trace!("real_fn_sig: {:?}", real_fn_sig);

        let mut folder = RidExtractFolder::new(self.tcx);
        real_fn_sig.fold_with(&mut folder);

        self.pat_provider
            .get_patterns_with(fn_did, &stmt.as_apicall().generic_args, |patterns| {
                rap_debug!("patterns: {:?}", patterns);
                rap_debug!("regions: {:?}", folder.rids());

                self.region_graph
                    .add_edges_by_patterns(patterns, folder.rids());
            });

        self.cx.add_stmt(stmt);
        var
    }

    pub fn add_ref_stmt(&mut self, var: Var, mutability: ty::Mutability) -> Var {
        self.borrow_var(var, mutability);

        let ref_ty = ty::Ty::new_ref(
            self.tcx,
            self.region_of(var),
            self.cx.type_of(var),
            mutability,
        );
        let new_var = self.mk_var(ref_ty, false);
        self.cx.add_stmt(Stmt::ref_(new_var, var, mutability));
        new_var
    }
}
