use crate::analysis::testgen::context::{ApiCall, UseKind, VarState, DUMMY_INPUT_VAR};
use crate::analysis::testgen::context::{Stmt, Var};
use crate::analysis::testgen::generator::ltgen::context::LtContext;
use crate::analysis::testgen::generator::ltgen::folder::RidExtractFolder;
use crate::analysis::testgen::generator::ltgen::lifetime::RegionNode;
use crate::analysis::testgen::utils;
use crate::{rap_debug, rap_trace};
use rustc_hir::def_id::DefId;
use rustc_hir::LangItem;
use rustc_middle::ty::{self, Ty, TyCtxt, TyKind, TypeFoldable};
use rustc_span::sym::{self};
use std::collections::VecDeque;

fn str_ref<'tcx>(region: ty::Region<'tcx>, tcx: TyCtxt<'tcx>) -> Ty<'tcx> {
    Ty::new_ref(tcx, region, tcx.types.str_, ty::Mutability::Not)
}

impl<'tcx, 'a> LtContext<'tcx, 'a> {
    ///
    /// drop all vars depended on `from`, but skip dropping `from` itself
    fn set_implicit_drop_state_from(&mut self, from: Var) {
        let mut q = VecDeque::from([self.rid_of(from).into()]);
        let mut visited = vec![false; self.region_graph.total_node_count()];
        let mut drop_var = Vec::new();
        visited[self.rid_of(from).index()] = true;
        while let Some(rid) = q.pop_front() {
            if let RegionNode::Named(var) = self.region_graph.get_node(rid) {
                if self.cx.var_state(var).is_dead() {
                    continue;
                }
                if from != var {
                    drop_var.push(var);
                }
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
        for var in drop_var.into_iter().rev() {
            self.cx.set_var_state(var, VarState::Dropped);
            let unit_place = self.mk_var(self.tcx.types.unit, false);
            self.cx.add_stmt(Stmt::drop_(unit_place, var));
            rap_debug!("implicitly set var {} dropped", var);
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

    fn move_var(&mut self, var: Var) {
        self.set_implicit_drop_state_from(var);
        self.cx.set_var_moved(var);
    }

    pub fn add_drop_stmt(&mut self, dropped: Var) {
        self.set_implicit_drop_state_from(dropped);
        if !self
            .cx
            .set_var_state(dropped, VarState::Dropped)
            .is_dropped()
        {
            let var = self.mk_var(self.tcx.types.unit, false);
            self.cx.add_stmt(Stmt::drop_(var, dropped));
            self.explicit_droped_cnt += 1;
        }
    }

    pub fn add_exploit_stmt(&mut self, var: Var, use_kind: UseKind) -> Var {
        let retvar = self.mk_var(self.tcx.types.unit, false);
        self.cx.add_stmt(Stmt::exploit(retvar, var, use_kind));
        retvar
    }

    pub fn add_box_stmt(&mut self, boxed: Var) -> Var {
        self.move_var(boxed);
        let ty = self.cx.type_of(boxed);
        let var = self.mk_var(Ty::new_box(self.tcx, ty), false);
        self.cx.add_stmt(Stmt::box_(var, boxed));
        var
    }

    pub fn try_add_input_stmts_for_std_item(
        &mut self,
        ty: Ty<'tcx>,
        item_did: DefId,
        args: ty::GenericArgsRef<'tcx>,
    ) -> Option<Var> {
        if self.tcx.is_lang_item(item_did, LangItem::String) {
            let inner_var =
                self.try_add_input_stmts(str_ref(self.tcx.lifetimes.re_static, self.tcx), true);
            let var = self.mk_var(ty, false);
            self.move_var(inner_var);
            self.cx.add_stmt(Stmt::special_call(
                "String::from".to_owned(),
                vec![inner_var],
                var,
            ));
            Some(var)
        } else if self.tcx.is_diagnostic_item(sym::Vec, item_did) {
            let inner_ty = args.type_at(0);
            let inner_var = self.try_add_input_stmts(Ty::new_array(self.tcx, inner_ty, 3), true); // FIXME: vec length is fixed to 3
            let var = self.mk_var(ty, false);
            self.move_var(inner_var);
            self.cx.add_stmt(Stmt::special_call(
                "Vec::from".to_owned(),
                vec![inner_var],
                var,
            ));
            Some(var)
        } else if self.tcx.is_diagnostic_item(sym::Arc, item_did) {
            let inner_ty = args.type_at(0);
            let inner_var = self.try_add_input_stmts(inner_ty, true);
            let var = self.mk_var(ty, false);
            self.move_var(inner_var);
            self.cx.add_stmt(Stmt::special_call(
                "std::sync::Arc::new".to_owned(),
                vec![inner_var],
                var,
            ));
            Some(var)
        } else {
            None
        }
    }

    /// try directly add input stmt to generate an instance of ty.
    /// This could fail since some types cannot be directly obtained from input,
    /// e.g., `[&i32]`. This function minimizes the number of input statements
    /// by making the types generated by the input statements as complex as possible.
    ///
    /// output: if ty can be directly generated, retrun DUMMY_INPUT_VAR,
    /// otherwise return a var representing the instance of ty.
    /// if must_instantiate is true, this function will always return a var
    /// representing the instance of ty.
    pub fn try_add_input_stmts(&mut self, ty: Ty<'tcx>, must_instantiate: bool) -> Var {
        let var;
        match ty.kind() {
            ty::Adt(def, args) => {
                if let Some(var) = self.try_add_input_stmts_for_std_item(ty, def.did(), args) {
                    return var;
                }
                var = DUMMY_INPUT_VAR;
            }
            ty::Ref(region, inner_ty, mutability) => {
                match (region.kind(), inner_ty.kind(), mutability) {
                    // Handle 'static
                    (ty::ReStatic, _, ty::Mutability::Mut) => {
                        panic!("&'static mut T is not supported yet");
                    }
                    (ty::ReStatic, _, ty::Mutability::Not) => {
                        var = DUMMY_INPUT_VAR;
                    }
                    // Handle &str/&mut str
                    (_, TyKind::Str, _) => {
                        let inner_var = self.try_add_input_stmts(
                            Ty::new_lang_item(self.tcx, self.tcx.types.unit, LangItem::String)
                                .unwrap(),
                            true,
                        );
                        var = self.add_ref_stmt(inner_var, *mutability, Some(self.tcx.types.str_));
                    }
                    // handle &[T]/&mut [T]
                    (_, TyKind::Slice(slice_ty), _) => {
                        //TODO: the length of array is fixed to 3, but should be determined when generated
                        let inner_var =
                            self.try_add_input_stmts(Ty::new_array(self.tcx, *slice_ty, 3), true);
                        let box_var = self.add_box_stmt(inner_var);
                        var = self.add_slice_ref_stmt(box_var, *mutability, *slice_ty);
                    }

                    _ => {
                        let inner_var = self.try_add_input_stmts(*inner_ty, true);
                        let box_var = self.add_box_stmt(inner_var);
                        var = self.add_ref_stmt(
                            box_var,
                            *mutability,
                            Some(self.cx.type_of(inner_var)),
                        );
                    }
                }
            }
            ty::Tuple(tys) => {
                let mut vars = Vec::new();
                let mut should_instantiate = false;
                for inner_ty in tys.iter() {
                    let var = self.try_add_input_stmts(inner_ty, false);
                    vars.push(var);
                    if var != DUMMY_INPUT_VAR {
                        should_instantiate = true;
                    }
                }
                if !should_instantiate {
                    var = DUMMY_INPUT_VAR;
                } else {
                    for (inner_ty, inner_var) in tys.iter().zip(vars.iter_mut()) {
                        if *inner_var == DUMMY_INPUT_VAR {
                            *inner_var = self.try_add_input_stmts(inner_ty, true);
                        }
                        self.move_var(*inner_var);
                    }
                    var = self.mk_var(ty, false);
                    self.cx.add_stmt(Stmt::tuple(var, vars));
                }
            }
            ty::Array(array_ty, array_len) => {
                let inner_var = self.try_add_input_stmts(*array_ty, false);
                if inner_var == DUMMY_INPUT_VAR {
                    var = DUMMY_INPUT_VAR;
                } else {
                    let len = array_len.try_to_target_usize(self.tcx).unwrap();
                    let mut vars = Vec::new();
                    for _ in 0..len {
                        let inner_var = self.try_add_input_stmts(*array_ty, true);
                        self.move_var(inner_var);
                        vars.push(inner_var);
                    }
                    var = self.mk_var(ty, false);
                    self.cx.add_stmt(Stmt::array(var, vars));
                }
            }
            _ => {
                var = DUMMY_INPUT_VAR;
            }
        }

        if var == DUMMY_INPUT_VAR && must_instantiate {
            let input_var = self.mk_var(ty, true);
            self.cx.add_stmt(Stmt::input(input_var));
            input_var
        } else {
            var
        }
    }

    pub fn add_input_stmts(&mut self, ty: Ty<'tcx>) -> Var {
        self.try_add_input_stmts(ty, true)
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
                let var = self.add_input_stmts(input_ty);
                call.args[idx] = var;
                self.cx.set_var_state(var, VarState::Moved);
                continue;
            }

            // if the var is not copy, the ownership of the var is moved into the call
            if !utils::is_ty_impl_copy(self.cx.type_of(arg), tcx) {
                self.move_var(arg);
            }
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

    pub fn add_ref_stmt(
        &mut self,
        var: Var,
        mutability: ty::Mutability,
        as_ref_ty: Option<Ty<'tcx>>, // None represent &T
    ) -> Var {
        self.borrow_var(var, mutability);

        let ref_ty = Ty::new_ref(
            self.tcx,
            self.region_of(var),
            as_ref_ty.unwrap_or(self.cx.type_of(var)),
            mutability,
        );

        let new_var = self.mk_var(ref_ty, false);
        self.cx.add_stmt(Stmt::ref_(new_var, var, mutability));
        new_var
    }

    pub fn add_slice_ref_stmt(
        &mut self,
        var: Var,
        mutability: ty::Mutability,
        slice_ty: Ty<'tcx>,
    ) -> Var {
        self.borrow_var(var, mutability);

        let ref_slice_ty = ty::Ty::new_ref(
            self.tcx,
            self.region_of(var),
            Ty::new_slice(self.tcx, slice_ty),
            mutability,
        );

        let new_var = self.mk_var(ref_slice_ty, false);
        self.cx.add_stmt(Stmt::slice_ref(new_var, var, mutability));
        new_var
    }
}
