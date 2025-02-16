use rustc_hir::def::DefKind;
use rustc_hir::def_id::DefId;
use rustc_hir::def_id::CRATE_DEF_INDEX;
use rustc_middle::ty::Visibility;
use rustc_middle::{
    mir::{Operand, TerminatorKind},
    ty,
    ty::TyCtxt,
};
use std::collections::HashSet;
// use crate::analysis::unsafety_isolation::draw_dot::render_dot_graphs;

use super::{
    generate_dot::{NodeType, UigUnit},
    UnsafetyIsolationCheck,
};

impl<'tcx> UnsafetyIsolationCheck<'tcx> {
    pub fn handle_std_unsafe(&mut self) {
        self.get_all_std_unsafe_def_id_by_treat_std_as_local_crate(self.tcx);
        let mut dot_strs = Vec::new();
        for uig in &self.uigs {
            let dot_str = uig.generate_dot_str();
            uig.compare_labels();
            dot_strs.push(dot_str);
        }
        for uig in &self.single {
            let dot_str = uig.generate_dot_str();
            // uig.compare_labels();
            dot_strs.push(dot_str);
        }
        // println!("single {:?}",self.single.len());
        // render_dot_graphs(dot_strs);
    }

    pub fn get_all_std_unsafe_def_id_by_rustc_extern_crates(
        &mut self,
        tcx: TyCtxt<'_>,
    ) -> HashSet<DefId> {
        let mut visited = HashSet::new();
        let mut unsafe_fn = HashSet::new();
        for &crate_num in tcx.crates(()).iter() {
            let crate_name = tcx.crate_name(crate_num).to_string();
            // if crate_name == "std" || crate_name == "core" || crate_name == "alloc" {
            if crate_name == "core" {
                let crate_root = DefId {
                    krate: crate_num,
                    index: CRATE_DEF_INDEX,
                };
                self.process_def_id(tcx, crate_root, &mut visited, &mut unsafe_fn);
                println!(
                    "{:?} has {:?} MIR instances totally, with {:?} unsafe fns.",
                    crate_name,
                    visited.len(),
                    unsafe_fn.len()
                );
            }
        }
        // Self::print_hashset(&unsafe_fn);
        unsafe_fn
    }

    pub fn get_all_std_unsafe_def_id_by_treat_std_as_local_crate(
        &mut self,
        tcx: TyCtxt<'_>,
    ) -> HashSet<DefId> {
        let mut unsafe_fn = HashSet::new();
        let def_id_sets = tcx.mir_keys(());
        for local_def_id in def_id_sets {
            let def_id = local_def_id.to_def_id();
            if Self::filter_mir(def_id) {
                continue;
            }
            if tcx.def_kind(def_id) == DefKind::Fn || tcx.def_kind(def_id) == DefKind::AssocFn {
                if self.check_safety(def_id) && self.tcx.visibility(def_id) == Visibility::Public {
                    unsafe_fn.insert(def_id);
                    self.insert_uig(def_id, self.get_callees(def_id), self.get_cons(def_id));
                }
            }
        }
        unsafe_fn
    }

    pub fn process_def_id(
        &mut self,
        tcx: TyCtxt<'_>,
        def_id: DefId,
        visited: &mut HashSet<DefId>,
        unsafe_fn: &mut HashSet<DefId>,
    ) {
        if !visited.insert(def_id) || Self::filter_mir(def_id) {
            return;
        }
        match tcx.def_kind(def_id) {
            DefKind::Fn | DefKind::AssocFn => {
                if self.check_safety(def_id) && self.tcx.visibility(def_id) == Visibility::Public {
                    unsafe_fn.insert(def_id);
                    self.insert_uig(def_id, self.get_callees(def_id), self.get_cons(def_id));
                }
            }
            DefKind::Mod => {
                for child in tcx.module_children(def_id) {
                    if let Some(child_def_id) = child.res.opt_def_id() {
                        self.process_def_id(tcx, child_def_id, visited, unsafe_fn);
                    }
                }
            }
            DefKind::Impl { of_trait: _ } => {
                for item in tcx.associated_item_def_ids(def_id) {
                    self.process_def_id(tcx, *item, visited, unsafe_fn);
                }
            }
            DefKind::Struct => {
                let impls = tcx.inherent_impls(def_id);
                for impl_def_id in impls {
                    self.process_def_id(tcx, *impl_def_id, visited, unsafe_fn);
                }
            }
            DefKind::Ctor(_of, _kind) => {
                if tcx.is_mir_available(def_id) {
                    let _mir = tcx.optimized_mir(def_id);
                }
            }
            _ => {
                // println!("{:?}",tcx.def_kind(def_id));
            }
        }
    }

    pub fn filter_mir(def_id: DefId) -> bool {
        let def_id_fmt = format!("{:?}", def_id);
        def_id_fmt.contains("core_arch") || def_id_fmt.contains("::__")
    }

    pub fn insert_uig(
        &mut self,
        caller: DefId,
        callee_set: HashSet<DefId>,
        caller_cons: Vec<NodeType>,
    ) {
        let mut pairs = HashSet::new();
        for callee in &callee_set {
            let callee_cons = self.get_cons(*callee);
            pairs.insert((self.generate_node_ty(*callee), callee_cons));
        }
        let uig = UigUnit::new_by_pair(self.generate_node_ty(caller), caller_cons, pairs);
        if callee_set.len() > 0 {
            self.uigs.push(uig);
        } else {
            self.single.push(uig);
        }
    }

    pub fn get_cons(&self, def_id: DefId) -> Vec<NodeType> {
        let mut cons = Vec::new();
        if self.tcx.def_kind(def_id) == DefKind::Fn || self.get_type(def_id) == 0 {
            return cons;
        }
        let tcx = self.tcx;
        if let Some(assoc_item) = tcx.opt_associated_item(def_id) {
            if let Some(impl_id) = assoc_item.impl_container(tcx) {
                // get struct ty
                let ty = tcx.type_of(impl_id).skip_binder();
                if let Some(adt_def) = ty.ty_adt_def() {
                    let adt_def_id = adt_def.did();
                    let impls = tcx.inherent_impls(adt_def_id);
                    for impl_def_id in impls {
                        for item in tcx.associated_item_def_ids(impl_def_id) {
                            if (tcx.def_kind(item) == DefKind::Fn
                                || tcx.def_kind(item) == DefKind::AssocFn)
                                && self.get_type(*item) == 0
                            {
                                cons.push(self.generate_node_ty(*item));
                            }
                        }
                    }
                }
            }
        }
        cons
    }

    pub fn get_callees(&self, def_id: DefId) -> HashSet<DefId> {
        let mut callees = HashSet::new();
        let tcx = self.tcx;
        if tcx.is_mir_available(def_id) {
            let body = tcx.optimized_mir(def_id);
            for bb in body.basic_blocks.iter() {
                match &bb.terminator().kind {
                    TerminatorKind::Call { func, .. } => {
                        if let Operand::Constant(func_constant) = func {
                            if let ty::FnDef(ref callee_def_id, _) =
                                func_constant.const_.ty().kind()
                            {
                                if self.check_safety(*callee_def_id) {
                                    callees.insert(*callee_def_id);
                                }
                            }
                        }
                    }
                    _ => {}
                }
            }
        }
        return callees;
    }

    pub fn generate_node_ty(&self, def_id: DefId) -> NodeType {
        (def_id, self.check_safety(def_id), self.get_type(def_id))
    }

    pub fn print_hashset<T: std::fmt::Debug>(set: &HashSet<T>) {
        for item in set {
            println!("{:?}", item);
        }
        println!("---------------");
    }
}
