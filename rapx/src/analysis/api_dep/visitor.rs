use std::io::Write;

use crate::rap_debug;

use super::graph::ApiDepGraph;
use super::graph::DepNode;
use petgraph::graph::NodeIndex;
use rustc_hir::{
    def_id::{DefId, LocalDefId},
    intravisit::{self, FnKind, Visitor},
    BodyId, FnDecl,
};
use rustc_middle::ty::{self, Ty, TyCtxt};
use rustc_span::Span;

pub struct FnVisitor<'tcx, 'a> {
    fn_cnt: usize,
    tcx: TyCtxt<'tcx>,
    funcs: Vec<DefId>,
    graph: &'a mut ApiDepGraph<'tcx>,
}

impl<'tcx, 'a> FnVisitor<'tcx, 'a> {
    pub fn new(tcx: TyCtxt<'tcx>, graph: &'a mut ApiDepGraph<'tcx>) -> FnVisitor<'tcx, 'a> {
        let fn_cnt = 0;
        let funcs = Vec::new();
        FnVisitor {
            fn_cnt,
            tcx,
            graph,
            funcs,
        }
    }
    pub fn fn_cnt(&self) -> usize {
        self.fn_cnt
    }
    pub fn write_funcs<T: Write>(&self, F: &mut T) {
        for id in &self.funcs {
            write!(F, "{}\n", self.tcx.def_path_str(id)).expect("fail when write funcs");
        }
    }
    pub fn add_func(&mut self, id: LocalDefId) {
        let fn_def_id = id.to_def_id();

        self.fn_cnt += 1;
        self.funcs.push(fn_def_id);
        let api_node = self.graph.get_node(DepNode::api(id));

        let early_fn_sig = self.tcx.fn_sig(fn_def_id);
        rap_debug!("fn_sig: {:?}", early_fn_sig);
        let binder_fn_sig = early_fn_sig.instantiate_identity();
        // use no_bound_vars or instantiate_bound_regions
        // let vars = binder_fn_sig.bound_vars();
        // rap_debug!("bound_vars: {:?}", vars);
        // TODO: Replace skip_binder
        // use no_bound_vars or instantiate_bound_regions
        // let fn_sig = binder_fn_sig.skip_binder();
        let fn_sig = self
            .tcx
            .liberate_late_bound_regions(fn_def_id, binder_fn_sig);

        for input_ty in fn_sig.inputs().iter() {
            let input_node = self.graph.get_node(DepNode::ty(*input_ty));
            self.bind_lifetime(*input_ty, 0, input_node);
            self.graph.add_edge(input_node, api_node);
        }

        let output_ty = fn_sig.output();
        let output_node = self.graph.get_node(DepNode::ty(output_ty));
        self.bind_lifetime(output_ty, 0, output_node);
        self.graph.add_edge(api_node, output_node);
    }

    pub fn bind_lifetime(&mut self, ty: Ty<'tcx>, no: usize, src_node: NodeIndex) {
        let kind = ty.kind();
        match kind {
            ty::TyKind::Ref(region, inner_ty, _) => {
                rap_debug!(
                    "Region, Ref: {:?}, {:?}",
                    get_region_kind_variant(*region),
                    inner_ty
                );
                let node_index = self.graph.get_node(DepNode::region(ty, no));
                self.graph.add_edge(src_node, node_index);
                self.bind_lifetime(*inner_ty, no + 1, src_node);
            }
            ty::TyKind::Adt(adt_def, generic_args) => {
                for region in generic_args.regions() {
                    rap_debug!("Region: {}", get_region_kind_variant(region));
                    let node_index = self.graph.get_node(DepNode::region(ty, no));
                    self.graph.add_edge(src_node, node_index);
                }
                // TODO: handle adt_def
            }
            ty::TyKind::Array(ty, _) | ty::TyKind::Slice(ty) => {
                self.bind_lifetime(*ty, no + 1, src_node);
            }
            _ => {}
        }
    }
}

// print variant information for ty::RegionKind
fn get_region_kind_variant(region: ty::Region) -> &'static str {
    match region.kind() {
        ty::RegionKind::ReEarlyParam(_) => "ReEarlyParam",
        ty::RegionKind::ReBound(debruijn_index, _) => "ReBound",
        ty::RegionKind::ReLateParam(_) => "ReLateParam",
        ty::RegionKind::ReStatic => "ReStatic",
        ty::RegionKind::ReVar(region_vid) => "ReVar",
        ty::RegionKind::RePlaceholder(_) => "Replaceholder",
        ty::RegionKind::ReErased => "ReErased",
        ty::RegionKind::ReError(_) => "ReError",
    }
}

impl<'tcx, 'a> Visitor<'tcx> for FnVisitor<'tcx, 'a> {
    fn visit_fn<'v>(
        &mut self,
        fk: FnKind<'v>,
        fd: &'v FnDecl<'v>,
        b: BodyId,
        span: Span,
        id: LocalDefId,
    ) -> Self::Result {
        self.add_func(id);
    }
}
