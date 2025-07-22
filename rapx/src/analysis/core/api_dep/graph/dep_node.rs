use std::hash::Hash;

use super::ty_wrapper::TyWrapper;
use rustc_middle::{
    query::IntoQueryParam,
    ty::{self, Ty, TyCtxt},
};

use rustc_hir::def_id::DefId;

#[derive(Clone, Copy, Eq, PartialEq, Hash, Debug)]
enum IntrinsicKind {
    Borrow,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum DepNode<'tcx> {
    Api(DefId, ty::GenericArgsRef<'tcx>),
    Ty(TyWrapper<'tcx>),
    GenericParamDef(DefId, usize, String, bool), // (fn_def_id, index, symbol, is_lifetime_param)
}

pub fn desc_str<'tcx>(node: DepNode<'tcx>, tcx: TyCtxt<'tcx>) -> String {
    match node {
        DepNode::Api(def_id, args) => tcx.def_path_str_with_args(def_id, args),
        DepNode::Ty(ty) => ty.desc_str(tcx),
        DepNode::GenericParamDef(idx, index, sym, is_lifetime) => {
            format!("{sym}/#{index}")
        }
    }
}

impl<'tcx> DepNode<'tcx> {
    pub fn api(id: impl IntoQueryParam<DefId>, args: ty::GenericArgsRef<'tcx>) -> DepNode<'tcx> {
        DepNode::Api(id.into_query_param(), args)
    }
    pub fn ty(ty: Ty<'tcx>) -> DepNode<'tcx> {
        DepNode::Ty(TyWrapper::from(ty))
    }
    pub fn generic_param_def(
        fn_def_id: DefId,
        index: usize,
        name: impl ToString,
        is_lifetime: bool,
    ) -> DepNode<'tcx> {
        DepNode::GenericParamDef(fn_def_id, index, name.to_string(), is_lifetime)
    }
    pub fn is_ty(&self) -> bool {
        matches!(self, DepNode::Ty(_))
    }
    pub fn is_api(&self) -> bool {
        matches!(self, DepNode::Api(..))
    }
    pub fn is_generic(&self) -> bool {
        matches!(self, DepNode::GenericParamDef(..))
    }

    pub fn as_ty(&self) -> TyWrapper<'tcx> {
        match self {
            DepNode::Ty(ty) => *ty,
            _ => {
                panic!("{self:?} is not a ty")
            }
        }
    }

    pub fn as_api(&self) -> (DefId, ty::GenericArgsRef<'tcx>) {
        match self {
            DepNode::Api(did, args) => (*did, args),
            _ => {
                panic!("{self:?} is not a ty")
            }
        }
    }
}
