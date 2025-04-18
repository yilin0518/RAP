use rustc_middle::ty::{self, Mutability, Ty};
use std::{fmt::Display, sync::OnceLock};

// static ALL_TRANSFORMKIND: OnceLock<Vec<TransformKind>> = OnceLock::new();

static ALL_TRANSFORMKIND: [TransformKind; 2] = [
    TransformKind::Ref(Mutability::Not),
    TransformKind::Ref(Mutability::Mut),
    // TransformKind::Deref,
    // TransformKind::Box,
];

#[derive(Clone, Copy, Eq, PartialEq, Debug)]
pub enum TransformKind {
    Ref(ty::Mutability),
    Deref,
    Box,
}

#[derive(Clone, Copy, Eq, PartialEq, Debug)]
pub enum DepEdge {
    Arg(usize),
    Ret,
    Fn2Generic,
    Transform(TransformKind),
}

impl TransformKind {
    pub fn all() -> &'static [TransformKind] {
        &ALL_TRANSFORMKIND
    }
}

impl Display for TransformKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TransformKind::Ref(mutability) => write!(f, "{}T", mutability.ref_prefix_str()),
            TransformKind::Deref => write!(f, "Deref"),
            TransformKind::Box => write!(f, "Box"),
        }
    }
}

impl Display for DepEdge {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DepEdge::Arg(no) => write!(f, "{}", no),
            DepEdge::Ret => write!(f, "r"),
            DepEdge::Fn2Generic => write!(f, ""),
            DepEdge::Transform(kind) => write!(f, "Transform({})", kind),
        }
    }
}

impl DepEdge {
    pub fn arg(no: usize) -> DepEdge {
        DepEdge::Arg(no)
    }
    pub fn ret() -> DepEdge {
        DepEdge::Ret
    }
    pub fn fn2generic() -> DepEdge {
        DepEdge::Fn2Generic
    }
    pub fn transform(kind: TransformKind) -> DepEdge {
        DepEdge::Transform(kind)
    }
}
