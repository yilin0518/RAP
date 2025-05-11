use rustc_middle::ty::{self};
use std::fmt::Display;

// static ALL_TRANSFORMKIND: OnceLock<Vec<TransformKind>> = OnceLock::new();

static ALL_TRANSFORMKIND: [TransformKind; 2] = [
    TransformKind::Ref(ty::Mutability::Not),
    TransformKind::Ref(ty::Mutability::Mut),
    // TransformKind::Deref,
    // TransformKind::Box,
];

#[derive(Clone, Copy, Eq, PartialEq, Debug)]
pub enum TransformKind {
    Ref(ty::Mutability),
    Deref,
    Box,
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
