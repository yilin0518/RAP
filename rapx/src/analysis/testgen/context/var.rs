use rustc_middle::ty;
use std::fmt::{self, Display};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum VarState {
    Live,
    Moved,
    Borrowed(ty::Mutability),
    Dropped,
}

impl VarState {
    pub fn is_dropped(&self) -> bool {
        matches!(self, VarState::Dropped)
    }

    pub fn is_dead(&self) -> bool {
        matches!(self, VarState::Dropped | VarState::Moved)
    }

    pub fn borrowed() -> Self {
        VarState::Borrowed(ty::Mutability::Not)
    }

    pub fn borrowed_mut() -> Self {
        VarState::Borrowed(ty::Mutability::Mut)
    }
}

impl Display for VarState {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            VarState::Live => write!(f, "Live"),
            VarState::Moved => write!(f, "Moved"),
            VarState::Borrowed(ty::Mutability::Not) => write!(f, "Borrowed"),
            VarState::Borrowed(ty::Mutability::Mut) => write!(f, "BorrowedMut"),
            VarState::Dropped => write!(f, "Dropped"),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Var(pub usize, pub bool); // bool is true if the var is an input var

impl Display for Var {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "v{}", self.0)
    }
}

impl Var {
    pub fn unique_id(&self) -> usize {
        self.0
    }
    pub fn is_from_input(&self) -> bool {
        self.1
    }
}

pub static DUMMY_INPUT_VAR: Var = Var(0, true);
pub static DUMMY_UNIT_VAR: Var = Var(0, false); // unused now
