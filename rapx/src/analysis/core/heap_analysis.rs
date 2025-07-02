pub mod default;

use rustc_middle::ty::{Ty, TyKind};
use rustc_span::def_id::DefId;

use std::{
    collections::{HashMap, HashSet},
    env, fmt,
};

use crate::{rap_info, Analysis};

#[repr(u8)]
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub enum HeapInfo {
    False = 0,
    True = 1,
    Unknown = 2,
}

impl Default for HeapInfo {
    fn default() -> Self {
        Self::Unknown
    }
}

impl HeapInfo {
    pub fn is_onheap(&self) -> bool {
        match self {
            HeapInfo::True => true,
            _ => false,
        }
    }
}

impl fmt::Display for HeapInfo {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let name = match self {
            HeapInfo::False => "0",
            HeapInfo::True => "1",
            HeapInfo::Unknown => "2",
        };
        write!(f, "{}", name)
    }
}

/// This is the type for storing the heap analysis results.
/// The result is represented as a hashmap, where the key is `DefId` and the value contains the
/// information of whether the type contains data on heap.
/// Since a type may have multiple fields, the value is represented as a vec, indicating the heap
/// information of each field.
/// Also, because it may contain type parameters or generic types,
/// the heap information is a tuple containing the information of each type parameter.
pub type HAResult = HashMap<DefId, Vec<(HeapInfo, Vec<bool>)>>;

pub trait HeapAnalysis: Analysis {
    fn get_all_items(&mut self) -> HAResult;
    fn is_onheap<'tcx>(hares: HAResult, ty: Ty<'tcx>) -> Result<bool, &'static str> {
        match ty.kind() {
            TyKind::Adt(adtdef, ..) => {
                let ans = hares.get(&adtdef.0 .0.did).unwrap();
                if ans[0].0 == HeapInfo::True {
                    return Ok(true);
                }
                Ok(false)
            }
            _ => Err("The input is not an ADT"),
        }
    }
}
