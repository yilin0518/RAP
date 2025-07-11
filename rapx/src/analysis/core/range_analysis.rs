#![allow(non_snake_case)]
#![allow(unused_variables)]
#![allow(dead_code)]
pub mod default;
pub mod domain;
use crate::analysis::{
    core::range_analysis::domain::domain::{ConstConvert, IntervalArithmetic},
    Analysis,
};
use intervals::Closed;
use once_cell::sync::Lazy;

use rustc_data_structures::fx::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_middle::mir::{BinOp, Place};

use std;
use std::{
    collections::HashMap,
    fmt::{self, Debug, Display},
};

pub type RAResult<'tcx, T> = HashMap<Place<'tcx>, Range<T>>;
pub type RAResultMap<'tcx, T> = FxHashMap<DefId, HashMap<Place<'tcx>, Range<T>>>;
pub type PathConstraint<'tcx> = HashMap<Vec<usize>, Vec<(Place<'tcx>, Place<'tcx>, BinOp)>>;
pub type PathConstraintMap<'tcx> =
    FxHashMap<DefId, HashMap<Vec<usize>, Vec<(Place<'tcx>, Place<'tcx>, BinOp)>>>;
pub struct RAResultWrapper<'tcx, T: Clone + PartialOrd>(pub RAResult<'tcx, T>);
pub struct RAResultMapWrapper<'tcx, T: Clone + PartialOrd>(pub RAResultMap<'tcx, T>);
pub struct PathConstraintWrapper<'tcx>(pub PathConstraint<'tcx>);
pub struct PathConstraintMapWrapper<'tcx>(pub PathConstraintMap<'tcx>);

/// This is the trait for range analysis. Range analysis is used to determine the value range of a
/// given variable at particular program points.
pub trait RangeAnalysis<'tcx, T: IntervalArithmetic + ConstConvert + Debug>: Analysis {
    /// Returns the range information for all local variables (Places) in a given function.
    ///
    /// Parameters:
    /// - def_id: The function's unique identifier (DefId)
    ///
    /// Returns:
    /// - A HashMap mapping each Place (variable) in the function to its inferred Range<T>.
    fn get_fn_range(&self, def_id: DefId) -> Option<RAResult<'tcx, T>>;

    /// Returns the complete mapping of range information for all functions in the crate.
    ///
    /// Returns:
    /// - A map from DefId (function) to a HashMap of Places and their corresponding ranges.
    fn get_all_fn_ranges(&self) -> RAResultMap<'tcx, T>;

    /// Returns the range for a specific local variable in a specific function.
    ///
    /// Parameters:
    /// - def_id: The function's identifier
    /// - local: The target Place (local variable) within the function
    ///
    /// Returns:
    /// - The inferred Range<T> if available, otherwise None.
    fn get_fn_local_range(&self, def_id: DefId, local: Place<'tcx>) -> Option<Range<T>>;

    /// Returns:
    /// - A mapping from paths (as sequences of basic block indices) to their corresponding
    ///   control-flow constraints expressed as (Place, Place, BinOp).
    ///
    /// This supports path-sensitive pruning by allowing reasoning over feasible paths.

    fn get_fn_path_constraints(&self, def_id: DefId) -> Option<PathConstraint<'tcx>>;

    fn get_all_path_constraints(&self) -> PathConstraintMap<'tcx>;
}

impl<'tcx, T> Display for RAResultWrapper<'tcx, T>
where
    Place<'tcx>: Debug,
    T: IntervalArithmetic + Clone + PartialOrd + Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (place, range) in &self.0 {
            writeln!(f, "{:?} => {}", place, range)?;
        }
        Ok(())
    }
}
impl<'tcx, T> Display for RAResultMapWrapper<'tcx, T>
where
    DefId: Debug,
    Place<'tcx>: Debug,
    T: IntervalArithmetic + Clone + PartialOrd + Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (def_id, ra_result) in &self.0 {
            writeln!(f, "DefId: {:?} =>", def_id)?;
            for (place, range) in ra_result {
                writeln!(f, "  {:?} => {}", place, range)?;
            }
        }
        Ok(())
    }
}

impl<'tcx> Display for PathConstraintWrapper<'tcx>
where
    Place<'tcx>: Debug,
    BinOp: Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (path, constraints) in &self.0 {
            writeln!(f, "Path {:?}:", path)?;
            for (p1, p2, op) in constraints {
                writeln!(f, "    Constraint:{:?} {:?} {:?}", p1, op, p2)?;
            }
        }
        Ok(())
    }
}

impl<'tcx> Display for PathConstraintMapWrapper<'tcx>
where
    DefId: Debug,
    Place<'tcx>: Debug,
    BinOp: Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (def_id, pc) in &self.0 {
            writeln!(f, "DefId {:?}:", def_id)?;
            for (path, constraints) in pc {
                writeln!(f, "  Path {:?}:", path)?;
                for (p1, p2, op) in constraints {
                    writeln!(f, "    Constraint:{:?} {:?} {:?}", p1, op, p2)?;
                }
            }
        }
        Ok(())
    }
}
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum RangeType {
    Unknown,
    Regular,
    Empty,
}
impl fmt::Display for RangeType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            RangeType::Unknown => "Unknown",
            RangeType::Regular => "Regular",
            RangeType::Empty => "Empty",
        };
        write!(f, "{}", s)
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct Range<T>
where
    T: PartialOrd + Clone,
{
    pub rtype: RangeType,
    pub range: Closed<T>,
}

static STR_MIN: Lazy<String> = Lazy::new(|| "Min".to_string());
static STR_MAX: Lazy<String> = Lazy::new(|| "Max".to_string());

impl<T> Display for Range<T>
where
    T: IntervalArithmetic,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let lower = if self.range.left.0 == T::min_value() {
            &*STR_MIN
        } else if self.range.left.0 == T::max_value() {
            &*STR_MAX
        } else {
            return write!(
                f,
                "{} [{}, {}]",
                self.rtype, self.range.left.0, self.range.right.0
            );
        };

        let upper = if self.range.right.0 == T::min_value() {
            &*STR_MIN
        } else if self.range.right.0 == T::max_value() {
            &*STR_MAX
        } else {
            return write!(
                f,
                "{} [{}, {}]",
                self.rtype, self.range.left.0, self.range.right.0
            );
        };
        write!(f, "{} [{}, {}]", self.rtype, lower, upper)
    }
}
