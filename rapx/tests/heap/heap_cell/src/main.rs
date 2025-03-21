#![feature(unique_rc_arc)]

fn main() {
    mod cell {
        use std::cell::{Cell, LazyCell, RefCell, UnsafeCell};
        fn t() {
            let _cell = Cell::new(1);
            let _unsafe_cell = UnsafeCell::new(1);
            let _ref_cell = RefCell::new(1);
            let _lazy_cell = LazyCell::new(|| 92);
        }
    }

    mod rc {
        use std::{rc::{Rc, UniqueRc, Weak as Weak1}, sync::{Arc, Weak as Weak2}};
        fn t() {
            let _rc = Rc::new(1);
            let _arc = Arc::new(1);
            let _unique_rc = UniqueRc::new(1);
            let _weak_rc:Weak1<i32> = Weak1::new();
            let _weak_arc:Weak2<i32>  = Weak2::new();
        }
    }
}