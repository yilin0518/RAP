#![feature(fn_traits)]

use std::alloc::{dealloc, Layout};
use std::mem::{ManuallyDrop, MaybeUninit};
use std::ptr::drop_in_place;

fn main() {
    unsafe {
        t1();
        t2();
        t3();
        t4();
        t5();
        t6();
        t7();
        t8();
        t9();
        t10();
        t11();
    }
}

fn t1() {
    let v = String::from("a");
    drop(v);
}

unsafe fn t2() {
    let v = Box::leak(Box::new(1));
    drop_in_place(v as *mut _);
}

unsafe fn t3() {
    let mut md = ManuallyDrop::new(Box::new(1));
    ManuallyDrop::drop(&mut md);
}

unsafe fn t5() {
    let mut x = MaybeUninit::<Option<Vec<u32>>>::uninit();
    x.write(Some(vec![0, 1, 2]));
    x.assume_init_drop();
}

unsafe fn t6() {
    let mut b = Box::new(1);
    let p = b.as_mut();
    dealloc(p, Layout::new::<i32>());
}

unsafe fn t7() {
    let x = 1i32;
    let mut c = || {
        x + 1;
    };
    c.call_mut(());
}

unsafe fn t8() {
    let mut b = Box::new(1);
    let p = b.as_mut() as *mut i32;
    p.copy_from_nonoverlapping(p, 0);
}

unsafe fn t9() {
    let mut b = Box::new(1);
    let p = b.as_mut() as *mut i32;
    p.copy_to_nonoverlapping(p, 0);
}

unsafe fn t10() {
    let mut b = Box::new(1);
    let p = b.as_mut() as *mut i32;
    p.copy_from(p, 0);
}

unsafe fn t11() {
    let mut b = Box::new(1);
    let p = b.as_mut() as *mut i32;
    p.copy_to(p, 0);
}

unsafe fn t12() {
    let mut b = Box::new(1);
    drop(b);
}

fn t4() {
    let b = Box::new(1).clone();
}
