use std::{mem::ManuallyDrop, slice};

// 1. There is dataflow between the argument p and the return value, but not alias.
fn get_vec(p:&[u8]) -> Vec<u8>{
    p.iter().map(|x| x + 1).collect()
}

// 2. The first arguments v and the return value are aliases.
fn get_slice(v:&[u8], l:usize) -> &[u8]{
    let ptr = v.as_ptr();
    let len = v.len();
    if l < len {
        // 3. This branch is executed with the precondition l < len.
        unsafe {slice::from_raw_parts(ptr, l)}
    } else {
        unsafe {slice::from_raw_parts(ptr, len)}
    } 
}

fn main() {
    let vec1 = vec![1;10];
    let _slice = get_slice(&vec1, 5);
    // 4. vec2 is a heap owner, so _mdvec is a heap owner => memory leakage.
    let vec2 = get_vec(&vec1);
    let _mdvec = ManuallyDrop::new(vec2);
}
