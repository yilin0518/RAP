use std::{mem::ManuallyDrop, slice};

// 1. Dataflow: p => ret value.
fn get_new_vec(p:&[u8]) -> Vec<u8>{
    p.iter().map(|x| x + 1).collect()
}

// 2. Dataflow: v => ret value.
// 3. Alias: (v, ret value) 
unsafe fn get_vec(v:&mut [u8]) -> Vec<u8>{
    let ptr = v.as_mut_ptr();
    let len = v.len();
    unsafe {Vec::from_raw_parts(ptr, len, len)}
}

// 6. Is the interior unsafe function sound?
fn get_slice<T>(v:&[T], l:usize) -> &[u8]{
    let ptr = v.as_ptr() as *const u8;
    let len = v.len();
    if l < len {
        // 7. This branch is executed with the precondition l < len.
        unsafe {slice::from_raw_parts(ptr, l)}
    } else {
        unsafe {slice::from_raw_parts(ptr, len)}
    } 
}


fn main() {
    let mut vec1 = vec![1;10];

    // 4. vec1 has two owners => double free 
    let _vec2 = unsafe { get_vec(&mut vec1) };

    // 5. vec2 is a heap owner, so _mdvec is a heap owner => memory leakage.
    let vec2 = get_new_vec(&vec1);
    let _mdvec = ManuallyDrop::new(vec2);

    // 8. Crate a Vec<u32> to trigger out-of-bound access.
    let vec3 = vec![1u32;10];
    let _slice = get_slice(&vec3, 5);

}
