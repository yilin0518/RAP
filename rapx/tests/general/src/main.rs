use std::slice;
fn get_vec(p:&[u8]) -> Vec<u8>{
    p.iter().map(|x| x + 1).collect()
}

fn get_slice(v:&[u8], l:usize) -> &[u8]{
    let ptr = v.as_ptr();
    let len = v.len();
    if l < len {
        unsafe {slice::from_raw_parts(ptr, l)}
    } else {
        unsafe {slice::from_raw_parts(ptr, len)}
    } 
}

fn main() {
    let vec1 = vec![1;10];
    let _vec2 = get_vec(&vec1);
    let slice =get_slice(&vec1, 5);

    let len = slice.len();
    for i in 0..len {
        println!("slice[{}] = {}", i, slice[i]);
    }
}
