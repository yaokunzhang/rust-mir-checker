fn main() {
    let mut array: [u8; 5] = [1, 2, 3, 4, 5];
    let p = array.as_mut_ptr();
    // 越界访问
    let _out_of_bound_access = unsafe { *p.offset(5) };
    println!("out_of_bound_access: {}", _out_of_bound_access);
}
