fn main() {
    let mut array: [[u8; 2]; 2] = [[1, 2], [3, 4]];
    let p = array.as_mut_ptr();
    unsafe {
        let _out_of_bound_access = *p.offset(2); // 超出二维数组的边界
        println!("out_of_bound_access: {:?}", _out_of_bound_access);
    }
}
