fn main() {
    let mut array: [u8; 5] = [1, 2, 3, 4, 5];
    let p = array.as_mut_ptr();
    unsafe {
        // 从越界位置开始创建切片
        let slice = std::slice::from_raw_parts_mut(p.offset(5), 1);
        let _slice_access = slice[0]; // 可能会越界
        println!("slice_access: {}", _slice_access);
    }
}
