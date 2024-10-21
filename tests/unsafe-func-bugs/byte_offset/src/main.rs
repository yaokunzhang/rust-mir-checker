fn main() {
    let mut x = [1, 2, 3, 4, 5];
    
    unsafe {
        // 使用 byte_offset 进行溢出访问
        let out_of_bounds_ptr = x.as_mut_ptr().offset(3); // 偏移到超出边界的位置
        
        // 尝试写入超出边界的内存
        *out_of_bounds_ptr = 1; // 这里可能导致未定义行为
        
        // 尝试读取超出边界的内存
        let value = *out_of_bounds_ptr; // 这里也可能导致未定义行为
        println!("Value at out-of-bounds pointer: {}", value);
    }
}

