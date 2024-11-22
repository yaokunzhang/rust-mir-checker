fn main() {
    let mut a = [10, 20, 30, 40, 50];
    unsafe {
        let ptr1 = a.as_mut_ptr();
        let ptr2 = ptr1.add(3);
        // 正确的操作
        let valid_ptr = ptr1.add(2); // 应该指向 a[3]

        // 越界操作
        let out_of_bounds_ptr = ptr1.add(5); // 越界，指向无效内存

        // 错误的 offset 操作
        let invalid_offset = ptr2.offset(-4); // 越界，指向无效内存

        // 输出操作结果（用于验证分析工具的行为）
        println!("Valid pointer: {:?}", valid_ptr);
        println!("Out of bounds pointer: {:?}", out_of_bounds_ptr);
        println!("Invalid offset pointer: {:?}", invalid_offset);
    }
}
