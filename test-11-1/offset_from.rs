fn main() {
    let arr: [i32; 5] = [10, 20, 30, 40, 50];
    let ptr = arr.as_ptr();
    unsafe {
        // 不规范：`offset_from` 使用非同一块内存的指针
        let arr2 = [60, 70, 80];
        let ptr_other = ptr.offset(1);
        let diff_invalid = ptr_other.offset_from(ptr); // 未定义行为
        println!("Invalid offset_from: {}", diff_invalid);
    }
}
