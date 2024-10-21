fn main() {
    let array: [u8; 5] = [1, 2, 3, 4, 5];
    let p = array.as_ptr();
    unsafe {
        let ptr = p.offset(5) as *mut u8; // 不可变指针转可变指针
        let _ptr_access = *ptr; // 读取越界值
        println!("ptr_access: {}", _ptr_access);
    }
}
