#[repr(C)]
struct MyStruct {
    a: i32,
    b: f64,
}

fn main() {
    let s = MyStruct { a: 42, b: 3.14 };
    let ptr: *const MyStruct = &s;

    unsafe {
        println!("{:?}", *(ptr as *const i32));
        // 使用 `offset` 进行指针偏移
        let a_ptr = ptr as *const u8;
        println!("Value of a: {}", *(a_ptr.offset(0) as *const i32)); // 偏移 0 字节，访问 `a`
    }
}


