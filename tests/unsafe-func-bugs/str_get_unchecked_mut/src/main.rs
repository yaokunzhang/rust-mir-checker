fn main() {
    let mut my_string = String::from("Hello, Rust!");

    unsafe {
        let byte = my_string.as_mut_vec().get_unchecked_mut(7); // 获取索引 7 处的可变字节
        *byte = b'r'; // 修改字符为 'r'
    }

    println!("Modified string: {}", my_string);
}
