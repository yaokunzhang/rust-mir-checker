fn main() {
    let mut array: [u8; 5] = [1, 2, 3, 4, 5];
    let i = 5;
    unsafe {
        let _unchecked_access = *array.get_unchecked_mut(i); // 越界访问
        println!("unchecked_access: {}", _unchecked_access);
    }
}
