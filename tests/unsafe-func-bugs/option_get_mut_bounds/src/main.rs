fn main() {
    let mut array: [u8; 5] = [1, 2, 3, 4, 5];
    let i = 5;
    let element = array.get_mut(i); // 检查是否越界
    match element {
        Some(value) => println!("valid_access: {}", value),
        None => println!("Index out of bounds"),
    }
}
