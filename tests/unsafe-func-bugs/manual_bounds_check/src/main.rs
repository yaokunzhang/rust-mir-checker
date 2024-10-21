fn main() {
    let mut array: [u8; 5] = [1, 2, 3, 4, 5];
    let i = 5;
    let p = array.as_mut_ptr();
    if i < array.len() {
        let _valid_access = unsafe { *p.offset(i as isize) };
        println!("valid_access: {}", _valid_access);
    } else {
        println!("Index out of bounds");
    }
}
