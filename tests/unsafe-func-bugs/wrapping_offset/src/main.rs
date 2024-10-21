fn main() {
    let mut x = [1, 2, 3, 4, 5];
    unsafe {
        *x.as_mut_ptr().offset(3) = 6;
    }
}