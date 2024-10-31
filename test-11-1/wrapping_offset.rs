fn main() {
    let mut x = [1, 2, 3, 4];
    let i = 3;
    let j = 5;
    unsafe {
        *x.as_mut_ptr().wrapping_offset(i) = 999;
        *x.as_mut_ptr().wrapping_offset(j) = 999;
    }
}