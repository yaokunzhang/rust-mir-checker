macro_rules! safe_offset {
    ($arr:expr, $i:expr) => {{
        if $i < $arr.len() {
            unsafe {
                *$arr.as_mut_ptr().offset($i as isize)
            }
        } else {
            panic!("Index out of bounds");
        }
    }};
}

fn main() {
    let mut array: [u8; 5] = [1, 2, 3, 4, 5];
    let i = 5;
    let _safe_access = safe_offset!(array, i); // 会触发 panic
}
