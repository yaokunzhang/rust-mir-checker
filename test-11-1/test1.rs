fn main() {
    let mut x = [1, 2, 3, 4];
    let i = 5;
    unsafe {
        // 在unsafe块中，可以对数组的元素进行越界修改
        *x.as_mut_ptr().offset(i) = i;
    }
}