fn main() {
    let mut array = [10, 20, 30, 40, 50];

    unsafe {
        let out_of_bounds_index = 5; // 越界索引
        let out_of_bounds_index2 = 4; // 非越界索引
        let out_of_bounds_ptr = array.get_unchecked_mut(out_of_bounds_index); // 取消注释将导致未定义行为

        *out_of_bounds_ptr = 30;
        let out_of_bounds_ptr2= array.get_unchecked_mut(out_of_bounds_index2); // 取消注释将导致未定义行为

        *out_of_bounds_ptr2 = 40;
    }
}
