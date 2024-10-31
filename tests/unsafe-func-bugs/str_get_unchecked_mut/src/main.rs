fn main() {
    let array = [10, 20, 30, 40, 50];

    unsafe {
        // let element1 = array.get_unchecked(0); // 获取第一个元素
        // let element2 = array.get_unchecked(2); // 获取第三个元素
        // let element3 = array.get_unchecked(4); // 获取第五个元素

        // 模拟一些不安全操作
        let out_of_bounds = array.get_unchecked(5); // 这里会导致 UB，但代码继续执行
        println!("Out of bounds access: {}", out_of_bounds); // 访问越界，不推荐这样使用

        // 为了演示，手动定义的内存地址
        let memory_address = &array[2] as *const i32;
        let element_from_ptr = *memory_address;

        println!("Element from pointer: {}", element_from_ptr); // 输出指向的元素
    }
}
