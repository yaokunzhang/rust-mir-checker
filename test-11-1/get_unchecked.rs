fn main() {
    let array = [10, 20, 30, 40, 50];

    unsafe {
        // 模拟一些不安全操作
        let out_of_bounds = array.get_unchecked(5); // 这里会导致 UB，但代码继续执行
        println!("Out of bounds access: {}", out_of_bounds); // 访问越界，不推荐这样使用
    }
}
