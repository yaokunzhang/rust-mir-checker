struct Buffer {
    data: [i32; 10], // 使用固定大小的数组
}

impl Buffer {
    // 创建并初始化缓冲区
    fn new() -> Self {
        let mut buffer = Buffer {
            data: [0; 10], // 初始化数组为零
        };
        buffer
    }

    // 不做边界检查的写入操作
    fn unsafe_fill(&mut self, index: isize, value: i32) {
        unsafe {
            // 直接写入指定索引
            *self.data.as_mut_ptr().offset(index) = value; // 直接写入
        }
    }

    // 带边界检查的写入操作
    fn safe_fill(&mut self, index: isize, value: i32) {
        unsafe {
            // 检查越界
            if index >= 0 && index < 10 as isize {
                *self.data.as_mut_ptr().offset(index) = value; // 直接写入
            }
        }
    }
}

fn main() {
    // 实例化 Buffer
    let mut buffer = Buffer::new();

    // 调用不安全的填充操作，可能会越界
    buffer.unsafe_fill(11, 100); // 从索引11写入100
    buffer.unsafe_fill(8, 100);

    buffer.safe_fill(11, 200); // 从索引11写入200

}
