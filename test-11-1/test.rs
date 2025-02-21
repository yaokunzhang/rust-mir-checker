#[allow(unused_variables)]
fn test_pointer_operations_no_byte() {
    let arr: [i32; 5] = [10, 20, 30, 40, 50];
    let ptr = arr.as_ptr();

    unsafe {
        // 1.正确：`offset` 在范围内偏移
        let ptr1 = ptr.offset(2);
        println!("Value at offset 2: {}", *ptr1);

        // 2.不规范：`offset` 越界访问
        let ptr2 = ptr.offset(6); // 超出范围，未定义行为
        // println!("Value at offset 6: {}", *ptr2);
        
        // 3.正确：`wrapping_offset` 在范围内偏移
        let ptr3 = ptr.wrapping_offset(3);
        println!("Value at wrapping offset 3: {}", *ptr3);

        // 4.不规范：`wrapping_offset` 越界逻辑错误
        let ptr4 = ptr.wrapping_offset(-10); // 虽不会 panic，但逻辑上越界
        // println!("Value at wrapping offset -10: {}", *ptr4);

        // 5.正确：`offset_from` 计算两个指针间的偏移量
        let diff = ptr1.offset_from(ptr);
        println!("Offset from start to ptr1: {}", diff);

        // 6.不规范：`offset_from` 使用非同一块内存的指针
        let arr2 = [60, 70, 80];
        let ptr_other = arr2.as_ptr();
        let diff_invalid = ptr_other.offset_from(ptr); // 未定义行为
        println!("Invalid offset_from: {}", diff_invalid);

        // 7.正确：`add` 在范围内的偏移
        let ptr5 = ptr.add(4);
        println!("Value at add 4: {}", *ptr5);

        // 8.不规范：`add` 越界访问
        let ptr6 = ptr.add(10); // 超出范围，未定义行为
        // println!("Value at add 10: {}", *ptr6);

        // 9.正确：`wrapping_add` 在范围内操作
        let ptr7 = ptr.wrapping_add(2);
        println!("Value at wrapping add 2: {}", *ptr7);

        // 10.不规范：`wrapping_add` 虽不会 panic，但逻辑上越界
        let ptr8 = ptr.wrapping_add(50); // 超出范围，未定义行为
        // println!("Value at wrapping add 50: {}", *ptr8);

        // 11.正确：`wrapping_sub` 恰好返回起始指针
        let ptr9 = ptr.wrapping_add(3).wrapping_sub(3);
        println!("Value after wrapping sub: {}", *ptr9);

        // 12.不规范：`wrapping_sub` 逻辑错误
        let ptr10 = ptr.wrapping_sub(10); // 虽不会 panic，但超出数组起始范围
        // println!("Value after wrapping sub -10: {}", *ptr10);

        // 13.正确：连续操作
        let ptr11 = ptr.add(1).offset(1);
        println!("Value at add 1 and offset 1: {}", *ptr11);

        // 14.不规范：连续错误操作导致越界
        let ptr12 = ptr.add(3).offset(5); // 超出范围，未定义行为
        // println!("Value at add 3 and offset 5: {}", *ptr12);
    }
}

// offset_from
// byte_offset_from
// add
// byte_add
// sub
// wrapping_add
// wrapping_byte_add
// wrapping_sub
// wrapping_byte_sub
fn main() {
    // test_str_pointer_operations_no_byte();
    test_pointer_operations_no_byte();
    // test_pointer_operations_from_sources();
}