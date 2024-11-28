// #[allow(unused_variables)]
// fn test_str_pointer_operations_no_byte() {
//     let s: &str = "Hello, world!";
//     let ptr = s.as_ptr();

//     unsafe {
//         // 正确：`offset` 在范围内偏移
//         let ptr1 = ptr.offset(7); // 偏移到 "world!" 的开头
//         println!("Value at offset 7: {}", *ptr1 as char);

//         // 不规范：`offset` 越界访问
//         let ptr2 = ptr.offset(20); // 超出范围，未定义行为
//         // println!("Value at offset 20: {}", *ptr2 as char);

//         // 正确：`wrapping_offset` 在范围内偏移
//         let ptr3 = ptr.wrapping_offset(5); // 偏移到 "world"
//         println!("Value at wrapping offset 5: {}", *ptr3 as char);

//         // 不规范：`wrapping_offset` 越界逻辑错误
//         let ptr4 = ptr.wrapping_offset(-10); // 虽不会 panic，但逻辑上越界
//         // println!("Value at wrapping offset -10: {}", *ptr4 as char);

//         // 正确：`offset_from` 计算两个指针间的偏移量
//         let diff = ptr1.offset_from(ptr);
//         println!("Offset from start to ptr1: {}", diff);

//         // 不规范：`offset_from` 使用非同一块内存的指针
//         let s2 = "Another string";
//         let ptr_other = s2.as_ptr();
//         let diff_invalid = ptr_other.offset_from(ptr); // 未定义行为
//         // println!("Invalid offset_from: {}", diff_invalid);

//         // 正确：`add` 在范围内的偏移
//         let ptr5 = ptr.add(6); // 偏移到 "world"
//         println!("Value at add 6: {}", *ptr5 as char);

//         // 不规范：`add` 越界访问
//         let ptr6 = ptr.add(20); // 超出范围，未定义行为
//         // println!("Value at add 20: {}", *ptr6 as char);

//         // 正确：`wrapping_add` 在范围内操作
//         let ptr7 = ptr.wrapping_add(3); // 偏移到 "lo,"
//         println!("Value at wrapping add 3: {}", *ptr7 as char);

//         // 不规范：`wrapping_add` 虽不会 panic，但逻辑上越界
//         let ptr8 = ptr.wrapping_add(50); // 超出范围，未定义行为
//         // println!("Value at wrapping add 50: {}", *ptr8 as char);

//         // 正确：`wrapping_sub` 恰好返回起始指针
//         let ptr9 = ptr.wrapping_add(6).wrapping_sub(6);
//         println!("Value after wrapping sub: {}", *ptr9 as char);

//         // 不规范：`wrapping_sub` 逻辑错误
//         let ptr10 = ptr.wrapping_sub(10); // 虽不会 panic，但超出字符串起始范围
//         // println!("Value after wrapping sub -10: {}", *ptr10 as char);

//         // 正确：连续操作
//         let ptr11 = ptr.add(1).offset(2); // 从 "H" 向后偏移到 "l"
//         println!("Value at add 1 and offset 2: {}", *ptr11 as char);

//         // 不规范：连续错误操作导致越界
//         let ptr12 = ptr.add(5).offset(7); // 超出范围，未定义行为
//         // println!("Value at add 5 and offset 7: {}", *ptr12 as char);
//     }
// }

#[allow(unused_variables)]
fn test_pointer_operations_no_byte() {
    let arr: [i32; 5] = [10, 20, 30, 40, 50];
    let ptr = arr.as_ptr();

    unsafe {
        // 正确：`offset` 在范围内偏移
        let ptr1 = ptr.offset(2);
        println!("Value at offset 2: {}", *ptr1);

        // 不规范：`offset` 越界访问
        let ptr2 = ptr.offset(6); // 超出范围，未定义行为
        // println!("Value at offset 6: {}", *ptr2);
        
        // 正确：`wrapping_offset` 在范围内偏移
        let ptr3 = ptr.wrapping_offset(3);
        println!("Value at wrapping offset 3: {}", *ptr3);

        // 不规范：`wrapping_offset` 越界逻辑错误
        let ptr4 = ptr.wrapping_offset(-10); // 虽不会 panic，但逻辑上越界
        // println!("Value at wrapping offset -10: {}", *ptr4);

        // 正确：`offset_from` 计算两个指针间的偏移量
        let diff = ptr1.offset_from(ptr);
        println!("Offset from start to ptr1: {}", diff);

        // 不规范：`offset_from` 使用非同一块内存的指针
        let arr2 = [60, 70, 80];
        let ptr_other = arr2.as_ptr();
        let diff_invalid = ptr_other.offset_from(ptr); // 未定义行为
        println!("Invalid offset_from: {}", diff_invalid);

        // 正确：`add` 在范围内的偏移
        let ptr5 = ptr.add(4);
        println!("Value at add 4: {}", *ptr5);

        // 不规范：`add` 越界访问
        let ptr6 = ptr.add(10); // 超出范围，未定义行为
        // println!("Value at add 10: {}", *ptr6);

        // 正确：`wrapping_add` 在范围内操作
        let ptr7 = ptr.wrapping_add(2);
        println!("Value at wrapping add 2: {}", *ptr7);

        // 不规范：`wrapping_add` 虽不会 panic，但逻辑上越界
        let ptr8 = ptr.wrapping_add(50); // 超出范围，未定义行为
        // println!("Value at wrapping add 50: {}", *ptr8);

        // 正确：`wrapping_sub` 恰好返回起始指针
        let ptr9 = ptr.wrapping_add(3).wrapping_sub(3);
        println!("Value after wrapping sub: {}", *ptr9);

        // 不规范：`wrapping_sub` 逻辑错误
        let ptr10 = ptr.wrapping_sub(10); // 虽不会 panic，但超出数组起始范围
        // println!("Value after wrapping sub -10: {}", *ptr10);

        // 正确：连续操作
        let ptr11 = ptr.add(1).offset(1);
        println!("Value at add 1 and offset 1: {}", *ptr11);

        // 不规范：连续错误操作导致越界
        let ptr12 = ptr.add(3).offset(5); // 超出范围，未定义行为
        // println!("Value at add 3 and offset 5: {}", *ptr12);
    }
}

#[allow(unused_variables)]
fn test_pointer_operations_from_sources() {
    use std::alloc::{alloc, dealloc, Layout};

    // 栈分配数组
    let stack_array: [i32; 5] = [10, 20, 30, 40, 50];
    let stack_ptr = stack_array.as_ptr();

    // 堆分配数组
    let layout = Layout::array::<i32>(5).unwrap();
    let heap_ptr = unsafe { alloc(layout) as *mut i32 };
    unsafe {
        for i in 0..5 {
            *heap_ptr.add(i) = ((i + 1) * 10) as i32;
        }
    }

    // 静态分配内存
    static STATIC_ARRAY: [i32; 5] = [100, 200, 300, 400, 500];
    let static_ptr = STATIC_ARRAY.as_ptr();

    unsafe {
        // 栈指针操作
        println!("Testing stack pointer...");
        let stack_ptr_valid = stack_ptr.add(3);
        assert_eq!(*stack_ptr_valid, 40, "Stack pointer offset 3 failed");
        println!("Value at stack pointer offset 3: {}", *stack_ptr_valid);

        // 栈指针越界操作
        let stack_ptr_out_of_bounds = stack_ptr.add(10);
        if stack_ptr_out_of_bounds >= stack_ptr.add(stack_array.len()) {
            println!("Error: Stack pointer out of bounds at offset 10");
        }

        // 堆指针操作
        println!("\nTesting heap pointer...");
        let heap_ptr_valid = heap_ptr.add(2);
        assert_eq!(*heap_ptr_valid, 30, "Heap pointer offset 2 failed");
        println!("Value at heap pointer offset 2: {}", *heap_ptr_valid);

        // 堆指针越界操作
        let heap_ptr_out_of_bounds = heap_ptr.add(6);
        if heap_ptr_out_of_bounds >= heap_ptr.add(5) {
            println!("Error: Heap pointer out of bounds at offset 6");
        }

        // 静态指针操作
        println!("\nTesting static pointer...");
        let static_ptr_valid = static_ptr.offset(1);
        assert_eq!(*static_ptr_valid, 200, "Static pointer offset 1 failed");
        println!("Value at static pointer offset 1: {}", *static_ptr_valid);

        // 静态指针越界操作
        let static_ptr_out_of_bounds = static_ptr.offset(10);
        if static_ptr_out_of_bounds >= static_ptr.add(STATIC_ARRAY.len()) {
            println!("Error: Static pointer out of bounds at offset 10");
        }

        // 综合逻辑验证：从堆指针到静态指针的无效操作
        let invalid_offset = heap_ptr.offset_from(static_ptr);
        println!(
            "\nInvalid offset between heap pointer and static pointer: {} (undefined behavior)",
            invalid_offset
        );

        // 综合逻辑验证：对栈和堆指针混合操作
        let combined_ptr = stack_ptr.add(2).wrapping_offset(2);
        if combined_ptr == heap_ptr {
            println!(
                "Warning: Combined pointer operation accidentally matches heap pointer address"
            );
        } else {
            println!("Combined pointer operation is valid and distinct");
        }
    }

    // 释放堆内存
    unsafe {
        dealloc(heap_ptr as *mut u8, layout);
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