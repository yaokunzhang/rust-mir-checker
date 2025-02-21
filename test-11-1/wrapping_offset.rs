trait Number {
    fn get(&self) -> i32;
}

struct One;

impl Number for One {
    fn get(&self) -> i32 {
        1
    }
}

struct Two;

impl Number for Two {
    fn get(&self) -> i32 {
        2
    }
}

fn main() {
    let n1: Box<dyn Number> = Box::new(One); // o1
    let n2: Box<dyn Number> = Box::new(Two); // o2

    let x = id(&n1);
    let y = id(&n2);

    let i = x.get();
    println!("Value of i: {}", i);
}

fn id(n: &Box<dyn Number>) -> &dyn Number {
    n.as_ref()
}
