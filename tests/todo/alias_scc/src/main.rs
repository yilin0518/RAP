enum Selector {
    First,
    Second,
}

//Expected alias analysis result: (1,0)
fn foo<'a>(x: &'a i32, y: &'a i32, choice: Selector) -> &'a i32 {
    let mut r = x;
    for _i in 0..100 {
        let a = match choice {
            Selector::First => x,
            Selector::Second => y,
        };
        r = match choice {
            Selector::First => a,
            Selector::Second => x,
        };
    }
    return r;
}

fn main() {
    let a = Box::new(10);
    let b = Box::new(20);
    let _result = foo(&a, &b, Selector::First);
}
