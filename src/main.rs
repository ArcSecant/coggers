mod gen;
mod inference;
mod parse;
use crate::{gen::*, inference::*, parse::*};
use std::mem;

unsafe fn run_code<I>(ptr: *const u8, input: I) {
    let code_ptr = ptr;
    let code_fn = mem::transmute::<_, fn(I) -> i64>(code_ptr);
    println!("{:?}", code_fn(input))
}

fn main() {
    use Expr::*;
    // let f = "fn f x = if x == 5 then x - 5 else f (x - 1) ";
    // let f = "fn f x = if x == 5 then x - 5 else x - 1 ";
    let f = "fn f x = x + 5";
    println!("{:?}", f);

    let mut generator = Generator::default();
    let res = parser::function(&f);
    match res {
        Ok(v) => {
            println!("{:?}, {:?}, {:?}", v.0, v.1, v.2);
            let func = ELam(v.1.clone(), Box::new(v.2.clone()));
            let func = ELetRec(
                v.0.clone(),
                Box::new(func.clone()),
                Box::new(EVar(v.0.clone())),
            );
            println!("{:?}", func);
            let func_t = infer_type(&func);
            println!("{:?}: {:?}", v.0, func_t);

            let prototype = Prototype {
                function_name: v.0,
                parameters: vec![v.1.clone()],
            };

            let function = Function {
                prototype,
                body: v.2.clone(),
            };

            unsafe{ run_code(generator.function(function).unwrap(), 5) };
        }
        Err(e) => println!("error {:?}", e),
    };
}
