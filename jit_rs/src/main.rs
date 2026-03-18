#![allow(dead_code, unused_imports)]

use crate::{codegen::compile, executor::execute};

mod lexer;
mod parser;
mod interpreter;
mod codegen;
mod executor;

fn main() {
    // compile "2 + 3" and run it
    let buf = codegen::compile("2 + 3;");
    let result = executor::execute(&buf);
    println!("result: {}", result); // should print 5

    let buf = codegen::compile("x = 10; x + 3;");
    let result = executor::execute(&buf);
    println!("result: {}", result); // should print 13
    

    let buf = codegen::compile("x = 10; y = 3; x -(-y);");
    let result = executor::execute(&buf);
    println!("result: {}", result); // should print 17
                                    
    let buf = codegen::compile(" x = 5 ; if ( x > 3 ) { x = 99;};");
    let result = executor::execute(&buf);
    println!("result: {}", result); 

    // else branch — should print 0
    let buf = codegen::compile("x = 2; if (x > 3) { x = 99; } else { x = 0; }; x;");
    let result = executor::execute(&buf);
    println!("else branch: {}", result);

    // while loop — should print 10 (adds 2 five times)
    let buf = codegen::compile("x = 0; y = 0; while (y < 5) { x = x + 2; y = y + 1; }; x;");
    let result = executor::execute(&buf);
    println!("while result: {}", result);
}


