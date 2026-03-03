
#![allow(dead_code, unused_imports)]

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
    

    let buf = codegen::compile("x = 10; y = 7; x + y;");
    let result = executor::execute(&buf);
    println!("result: {}", result); // should print 17
 
    


}

