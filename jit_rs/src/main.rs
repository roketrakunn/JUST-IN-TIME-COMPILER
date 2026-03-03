
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
}

