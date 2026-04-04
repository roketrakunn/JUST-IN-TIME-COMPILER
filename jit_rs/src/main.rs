#![allow(dead_code, unused_imports)]

use crate::{codegen::compile, executor::execute};

mod lexer;
mod parser;
mod interpreter;
mod codegen;
mod executor;

fn main() {
    // --- original tests ---
    let result = execute(&compile("2 + 3;"));
    println!("2 + 3 = {} (expected 5)", result);

    let result = execute(&compile("x = 10; x + 3;"));
    println!("x=10, x+3 = {} (expected 13)", result);

    let result = execute(&compile("x = 10; y = 3; x -(-y);"));
    println!("x-(-y) = {} (expected 13)", result);

    let result = execute(&compile("x = 5; if (x > 3) { x = 99; };"));
    println!("if x>3 then x=99: {} (expected 99)", result);

    let result = execute(&compile("x = 2; if (x > 3) { x = 99; } else { x = 0; }; x;"));
    println!("else branch: {} (expected 0)", result);

    let result = execute(&compile("x = 0; y = 0; while (y < 5) { x = x + 2; y = y + 1; }; x;"));
    println!("while loop: {} (expected 10)", result);

    // --- function tests ---
    let result = execute(&compile("fn add() { x = 5; } add();"));
    println!("fn no args: {} (expected 5)", result);

    let result = execute(&compile("fn double() { x = 10; x = x + x; } double();"));
    println!("fn double: {} (expected 20)", result);

    let result = execute(&compile("fn add(a, b) { a + b; } add(3, 7);"));
    println!("fn add(3,7): {} (expected 10)", result);

    // --- fn in if condition ---
    let result = execute(&compile("fn add(a, b) { a + b; } if (add(2, 3) == 5) { 99; } else { 0; };"));
    println!("if add(2,3)==5: {} (expected 99)", result);

    // --- fn in while condition ---
    let result = execute(&compile("fn gt(a, b) { a > b; } x = 0; while (gt(x, 5) == 0) { x = x + 1; }; x;"));
    println!("while gt: {} (expected 6)", result);

    // --- x = add(1,2) + add(3,4) ---
    let result = execute(&compile("fn add(a, b) { a + b; } x = add(1, 2) + add(3, 4); x;"));
    println!("x = add(1,2) + add(3,4): {} (expected 10)", result);

    // --- if add(2,3) * 2 == 10 ---
    let result = execute(&compile("fn add(a, b) { a + b; } if (add(2, 3) * 2 == 10) { 99; } else { 0; };"));
    println!("if add(2,3)*2==10: {} (expected 99)", result);

    // --- while with fn in condition ---
    let result = execute(&compile("fn add(a, b) { a + b; } fn inc(a) { a + 1; } x = 0; while (x < add(4, 6)) { x = inc(x); }; x;"));
    println!("while x < add(4,6), inc(x): {} (expected 10)", result);

     let result = execute(&compile("x = 10; fn double() { x + x; }
        double();"));
  println!("global x in fn: {} (expected 20)", result);


 let result = execute(&compile("fn fact(n) { if (n < 2) { 1; } else { n *
   fact(n - 1); }; } fact(5);"));
  println!("fact(5): {} (expected 120)", result);






}
