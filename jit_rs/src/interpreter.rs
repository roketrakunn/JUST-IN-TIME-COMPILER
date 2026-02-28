/**
 * -------- THIS IS THE INTERPRTER------------
 * Walks the ASTN Built by the parser and generate what is needed 
 * Like sya you have a node that is of token tyepe + ... and left as like
 * 3 and right as 7 
 * The interpreter will walk those and compute the resulsts
 * which in this case would be uh..... 10 ... 
 * Now unlike the JIT ... which writes codegen that will do all of that
 * faster
 * The interpretter is like .. on drugs... cool .. chilled and doing its
 * THing slow 
 * while the JIT is flash , well because it got to do the same thing more
 * complex but faster
 *
 *
 * WHAT WE ARE IMPLEMENTING 
  + Recursively walk the tree and compute the values as we go.
  + There is not machine code .. well atleast here.
 * */

use std::{collections::hash_map, panic};
use crate::parser::{Expr, Stmt , BinOpKind, UnaryOpKind , Program};



/**
 * Value = what the interpeter returns upon evaluation 
 * This for now is of type int 
 * Yes there is no floats or doubles as of yet ( because i am learning)
 * 
 */

#[derive(Debug , Clone , PartialEq)]
pub enum Value {
    Int(i64),
    Uint, // nothin returned by assingment , void funcs and all.
}

impl Value {
    // helper function to get value as realy intm.. panics if its not 
    // like guy making sure you are woman before they sleep with you 
    // bad example
    // acknowledged , fully
    
    pub fn as_int(&self) -> i64 {
        match self {
            Value::Int(n) => *n,
            Value::Uint => panic!("Expected integer , got Uint")
        }
    }

    // truthy check , 0 = false all else is true
    pub fn is_truthy(&self) -> bool {
        match self {
            Value::Int(n) => *n != 0,
            Value::Uint => false,
        }
    }
}







