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

use std::{collections::{HashMap, hash_map}, fmt::write, panic, thread::scope};
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

impl std::fmt::Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::Int(n) => write!(f,"{}",n),
            Value::Uint =>write!(f,"()")
        }
    }
}


/**
 * ------ ENVIRONMENT(symbol table if you wanna)------
 * Uses a stack of hashmaps to distinguish "scope"
 * Imagine you lost your keys in a big house 
 * YOu first would check maybe under the bed
 * And the dining hall
 * And then maybe the balcony and so on ..
 * THat is the idea here.well that is the idea
 */

#[derive(Debug, Clone)]
pub struct Env { 
    //each hashmap is a "scope" functiomn body , if block , while..etc
    scopes : Vec<HashMap<String, Value>>
}

impl Env {
    
    //start with one global scope
    pub fn new() -> Self {
        Env { scopes: vec![HashMap::new()] }
    }

    /**Push a new scope */
    pub fn push_scope(&mut self) {
        self.scopes.push(HashMap::new());
    }

    pub fn pop_scope(&mut self) {
        self.scopes.pop();
    }

    //store a variable in teh current inner most scope

    pub fn set(&mut self , name:&str , value :Value) {

        //walk from the inner most to outer , update if found
        for scope in self.scopes.iter_mut().rev() { 
            if scope.contains_key(name) {
                scope.insert(name.to_string(), value);
                return 
            }
        }

        //if it is not found then create a new one in currnt scope
        let last = self.scopes.last_mut().unwrap();
        last.insert(name.to_string(), value);
    }

    /**get value if exist , looks it up from inner scope outwards.*/
    pub fn get(&mut self , name:&str) ->Option<&Value> {
        for scope in self.scopes .iter().rev() {
            if let Some(val) = scope.get(name) { 
                return Some(val);
            }
        }
        None
    }
}



    






