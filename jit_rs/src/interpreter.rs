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

    /**Push a new scope , like entering a new if or while block*/
    pub fn push_scope(&mut self) {
        self.scopes.push(HashMap::new());
    }

    /**
     * Pop the scope ,liek breaking out of while loop if if stmt
     * */
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


//well not its time to store functions 

/**
 * --------FUNCTIN DEFINITION STORE--------
 * These are stored seperately from variables
 * so when you call a function , e.g Add() this is where
 * the interpreter will look.
 * */

#[derive(Debug,Clone)]
pub struct FnDef{
    pub params : Vec<String>,
    pub body :Vec<Stmt>,
}

//---SIGNAL---- 
//When a function hits return x ; deep in the cal stack
//we need to to recursively unwind or way back immmediately 
//we propagate thru the call stack.

#[derive(Debug)]
enum Signal{
    Return(Value),
}
//==========THE INTERPETER===========

pub struct Interpreter { 
    pub  env :Env,
    functions : HashMap<String, FnDef>,
}

impl Interpreter {
    
    pub fn new() -> Self {
        Interpreter {
            env: Env::new(), 
            functions: HashMap::new(),
        }
    }

    // run a full program ... just a list of statements 
    // Returns the value  of the last evaluated expression.

    pub  fn run(&mut self , program : &Program) -> Value {
        self.exec_stmts(program).unwrap_or(Value::Uint)
    }

    fn exec_stmts(&mut self ,stmts : &[Stmt])-> Result<Value , Signal> {
        let mut last = Value::Uint;
        for stmt in stmts { 
            last = self.exec_stmt(stmt)?;
        }
        Ok(last)
    }


    fn exec_stmt(&mut self, stmt :&Stmt) ->Result<Value , Signal> {
        match stmt {
            //On expression statement , evaluate it and return its value.
            Stmt::Expr(expr) => { 
                Ok(self.eval_expr(expr)?)
            }

            //return expr => pack the value into a signal to unwind the stk
            
            Stmt::Return(expr) => { 
                let val  = self.eval_expr(expr)?;
                Err(Signal::Return(val))
            }

            //fn name(params) just register it , do not run it yet.

            Stmt::FnDef { name, params, body } => {
                self.functions.insert(name.clone(), FnDef {
                    params: params.clone() ,
                    body: body.clone()
                });
                
                Ok(Value::Uint)
            }
        }
    }

    fn eval_expr(&mut self, expr : &Expr) -> Result<Value,Signal> {
        
        match expr {
            
            // A literal number 
            Expr::Number(n) => Ok(Value::Int(*n)),

            // a variable read , loook it up in the environment

            Expr::Var(name) => { 
                match self.env.get(name) {
                    Some(val) => Ok(val.clone()),
                    None => panic!("Undefined varibale {}",name),
                }
            }

            //Assignmet : eval right side and store on environment

            Expr::Assign { name, value } => { 
                let val = self.eval_expr(value)?;
                self.env.set(name, val.clone());
                Ok(val)
            }


            // Binary operations
        
            Expr::BinOp { op, left, right } => { 
                let l = self.eval_expr(left)?.as_int();
                let r = self.eval_expr(right)?.as_int();

                let results = match op {
                    
                    BinOpKind::Add => l + r,
                    BinOpKind::Sub => l - r,
                    BinOpKind::Mul => l * r,
                    BinOpKind::Div=>  { 
                        if r == 0 { panic!("Error division by zero!");}
                        l/r
                    },
                    BinOpKind::Mod => {
                        if r == 0 {panic!("Error mudulo by zero");}
                        r % l
                    }

                    BinOpKind::EqEq  => (l == r) as i64,
                    BinOpKind::NotEq => (l != r) as i64,
                    BinOpKind::Lt    => (l <  r) as i64,
                    BinOpKind::Gt    => (l >  r) as i64,
                    BinOpKind::LtEq  => (l <= r) as i64,
                    BinOpKind::GtEq  => (l >= r) as i64,

                };
                Ok(Value::Int(results))
            }
            Expr::UnaryOp { op, expr } => {
                let val = self.eval_expr(expr)?.as_int();
                let resulst = match op {
                    
                    UnaryOpKind::Neg => -val,
                    UnaryOpKind::Pos => val,
                };
                Ok(Value::Int(resulst))
            }
        }
    }
}


    






