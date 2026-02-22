use std::intrinsics::simd::simd_le;

/** @parser
 * Parser
 *
 * The parser transforms a list of tokens into an Abstract Syntax Tree (AST).
 *
 * The AST is important because it encodes operator precedence.
 * For example:
 *
 *     2 + 3 * 4        is NOT the same as        (2 + 3) * 4
 *
 *     2 + 3 * 4
 *
 *         ADD
 *        /   \
 *       2    MUL
 *           /   \
 *          3     4
 *
 *
 *     (2 + 3) * 4
 *
 *         MUL
 *        /   \
 *      ADD     4
 *     /   \
 *    2     3
 *
 *
 * Example:
 *     x = 5 + 3 * 2
 *
 * Becomes:
 *
 *         ASSIGN(x)
 *             |
 *            ADD
 *           /   \
 *          5    MUL
 *              /   \
 *             3     2
 *
 * Notice:
 * Multiplication appears deeper in the tree,
 * which reflects its higher precedence.
 *
 * The tree is built bottom-up according to precedence rules.
 */

use crate::lexer::{Token, TokenKind};

/**
 * AST NODE - one node in he syntax tree 
 * I used Box<Expr> for child node beacause a rercusive struct needs
 * heap allocation(so the compiler must know the size)
 *
 * Box<Expr>  = "One item per heap" , its a pointer , pointers have known size
 */

#[derive(Debug ,Clone)]
pub enum Expr {
    // leaf Node
    Number(i64),
    Var(String),        // reading a varible .. likee uhh .. x = expr 

    Assign { 
        name : String,
        value: Box<Expr>,
    },

    // Binary operation : left op right
    BinOp { 
        op : BinOpKind,
        left : Box<Expr>,
        right: Box<Expr>,
    },

    // Unary operation , e.g -x 
    
    UnaryOp { 
        op : UnaryOpKind,
        expr : Box<Expr>,
    },

    //if (cond) { then} else {else_then}

    If { 
        cond : Box<Expr>,
        then_block: Vec<Stmt>,
        else_block: Option<Vec<Stmt>>,
    },


    // while (cond) {body}

    While { 
        cond : Box<Expr>,
        body : Vec<Stmt>,
    },

    //Function call : fn name(params) {body} -declaration returns Uint

    FnCall { 
        name :String,
        args :Vec<Expr>,
    },
}


#[derive(Debug, Clone)]

pub enum BinOpKind {
    Add, Sub, Mul, Div ,Mod,
    EqEq , NotEq , Lt , Gt , LtEq , GtEq,
}

#[derive(Debug, Clone)]

pub enum UnaryOpKind {
    Neg , // -x 
    Pos , //mmm
}


/**
 * STATEMENTS - Things that DO something (vs things/expressions that produce/return values)
 * Statement : x = 6 + 8 (stores 14 to x)
 * Expression : 5 + 8 (produces 13)
 *
 * Every Statement ends with ';'
 */


#[derive(Debug, Clone)]

pub enum Stmt {

    Expr(Expr),             //expression used as statement , e.g foo();
    Return(Expr),           //return <expr>
                            
    FnDef {                 //fn name(param) {body}
        name: String,
        params: Vec<String>,
        body : Vec<Stmt>,
    },           
}

// full program = list of statemens 
pub type Program = Vec<Stmt>;

/**
 * ----THE PASER----
 * Contains the tokens list and the curso postion
 * Its like reading a book while holding a marker
 * peek() raed curr page
 * advance() turn to the next page
 * */

pub struct Parser { 
    tokens : Vec<Token>,
    pos : usize,
} 

impl Parser {

    // Create a new parser 
    pub fn new(tokens : Vec<Token>) -> Self {
        Parser { tokens, pos: 0 }
    }

    //look at the curr token without consuming it 

    fn peek(&self) -> &TokenKind { 
        &self.tokens[self.pos].kind
    }

    // Loook at the current tokens col/line for errors
   
    fn peek_token(&self) -> &Token {
        &self.tokens[self.pos]
    }

    //consume the curr token, return it and advance to the next token.

    fn advance(&mut self) -> &Token { 
        let tok = &self.tokens[self.pos];
        if self.pos < self.tokens.len() { 
            self.pos += 1;
        }
        tok
    } 

    // Consume the token if it macthes the expected kind , 
    // Return true if it does , else false

    fn matches(&mut self , kind :&TokenKind) -> bool { 
        if self.peek() == kind { 
            self.advance();
            return true;
        }
        false
    }

    // This is like matches but panics if the token does nto exist
    // Used when grammer requires a specific token


    // Like matches() but PANICS if token doesn't match
    // Used when the grammar REQUIRES a specific token
    fn expect(&mut self, kind: &TokenKind) {
        if self.peek() != kind {
            let tok = self.peek_token();
            panic!(
                "Expected {:?} but got {:?} at line {} col {}",
                kind, self.peek(), tok.line, tok.col
            );
        }
        self.advance();
    }

    /**
     * ----GRAMMER RULES-----
     * Precedence ladder ( lowest -> highest):
     *  parse_program 
     *      parse_stmt
     *          parser_expr         -> assignt variable
     *              parser_comparison   -> == , != , , <= , >=
     *                  parse_term  -> + , -
     *                      parse_factor    -> * / % 
     *                          parse_unary -> - + 
     *                              parse_primary -> number indent ,(expr)
     *
     * */
    
    pub fn parse_program(&mut self) -> Program {
        
        let mut stmts = Vec::new();
        
        while self.peek() != &TokenKind::Eof {
            stmts.push(self.parse_stmt());
        }
        stmts
    }

    pub fn parse_stmt(&mut self ) -> Stmt {
        //fn definition 
        
        if self.matches(&TokenKind::Fn) { 
            return return self.parse_fn_def();
        }
        
        //return statements 

        if self.matches(&TokenKind::Return) { 
            let expr = self.parse_expr;
            self.expect(&TokenKind::SemiColon);
            return Stmt::Return(expr);
        }

        // expression statement ( assignment , call , etc)

        let expr = self.parse_expr();
        self.expect(&TokenKind::SemiColon);
        Stmt::Expr(expr)
    }

    // ----TO BE CONTINUED----

}

