// ============================================================
// PARSER — Turns a flat list of Tokens into an AST (tree)
// ============================================================
//
//
// "x = 5 + 3 * 2" becomes:
//
//        ASSIGN(x)
//            |
//           ADD
//          /   \
//         5    MUL
//             /   \
//            3     2
//

use crate::lexer::{Token, TokenKind};

// ------------------------------------------------------
// AST NODE — one node in our syntax tree
// -------------------------------------------------------
// use Box<Expr> for child nodes because a recursive
// struct needs heap allocation (the compiler must know the size).
// Box<T> = "one item on the heap" — like a unique_ptr in C++.
#[derive(Debug, Clone)]
pub enum Expr {
    // Leaf nodes (no children)
    Number(i64),
    Var(String),                        // reading a variable: x

    // Assignment: x = <expr>
    Assign {
        name: String,
        value: Box<Expr>,
    },

    // Binary operation: left OP right
    BinOp {
        op: BinOpKind,
        left: Box<Expr>,
        right: Box<Expr>,
    },

    // Unary operation: OP expr  (e.g. -x)
    UnaryOp {
        op: UnaryOpKind,
        expr: Box<Expr>,
    },

    // if (cond) { then } else { else_ }
    If {
        cond: Box<Expr>,
        then_block: Vec<Stmt>,
        else_block: Option<Vec<Stmt>>,
    },

    // while (cond) { body }
    While {
        cond: Box<Expr>,
        body: Vec<Stmt>,
    },

    // fn name(params) { body }  — declaration returns Unit
    FnCall {
        name: String,
        args: Vec<Expr>,
    },
}

#[derive(Debug, Clone)]
pub enum BinOpKind {
    Add, Sub, Mul, Div, Mod,
    EqEq, NotEq, Lt, Gt, LtEq, GtEq,
}

#[derive(Debug, Clone)]
pub enum UnaryOpKind {
    Neg,   // -x
    Pos,   // +x  (no-op but valid)
}

// -------------------------------------------------------
// STATEMENT — things that DO something (vs expressions that produce values)
// -------------------------------------------------------
// This is a key distinction we're adding over the C version:
//   Expression: 5 + 3         (produces 8)
//   Statement:  x = 5 + 3;   (stores 8, produces nothing)
//
// In our language, every statement ends with ';'
#[derive(Debug, Clone)]
pub enum Stmt {
    Expr(Expr),                         // expression used as statement: foo();
    Return(Expr),                       // return <expr>;
    FnDef {                             // fn name(params) { body }
        name: String,
        params: Vec<String>,
        body: Vec<Stmt>,
    },
}

// A full program is just a list of statements
pub type Program = Vec<Stmt>;

// -------------------------------------------------------
// THE PARSER
// -------------------------------------------------------
// It holds the token list and a cursor (pos).
pub struct Parser {
    tokens: Vec<Token>,
    pos: usize,
}

impl Parser {
    pub fn new(tokens: Vec<Token>) -> Self {
        Parser { tokens, pos: 0 }
    }

    // Look at current token without consuming it
    fn peek(&self) -> &TokenKind {
        &self.tokens[self.pos].kind
    }

    // Look at current token's line/col (for errors)
    fn peek_token(&self) -> &Token {
        &self.tokens[self.pos]
    }

    // Consume current token, return it, advance pos
    fn advance(&mut self) -> &Token {
        let tok = &self.tokens[self.pos];
        if self.pos + 1 < self.tokens.len() {
            self.pos += 1;
        }
        tok
    }

    // Consume token only if it matches expected kind
    // Returns true if matched, false otherwise
    fn matches(&mut self, kind: &TokenKind) -> bool {
        if self.peek() == kind {
            self.advance();
            true
        } else {
            false
        }
    }

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

    // -------------------------------------------------------
    // GRAMMAR RULES — each function = one grammar rule
    // -------------------------------------------------------
    // Precedence ladder (lowest → highest):
    //   parse_program
    //     parse_stmt
    //       parse_expr         ← assignment
    //         parse_comparison  ← == != < > <= >=
    //           parse_term      ← + -
    //             parse_factor  ← * / %
    //               parse_unary ← - +
    //                 parse_primary ← number, ident, (expr)

    pub fn parse_program(&mut self) -> Program {
        let mut stmts = Vec::new();
        while self.peek() != &TokenKind::Eof {
            stmts.push(self.parse_stmt());
        }
        stmts
    }

    fn parse_stmt(&mut self) -> Stmt {
        // fn definition
        if self.matches(&TokenKind::Fn) {
            return self.parse_fn_def();
        }

        // return statement
        if self.matches(&TokenKind::Return) {
            let expr = self.parse_expr();
            self.expect(&TokenKind::Semicolon);
            return Stmt::Return(expr);
        }

        // expression statement (assignment, call, etc.)
        let expr = self.parse_expr();
        self.expect(&TokenKind::Semicolon);
        Stmt::Expr(expr)
    }

    fn parse_fn_def(&mut self) -> Stmt {
        // fn <name> ( <params...> ) { <body...> }
        let name = match self.advance().kind.clone() {
            TokenKind::Ident(n) => n,
            other => panic!("Expected function name, got {:?}", other),
        };

        self.expect(&TokenKind::LParen);
        let mut params = Vec::new();
        while self.peek() != &TokenKind::RParen {
            match self.advance().kind.clone() {
                TokenKind::Ident(p) => params.push(p),
                other => panic!("Expected param name, got {:?}", other),
            }
            if !self.matches(&TokenKind::Comma) {
                break;
            }
        }
        self.expect(&TokenKind::RParen);

        let body = self.parse_block();
        Stmt::FnDef { name, params, body }
    }

    // Parse { stmt* }
    fn parse_block(&mut self) -> Vec<Stmt> {
        self.expect(&TokenKind::LBrace);
        let mut stmts = Vec::new();
        while self.peek() != &TokenKind::RBrace && self.peek() != &TokenKind::Eof {
            stmts.push(self.parse_stmt());
        }
        self.expect(&TokenKind::RBrace);
        stmts
    }

    // ---- Expression parsing (recursive descent) ----

    fn parse_expr(&mut self) -> Expr {
        // Is this an assignment? peek: IDENT followed by '='
        // We check: current is Ident AND next is Eq (not EqEq)
        if let TokenKind::Ident(name) = self.peek().clone() {
            // peek ahead one more
            let next_pos = self.pos + 1;
            if next_pos < self.tokens.len() {
                if let TokenKind::Eq = self.tokens[next_pos].kind {
                    // It IS an assignment
                    self.advance(); // consume ident
                    self.advance(); // consume =
                    let value = self.parse_expr();
                    return Expr::Assign { name, value: Box::new(value) };
                }
            }
        }

        self.parse_comparison()
    }

    fn parse_comparison(&mut self) -> Expr {
        let mut left = self.parse_term();

        loop {
            let op = match self.peek() {
                TokenKind::EqEq  => BinOpKind::EqEq,
                TokenKind::BangEq => BinOpKind::NotEq,
                TokenKind::Lt    => BinOpKind::Lt,
                TokenKind::Gt    => BinOpKind::Gt,
                TokenKind::LtEq  => BinOpKind::LtEq,
                TokenKind::GtEq  => BinOpKind::GtEq,
                _ => break,
            };
            self.advance();
            let right = self.parse_term();
            left = Expr::BinOp { op, left: Box::new(left), right: Box::new(right) };
        }

        left
    }

    fn parse_term(&mut self) -> Expr {
        let mut left = self.parse_factor();

        loop {
            let op = match self.peek() {
                TokenKind::Plus  => BinOpKind::Add,
                TokenKind::Minus => BinOpKind::Sub,
                _ => break,
            };
            self.advance();
            let right = self.parse_factor();
            left = Expr::BinOp { op, left: Box::new(left), right: Box::new(right) };
        }

        left
    }

    fn parse_factor(&mut self) -> Expr {
        let mut left = self.parse_unary();

        loop {
            let op = match self.peek() {
                TokenKind::Star    => BinOpKind::Mul,
                TokenKind::Slash   => BinOpKind::Div,
                TokenKind::Percent => BinOpKind::Mod,
                _ => break,
            };
            self.advance();
            let right = self.parse_unary();
            left = Expr::BinOp { op, left: Box::new(left), right: Box::new(right) };
        }

        left
    }

    fn parse_unary(&mut self) -> Expr {
        if self.matches(&TokenKind::Minus) {
            let expr = self.parse_unary();
            return Expr::UnaryOp { op: UnaryOpKind::Neg, expr: Box::new(expr) };
        }
        if self.matches(&TokenKind::Plus) {
            let expr = self.parse_unary();
            return Expr::UnaryOp { op: UnaryOpKind::Pos, expr: Box::new(expr) };
        }
        self.parse_primary()
    }

    fn parse_primary(&mut self) -> Expr {
        match self.peek().clone() {
            // Literal number
            TokenKind::Number(n) => {
                let n = n;
                self.advance();
                Expr::Number(n)
            }

            // Identifier: either a variable read or a function call
            TokenKind::Ident(name) => {
                self.advance();
                // Is it a function call?
                if self.matches(&TokenKind::LParen) {
                    let mut args = Vec::new();
                    while self.peek() != &TokenKind::RParen {
                        args.push(self.parse_expr());
                        if !self.matches(&TokenKind::Comma) { break; }
                    }
                    self.expect(&TokenKind::RParen);
                    Expr::FnCall { name, args }
                } else {
                    Expr::Var(name)
                }
            }

            // Grouped expression: (expr)
            TokenKind::LParen => {
                self.advance();
                let expr = self.parse_expr();
                self.expect(&TokenKind::RParen);
                expr
            }

            // if expression
            TokenKind::If => {
                self.advance();
                self.expect(&TokenKind::LParen);
                let cond = self.parse_expr();
                self.expect(&TokenKind::RParen);
                let then_block = self.parse_block();
                let else_block = if self.matches(&TokenKind::Else) {
                    Some(self.parse_block())
                } else {
                    None
                };
                Expr::If { cond: Box::new(cond), then_block, else_block }
            }

            // while expression
            TokenKind::While => {
                self.advance();
                self.expect(&TokenKind::LParen);
                let cond = self.parse_expr();
                self.expect(&TokenKind::RParen);
                let body = self.parse_block();
                Expr::While { cond: Box::new(cond), body }
            }

            other => {
                let tok = self.peek_token();
                panic!("Unexpected token {:?} at line {} col {}", other, tok.line, tok.col);
            }
        }
    }
}

// Public convenience function 
pub fn parse(source: &str) -> Program {
    let tokens = crate::lexer::Lexer::new(source).tokenise();
    let mut parser = Parser::new(tokens);
    parser.parse_program()
}
