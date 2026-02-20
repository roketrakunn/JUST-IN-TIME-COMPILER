//THIS IS THE LEXER 
//What it does ? turns a string of characters into meaninfull list of words/tokens we will use
// e.g "x = 5 + 10;"
// you get [Ident("x")]  [Eq]  [Number(5)]  [Plus]  [Number(10)]  [Semicolon]  [Eof]

use std::{char, intrinsics::{breakpoint, volatile_load}, ptr::slice_from_raw_parts, slice::SliceIndex, vec};

#[derive(Debug , Clone , PartialEq)]

pub enum TokenKind { 
    Number(i64),
    Indent(String), 

    //Identifiers and key words
    If,
    Else , 
    While,
    Return,
    
    //Operators
    Plus,  //addition
    Minus, //subtration
    Star, //multiplication
    Slash, //int dv
    Percent, //mod div


    //comparisons for stuff like ifs and whiles

    EqEw , // == if ( x== y) typa thing
    BangEq, // != ( same thing) 
    Lt,         //les than
    Gt,         //greater than
    LtEq,        // less than or equals to 
    GtEq,       //greater than or equal to.


    Eq ,        //assingment

    LParen,      // "(" 
    RParen,      // ")"
    LBrace,     // "{" 
    RBrace,     //"}"
    SemiColon,  // ";"
    Comma,      // ","

    //end of input/line 
    Eof
}

/**
 * Token to pair a kind with where it actual came from in the source.
 * col and line used for error messages later.
 * */

#[derive(Debug , Clone)]
pub  struct Token { 
    pub kind : TokenKind,
    pub line : usize, 
    pub col : usize,
}

//============= THE LEXER =============#

/**
 *It holds: 
    + The source text as vector of chars.
    + Easier to navigate/index than bytes
    + pos : Current position in that vec
    + line , col : for error reporting (fancy stuff)
*/

pub  struct Lexer {
    source : Vec<char>, 
    pos : usize , 
    line : usize , 
    col : usize,
}

// A Constuctor that takes &str and converts it to our source vector.

impl Lexer {
    //returns a new lexer
    pub fn new(source : &str) -> Self{
        Lexer { source: source.chars().collect(),
        pos: 0,
        line: 1, 
        col: 1,
        }
    }

    // Peak at the current char without consumig it.
    fn peak(&self) -> Option<char> { 
        self.source.get(self.pos).copied() // "get the char from source and derefernce it" just
                                           // looking
    }

    //peak two chars ahead , needed to tell == from =

    fn peak2(&self) -> Option<char> { 
         self.source.get(self.pos + 1).copied() 
    }

    //consume char and advance postion 
    
    fn advance(&mut self) -> Option<char> { 
        let ch = self.source.get(self.pos).copied(); 
        if let Some(ch) = ch { 
            self.pos + 1 ;
            if ch == '\n' { 
                self.line += 1;
                self.col = 1;
            } else {
                self.col += 1;
            }
        }
        ch
    }
    //skips white spaces/tabs/newlines 

    fn skip_whitespace(&mut self) { 
        while matches!(self.peak() , Some(' ') | Some('\t') | Some('\n') | Some('\r') ) {
            self.advance();
        }
    }

    /**
     * Peak at next char , retuned is Some(char)
     * If None is  returned then loop ends/breaks
     * IF the char existed and was a value
     * we coveert it to its value from asci and build our value
     * return value at the end
     */

    fn read_number(&mut self) -> i64 { 
        let mut value :i64 = 0 ; 

        while let Some(c) = self.peak() {
            
            if c.is_ascii_digit() {
                value = value * 10 + ( c as i64  - '0' as i64);
                self.advance();
            } else {
                break;
            }
        }
        value 
    } 

    //Read an identifier or keyword like while x , myVar  , if

    fn read_ident(&mut self) -> String { 
        let mut s = String::new();
        while let Some(c) = self.peak() {
            if c.is_alphanumeric() || c == '_' { 
                s.push(c);
                self.advance();
            } else {
                break;
            }
        }
        s
    }

    /**
     * This is the main function , returns the next token from he source
     * Repeatdly called by the parser
     *
     */

    fn next_token(&mut self) -> Token { 
        self.skip_whitespace();

        let line = self.line;
        let col = self.col;

        let make = | kind : TokenKind , line : usize , col : usize |  Token { kind, line, col }; 

        match self.peak() {
            None => make(TokenKind::Eof, line, col),

            Some(c) if c.is_ascii_digit() => { 
                let n = self.read_number();
                make(TokenKind::Number(n), line , col)
            }

            Some(c) if c.is_alphabetic() || c == '_' => { 
                let ident = self.read_ident();

                //check if its a keyword

                let kind = match ident.as_str() {
                    "if"    => TokenKind::If,
                    "else"  => TokenKind::Else,
                    "while" => TokenKind::While,
                    "fn"    => TokenKind::Fn, 
                    "return" => TokenKind::Return,
                    _       => TokenKind::Indent(ident)
                    
                };
                make(kind,line,col)
            }

            Some(_) => { 
                //single double char token
                

                let c = self.advance().unwrap();
                let kind = match c {
                    '+' => TokenKind::Plus,
                    '-' => TokenKind::Minus,
                    '*' => TokenKind::Star,
                    '/' => TokenKind::Slash,
                    '%' => TokenKind::Percent,
                    '(' => TokenKind::LParen,
                    ')' => TokenKind::RParen,
                    '{' => TokenKind::LBrace,
                    '}' => TokenKind::RBrace,
                    ';' => TokenKind::SemiColon,
                    ',' => TokenKind::Comma,

                    // two char ops like ,<= or == or anything you are thinkng of

                    '=' => { 
                       if self.peak() == Some('=') { self.advance(); TokenKind::EqEq }
                        else { TokenKind::Eq } 
                    }

                    '!' => { 
                        if self.peak()  == Some('='){
                            self.advance();
                            TokenKind::BangEq
                        }else {
                            panic!("Unexpected '!' at line {line} col {col}")
                        }
                    }

                    '<' => {
                        if self.peak()== Some('=') { self.advance(); TokenKind::LtEq }
                        else { TokenKind::Lt }
                    }
                    '>' => {
                        if self.peak() == Some('=') { self.advance(); TokenKind::GtEq }
                        else { TokenKind::Gt }
                    }
                    
                    other => panic!("Unknown character '{}' at line {line} col {col}", other),
                };
                make(kind,line,col)
            }
        }
    }

    // Convinience : tokenise the whole source into Vec<Token>
    // The parser can use this instead of calling next_token()

    pub fn tokenise(mut self) -> Vec<Token> { 
        let mut tokens = Vec::new();
        loop {
            let tok = self.next_token();
            let is_eof = tok.kind == TokenKind::Eof;
            tokens.push(tok);
            if is_eof {break;}
        }
        tokens
    }
}




