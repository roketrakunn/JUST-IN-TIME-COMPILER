// ============================================================
// LEXER — Breaks raw source text into a stream of Tokens
// ============================================================

// -------------------------------------------------------
// TOKEN TYPES — every kind of "word" our language has
// -------------------------------------------------------
#[derive(Debug, Clone, PartialEq)]
pub enum TokenKind {
    // Literals
    Number(i64),        // 42, -7, 1000

    // Identifiers & Keywords
    Ident(String),      // variable names: x, foo, my_var
    If,                 // if
    Else,               // else
    While,              // while
    Fn,                 // fn
    Return,             // return

    // Operators
    Plus,               // +
    Minus,              // -
    Star,               // *
    Slash,              // /
    Percent,            // %

    // Comparison (needed for if/while conditions)
    EqEq,               // ==
    BangEq,             // !=
    Lt,                 // <
    Gt,                 // >
    LtEq,               // <=
    GtEq,               // >=

    // Assignment
    Eq,                 // =

    // Delimiters
    LParen,             // (
    RParen,             // )
    LBrace,             // {
    RBrace,             // }
    Semicolon,          // ;
    Comma,              // ,

    // End of input
    Eof,
}

// A Token pairs a kind with WHERE in the source it came from.
// The position (line, col) for error messages:
//   "Error at line 3, col 7: undefined variable 'x'"
#[derive(Debug, Clone)]
pub struct Token {
    pub kind: TokenKind,
    pub line: usize,
    pub col: usize,
}

// -------------------------------------------------------
// THE LEXER 
// -------------------------------------------------------
// It holds:
//   - the source text as a Vec of chars (easier to index than bytes)
//   - pos  : current position in that vec
//   - line, col : for error reporting
pub struct Lexer {
    source: Vec<char>,
    pos: usize,
    line: usize,
    col: usize,
}

impl Lexer {
    // Constructor — takes a &str, converts to Vec<char>
    pub fn new(source: &str) -> Self {
        Lexer {
            source: source.chars().collect(),
            pos: 0,
            line: 1,
            col: 1,
        }
    }

    // Peek at the current char WITHOUT consuming it
    // ANALOGY: Looking ahead in a book without turning the page
    fn peek(&self) -> Option<char> {
        self.source.get(self.pos).copied()
    }

    // Peek TWO chars ahead (needed to tell == from =)
    fn peek2(&self) -> Option<char> {
        self.source.get(self.pos + 1).copied()
    }

    // Consume the current char and advance position
    fn advance(&mut self) -> Option<char> {
        let ch = self.source.get(self.pos).copied();
        if let Some(c) = ch {
            self.pos += 1;
            if c == '\n' {
                self.line += 1;
                self.col = 1;
            } else {
                self.col += 1;
            }
        }
        ch
    }

    // Skip spaces, tabs, newlines
    fn skip_whitespace(&mut self) {
        while matches!(self.peek(), Some(' ') | Some('\t') | Some('\n') | Some('\r')) {
            self.advance();
        }
    }

    // Read a full integer number like 1234
    fn read_number(&mut self) -> i64 {
        let mut value: i64 = 0;
        while let Some(c) = self.peek() {
            if c.is_ascii_digit() {
                value = value * 10 + (c as i64 - '0' as i64);
                self.advance();
            } else {
                break;
            }
        }
        value
    }

    // Read an identifier or keyword like "while", "x", "myVar"
    fn read_ident(&mut self) -> String {
        let mut s = String::new();
        while let Some(c) = self.peek() {
            if c.is_alphanumeric() || c == '_' {
                s.push(c);
                self.advance();
            } else {
                break;
            }
        }
        s
    }

    // The main method — returns the next Token from the source
    // This is called repeatedly by the parser.
    pub fn next_token(&mut self) -> Token {
        self.skip_whitespace();

        let line = self.line;
        let col = self.col;

        // Helper closure to build a token at the current position
        let make = |kind: TokenKind, line: usize, col: usize| Token { kind, line, col };

        match self.peek() {
            None => make(TokenKind::Eof, line, col),

            Some(c) if c.is_ascii_digit() => {
                let n = self.read_number();
                make(TokenKind::Number(n), line, col)
            }

            Some(c) if c.is_alphabetic() || c == '_' => {
                let ident = self.read_ident();
                // Check if it's a keyword
                let kind = match ident.as_str() {
                    "if"     => TokenKind::If,
                    "else"   => TokenKind::Else,
                    "while"  => TokenKind::While,
                    "fn"     => TokenKind::Fn,
                    "return" => TokenKind::Return,
                    _        => TokenKind::Ident(ident),
                };
                make(kind, line, col)
            }

            Some(_) => {
                // Single (or double) character tokens
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
                    ';' => TokenKind::Semicolon,
                    ',' => TokenKind::Comma,

                    // Two-char operators: == != <= >=
                    '=' => {
                        if self.peek() == Some('=') { self.advance(); TokenKind::EqEq }
                        else { TokenKind::Eq }
                    }
                    '!' => {
                        if self.peek() == Some('=') { self.advance(); TokenKind::BangEq }
                        else { panic!("Unexpected '!' at line {line} col {col}") }
                    }
                    '<' => {
                        if self.peek() == Some('=') { self.advance(); TokenKind::LtEq }
                        else { TokenKind::Lt }
                    }
                    '>' => {
                        if self.peek() == Some('=') { self.advance(); TokenKind::GtEq }
                        else { TokenKind::Gt }
                    }

                    other => panic!("Unknown character '{}' at line {line} col {col}", other),
                };
                make(kind, line, col)
            }
        }
    }

    // Convenience: tokenise the ENTIRE source into a Vec<Token>
    // The parser will use this Vec instead of calling next_token() directly.
    pub fn tokenise(mut self) -> Vec<Token> {
        let mut tokens = Vec::new();
        loop {
            let tok = self.next_token();
            let is_eof = tok.kind == TokenKind::Eof;
            tokens.push(tok);
            if is_eof { break; }
        }
        tokens
    }
}
