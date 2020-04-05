use std::cmp;
use std::fmt;
use std::str::FromStr;

use super::errors::*;
use crate::ast::Span;

#[derive(PartialEq, Eq, Debug, Clone)]
pub enum TokenKind {
    Ident(String),

    Keyword(Keyword),

    Comment,

    // Values for internally supported types
    Literal(Literal),

    PathSep,
    Sep,

    // Delimiters
    LBrace,
    RBrace,
    LParen,
    RParen,
    LBracket,
    RBracket,

    Colon,
    Dot,
    Comma,

    Eq,

    Operator(Operator),

    // other punktuation tokens
    Semi,
    Underscore,
    ColonEq,
    ThinArrow,
    EOF,
}

impl fmt::Display for TokenKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let str = match self {
            TokenKind::Ident(id) => id,
            TokenKind::Keyword(kw) => kw.as_str(),
            TokenKind::Comment => "//",
            TokenKind::Literal(l) => l.as_str(),
            TokenKind::PathSep => "::",
            TokenKind::LBrace => "{",
            TokenKind::RBrace => "}",
            TokenKind::LParen => "(",
            TokenKind::RParen => ")",
            TokenKind::LBracket => "[",
            TokenKind::RBracket => "]",
            TokenKind::Sep => "|",
            TokenKind::Colon => ":",
            TokenKind::Comma => ",",
            TokenKind::Dot => ".",
            TokenKind::Eq => "=",
            TokenKind::Operator(op) => op.as_str(),
            TokenKind::Semi => ",",
            TokenKind::Underscore => "_",
            TokenKind::ColonEq => ":=",
            TokenKind::ThinArrow => "->",
            TokenKind::EOF => "EOF",
        };
        write!(f, "{}", str)
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Operator {
    // math and boolean operator
    Plus,
    Minus,
    Slash,
    Star,

    Not,
    And,
    Or,

    // Comparison operators
    EqEq,
    NotEq,
    Greater,
    GreaterEq,
    Less,
    LessEq,
}

impl Operator {
    fn as_str(&self) -> &'static str {
        match self {
            Operator::Plus => "+",
            Operator::Minus => "-",
            Operator::Star => "*",
            Operator::Slash => "/",
            Operator::And => "und",
            Operator::Or => "oder",
            Operator::Not => "nicht",
            Operator::EqEq => "gleich",
            Operator::NotEq => "ungleich",
            Operator::GreaterEq => ">=",
            Operator::Greater => ">",
            Operator::LessEq => "<=",
            Operator::Less => "<",
        }
    }
}

impl fmt::Display for Operator {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

impl FromStr for Operator {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "+" => Ok(Operator::Plus),
            "-" => Ok(Operator::Minus),
            "*" => Ok(Operator::Star),
            "/" => Ok(Operator::Slash),
            "nicht" | "!" => Ok(Operator::Not),
            "und" | "&&" => Ok(Operator::And),
            "oder" | "||" => Ok(Operator::Or),
            "ungleich" | "!=" => Ok(Operator::NotEq),
            "gleich" | "==" => Ok(Operator::EqEq),
            "groesser_gleich" | ">=" => Ok(Operator::EqEq),
            "groesser" | ">" => Ok(Operator::Greater),
            "kleiner" | "<" => Ok(Operator::Less),
            "kleiner_gleich" | "<=" => Ok(Operator::LessEq),
            _ => Err(()),
        }
    }
}

#[derive(PartialEq, Debug, Clone)]
pub enum Literal {
    String(String),
    Number(f64),
    Bool(bool),
}

impl Eq for Literal {}

impl Literal {
    fn as_str(&self) -> &'static str {
        match self {
            Literal::String(_) => "Textliteral",
            Literal::Number(_) => "Zahlenliteral",
            Literal::Bool(_) => "Boolliteral",
        }
    }
}

impl FromStr for Literal {
    type Err = ();

    // NOTE(Simon): we just match bool litearl here to avoid the added performance cost of checking for a string or a number
    // each time we build a token, we already do this in the scan_token fn of the lexer
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "wahr" => Ok(Literal::Bool(true)),
            "falsch" => Ok(Literal::Bool(false)),
            _ => Err(()),
        }
    }
}

#[derive(PartialEq, Debug, Eq, Clone)]
pub enum Keyword {
    // keywords used internall by the language
    Fun,
    Struct,
    Impl,
    This,
    While,
    Return,
    For,
    Break,
    Range,
    If,
    Then,
    Else,
}

impl Keyword {
    fn as_str(&self) -> &'static str {
        match self {
            Keyword::Fun => "fun",
            Keyword::Struct => "typ",
            Keyword::Impl => "implementiere",
            Keyword::This => "selbst",
            Keyword::While => "solange",
            Keyword::Return => "rueckgabe",
            Keyword::For => "fuer",
            Keyword::Break => "stop",
            Keyword::Range => "bis",
            Keyword::If => "wenn",
            Keyword::Then => "dann",
            Keyword::Else => "sonst",
        }
    }
}

impl fmt::Display for Keyword {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

impl FromStr for Keyword {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "funktion" | "fun" | "fn" => Ok(Keyword::Fun),
            "Typ" | "typ" => Ok(Keyword::Struct),
            "implementiere" | "impl" => Ok(Keyword::Impl),
            "selbst" => Ok(Keyword::This),
            "solange" => Ok(Keyword::While),
            "rueckgabe" => Ok(Keyword::Return),
            "fuer" => Ok(Keyword::For),
            ".." | "bis" => Ok(Keyword::Range),
            "wenn" => Ok(Keyword::If),
            "dann" => Ok(Keyword::Then),
            "sonst" => Ok(Keyword::Else),
            "stop" => Ok(Keyword::Break),
            _ => Err(()),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
}

pub struct Lexer {
    buffer: String,
    cursor: usize,
    line: usize,
}

impl Lexer {
    pub fn new(data: String) -> Self {
        Lexer {
            buffer: data,
            cursor: 0,
            line: 1,
        }
    }
    fn advance(&mut self) -> Option<char> {
        let c = self.buffer.chars().nth(self.cursor);
        if let Some('\n') = c {
            self.line += 1;
        }
        self.cursor += 1;
        c
    }

    pub fn peek(&mut self) -> Option<char> {
        self.buffer.chars().nth(self.cursor)
    }

    fn peek_next(&mut self) -> Option<char> {
        self.buffer.chars().nth(self.cursor + 1)
    }

    fn map_if<F>(&mut self, p: F, res: TokenKind) -> Option<TokenKind>
    where
        F: Fn(char) -> bool,
    {
        match self.peek() {
            Some(c) => {
                if p(c) {
                    self.advance()?;
                    Some(res)
                } else {
                    None
                }
            }
            None => None,
        }
    }

    pub fn advance_while<F>(&mut self, p: F)
    where
        F: Fn(&char) -> bool,
    {
        while let Some(c) = self.peek() {
            if p(&c) {
                self.advance();
            } else {
                break;
            }
        }
    }

    pub fn eat_whitespace(&mut self) {
        self.advance_while(|c| c.is_whitespace());
    }

    pub fn scan_token(&mut self) -> Option<Result<Token, SyntaxError>> {
        self.eat_whitespace();
        let start = self.cursor;

        let c = self.advance()?;

        let token_kind = match c {
            '(' => TokenKind::LParen,
            ')' => TokenKind::RParen,
            '{' => TokenKind::LBrace,
            '}' => TokenKind::RBrace,
            '[' => TokenKind::LBracket,
            ']' => TokenKind::RBracket,
            ',' => TokenKind::Comma,
            '+' => TokenKind::Operator(Operator::Plus),
            '*' => TokenKind::Operator(Operator::Star),
            ';' => TokenKind::Semi,
            '-' => self
                .map_if(|p| p == '>', TokenKind::ThinArrow)
                .unwrap_or(TokenKind::Operator(Operator::Minus)),
            '|' => self
                .map_if(|p| p == '|', TokenKind::Operator(Operator::Or))
                .unwrap_or(TokenKind::Sep),
            '!' => self
                .map_if(|p| p == '=', TokenKind::Keyword(Keyword::Range))
                .unwrap_or(TokenKind::Operator(Operator::Not)),
            '<' => self
                .map_if(|p| p == '=', TokenKind::Operator(Operator::LessEq))
                .unwrap_or(TokenKind::Operator(Operator::Less)),
            '>' => self
                .map_if(|p| p == '=', TokenKind::Operator(Operator::GreaterEq))
                .unwrap_or(TokenKind::Operator(Operator::Greater)),
            '=' => self
                .map_if(|p| p == '=', TokenKind::Operator(Operator::EqEq))
                .unwrap_or(TokenKind::Eq),
            '.' => self
                .map_if(|p| p == '.', TokenKind::Keyword(Keyword::Range))
                .unwrap_or(TokenKind::Dot),
            ':' => match self.peek() {
                Some(':') => {
                    self.advance();
                    TokenKind::PathSep
                }
                Some('=') => {
                    self.advance();
                    TokenKind::ColonEq
                }
                _ => TokenKind::Colon,
            },
            '"' => match self.string(start) {
                Ok(tk) => tk,
                Err(err) => return Some(Err(err)),
            },
            '/' => {
                // if we find a comment we can skip until we find a new line
                if let Some('/') = self.peek() {
                    self.advance_while(|&c| c != '\n');
                    self.advance();
                    TokenKind::Comment
                } else {
                    TokenKind::Operator(Operator::Slash)
                }
            }

            '_' => match self.peek().unwrap() {
                'a'..='z' | 'A'..='Z' => self.ident(start),
                _ => TokenKind::Underscore,
            },

            _ if c.is_digit(10) => match self.number(start) {
                Ok(tk) => tk,
                Err(err) => return Some(Err(err)),
            },
            'a'..='z' | 'A'..='Z' => self.ident(start),
            c => return Some(Err(SyntaxError::UnexpectedChar(c, self.line))),
        };
        let token = self.yield_token(start, token_kind);
        Some(Ok(token))
    }

    fn yield_token(&mut self, start: usize, kind: TokenKind) -> Token {
        let lexeme = self.sub_string(start);
        let len = lexeme.len();
        let span = Span::new(start, (start + len) - 1);
        Token { kind, span }
    }

    fn sub_string(&mut self, start: usize) -> String {
        // TODO(Simon): working with unicode strings is hard, this does probably not work with non ascii utf-8 strings
        self.buffer[start..self.cursor].to_string()
    }

    fn string(&mut self, start: usize) -> Result<TokenKind, SyntaxError> {
        self.advance_while(|&c| c != '"');
        if self.is_at_end() {
            return Err(SyntaxError::UnterminatedString(self.cursor));
        }
        // consume trailing "
        self.advance();
        let literal = self.sub_string(start);
        Ok(TokenKind::Literal(Literal::String(literal)))
    }

    fn number(&mut self, start: usize) -> Result<TokenKind, SyntaxError> {
        self.advance_while(|&c| c.is_digit(10));
        if let Some('.') = self.peek() {
            // we found a . but no numbers after it
            if self.peek_next().map(|c| !c.is_digit(10)).unwrap_or(true) {
                return Err(SyntaxError::UnexpectedChar('.', self.line));
            }
            self.advance();
            self.advance_while(|c| c.is_digit(10));
        }
        let num = self.buffer[start..self.cursor].parse::<f64>().unwrap();
        Ok(TokenKind::Literal(Literal::Number(num)))
    }

    fn ident(&mut self, start: usize) -> TokenKind {
        self.advance_while(|&c| {
            ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z') || ('0' <= c && c <= '9') || c == '_'
        });
        let lexeme = self.sub_string(start);
        str::parse::<Keyword>(&lexeme)
            .map(TokenKind::Keyword)
            .map_err(|_| str::parse::<Operator>(&lexeme))
            .map_err(|_| str::parse::<Literal>(&lexeme))
            // FIXME(Simon): this should be fixed, cloning the ident lexeme every time we construct one seems really wasteful,
            // FIXME(Simon): But I am tired and don't know how to fix this right now
            .unwrap_or(TokenKind::Ident(lexeme.to_string())) // FIXME(Simon): this should be fixed we don't need to clone the string for every
    }

    fn is_at_end(&mut self) -> bool {
        self.peek().is_none()
    }
}

impl Iterator for Lexer {
    type Item = Result<Token, SyntaxError>;
    fn next(&mut self) -> Option<Self::Item> {
        while let Some(item) = self.scan_token() {
            match item {
                Ok(t) => {
                    if t.kind != TokenKind::Comment {
                        return Some(Ok(t));
                    }
                }
                Err(e) => return Some(Err(e)),
            }
        }
        None
    }
}
