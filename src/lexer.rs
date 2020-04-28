use std::fmt;
use std::iter::*;
use std::str::Chars;
use std::str::FromStr;

use super::errors::*;
use crate::ast::Span;
use itertools::multipeek;
use itertools::*;

#[derive(PartialEq, Eq, Debug, Clone)]
pub enum TokenKind {
    Ident(String),

    Keyword(Keyword),

    Comment,

    // Values for internally supported types
    Lit(Lit),

    PathSep,
    Sep,

    Nl,

    // Delimiters
    LBrace,
    RBrace,
    LParen,
    RParen,
    LBracket,
    RBracket,

    Dollar,

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
    FatArrow,
    EOF,
}

impl fmt::Display for TokenKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let str = match self {
            TokenKind::Ident(id) => id,
            TokenKind::Keyword(kw) => kw.as_str(),
            TokenKind::Comment => "//",
            TokenKind::Lit(l) => l.as_str(),
            TokenKind::PathSep => "::",
            TokenKind::Nl => "Zeilenumbruch",
            TokenKind::LBrace => "{",
            TokenKind::RBrace => "}",
            TokenKind::LParen => "(",
            TokenKind::RParen => ")",
            TokenKind::LBracket => "[",
            TokenKind::RBracket => "]",
            TokenKind::Dollar => "$",
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
            TokenKind::FatArrow => "=>",
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

    Range,

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
            Operator::Range => "bis",
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
            ".." | "bis" => Ok(Operator::Range),
            "nicht" | "!" => Ok(Operator::Not),
            "und" | "&&" => Ok(Operator::And),
            "oder" | "||" => Ok(Operator::Or),
            "ungleich" | "!=" => Ok(Operator::NotEq),
            "gleich" | "==" => Ok(Operator::EqEq),
            "groesser_gleich" | ">=" => Ok(Operator::GreaterEq),
            "groesser" | ">" => Ok(Operator::Greater),
            "kleiner" | "<" => Ok(Operator::Less),
            "kleiner_gleich" | "<=" => Ok(Operator::LessEq),
            _ => Err(()),
        }
    }
}

#[derive(PartialEq, Debug, Clone)]
pub enum Lit {
    String(String),
    Number(f64),
    Bool(bool),
}

impl Eq for Lit {}

impl Lit {
    fn as_str(&self) -> &'static str {
        match self {
            Self::String(_) => "Textliteral",
            Self::Number(_) => "Zahlenliteral",
            Self::Bool(_) => "Boolliteral",
        }
    }
}

impl FromStr for Lit {
    type Err = ();

    // NOTE(Simon): we just match bool litearl here to avoid the added performance cost of checking for a string or a number
    // each time we build a token, we already do this in the scan_token fn of the lexer
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "wahr" => Ok(Self::Bool(true)),
            "falsch" => Ok(Self::Bool(false)),
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
    Continue,
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
            Keyword::Continue => "weiter",
            Keyword::Break => "stop",
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
            "wenn" => Ok(Keyword::If),
            "dann" => Ok(Keyword::Then),
            "sonst" => Ok(Keyword::Else),
            "stop" => Ok(Keyword::Break),
            "weiter" => Ok(Keyword::Continue),
            _ => Err(()),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
}

pub struct Lexer<'a> {
    iter: MultiPeek<Chars<'a>>,
    src_buf: &'a str,
    cursor: usize,
}

impl<'a> Lexer<'a> {
    pub fn new(data: &'a str) -> Self {
        Lexer {
            iter: multipeek(data.chars()),
            src_buf: data,
            cursor: 0,
        }
    }
    fn advance(&mut self) -> Option<char> {
        let c = self.iter.next();
        self.cursor += 1;
        c
    }

    pub fn peek(&mut self) -> Option<char> {
        let elem = self.iter.peek().cloned();
        self.iter.reset_peek();
        elem
    }

    fn peek_next(&mut self) -> Option<char> {
        self.iter.peek();
        let elem = self.iter.peek().cloned();
        self.iter.reset_peek();
        elem
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

    fn eat_whitespace(&mut self) {
        self.advance_while(|c| should_skip(c));
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
            '\n' => TokenKind::Nl,
            '[' => TokenKind::LBracket,
            ']' => TokenKind::RBracket,
            ',' => TokenKind::Comma,
            '+' => TokenKind::Operator(Operator::Plus),
            '*' => TokenKind::Operator(Operator::Star),
            ';' => TokenKind::Semi,
            '$' => TokenKind::Dollar,
            '-' => self
                .map_if(|p| p == '>', TokenKind::ThinArrow)
                .unwrap_or(TokenKind::Operator(Operator::Minus)),
            '|' => self
                .map_if(|p| p == '|', TokenKind::Operator(Operator::Or))
                .unwrap_or(TokenKind::Sep),
            '!' => self
                .map_if(|p| p == '=', TokenKind::Operator(Operator::NotEq))
                .unwrap_or(TokenKind::Operator(Operator::Not)),
            '<' => self
                .map_if(|p| p == '=', TokenKind::Operator(Operator::LessEq))
                .unwrap_or(TokenKind::Operator(Operator::Less)),
            '>' => self
                .map_if(|p| p == '=', TokenKind::Operator(Operator::GreaterEq))
                .unwrap_or(TokenKind::Operator(Operator::Greater)),
            '.' => self
                .map_if(|p| p == '.', TokenKind::Operator(Operator::Range))
                .unwrap_or(TokenKind::Dot),
            '=' => match self.peek() {
                Some('=') => {
                    self.advance()?;
                    TokenKind::Operator(Operator::EqEq)
                }
                Some('>') => {
                    self.advance()?;
                    TokenKind::FatArrow
                }
                _ => TokenKind::Eq,
            },
            ':' => match self.peek() {
                Some(':') => {
                    self.advance()?;
                    TokenKind::PathSep
                }
                Some('=') => {
                    self.advance()?;
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
            '&' => match self.peek() {
                Some('&') => {
                    self.advance()?;
                    TokenKind::Operator(Operator::And)
                }
                // TODO(Simon): we should just return a more specific error and hinting at the use of th keyword operators
                // NOTE(Simon): binary AND is not allowed in this language
                _ => return Some(Err(SyntaxError::UnexpectedChar(c, start))),
            },
            c => return Some(Err(SyntaxError::UnexpectedChar(c, start))),
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
        self.src_buf[start..self.cursor].to_string()
    }

    fn string(&mut self, start: usize) -> Result<TokenKind, SyntaxError> {
        self.advance_while(|&c| c != '"');
        if self.is_at_end() {
            return Err(SyntaxError::UnterminatedString(self.cursor));
        }
        // consume trailing "
        self.advance();
        let lit = self.sub_string(start);
        Ok(TokenKind::Lit(Lit::String(lit)))
    }

    fn number(&mut self, start: usize) -> Result<TokenKind, SyntaxError> {
        self.advance_while(|&c| c.is_digit(10));
        if let Some('.') = self.peek() {
            // if we find the range token we just bail out early and tokenize it on the next iteration
            // example: 3..10
            //          ^ first token, at this point we bail out and get the rest on a later iteration
            if let Some('.') = self.peek_next() {
                let num = self.src_buf[start..self.cursor].parse::<f64>().unwrap();
                return Ok(TokenKind::Lit(Lit::Number(num)));
            }

            // we found a . but no numbers after it
            if self.peek_next().map(|c| !c.is_digit(10)).unwrap_or(true) {
                return Err(SyntaxError::UnexpectedChar('.', start));
            }
            self.advance();
            self.advance_while(|c| c.is_digit(10));
        }
        let num = self.src_buf[start..self.cursor].parse::<f64>().unwrap();
        Ok(TokenKind::Lit(Lit::Number(num)))
    }

    fn ident(&mut self, start: usize) -> TokenKind {
        self.advance_while(|&c| {
            ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z') || ('0' <= c && c <= '9') || c == '_'
        });
        let lexeme = self.sub_string(start);

        // NOTE(Simon): we use or else because the argument only needs to be lazy evaluated if we get an err
        str::parse::<Keyword>(&lexeme)
            .map(TokenKind::Keyword)
            .or_else(|_| str::parse::<Operator>(&lexeme).map(TokenKind::Operator))
            .or_else(|_| str::parse::<Lit>(&lexeme).map(TokenKind::Lit))
            .unwrap_or(TokenKind::Ident(lexeme))
    }

    fn is_at_end(&mut self) -> bool {
        self.peek().is_none()
    }
}

impl Iterator for Lexer<'_> {
    type Item = Result<Token, SyntaxError>;
    fn next(&mut self) -> Option<Self::Item> {
        while let Some(item) = self.scan_token() {
            match item {
                Ok(t) if t.kind == TokenKind::Comment => (),
                Ok(_) | Err(_) => return Some(item),
            };
        }
        None
    }
}

fn should_skip(c: &char) -> bool {
    if *c == '\n' {
        false
    } else {
        c.is_whitespace()
    }
}

pub fn infer_semis(t_stream: Vec<Token>) -> Vec<Token> {
    let mut open_paren = 0;
    let mut open_bracket = 0;
    let mut t_buf = Vec::new();

    for t in t_stream {
        match t.kind {
            TokenKind::LParen => open_paren += 1,
            TokenKind::RParen => open_paren -= 1,
            TokenKind::LBracket => open_bracket += 1,
            TokenKind::RBracket => open_bracket -= 1,
            TokenKind::Nl if open_paren == 0 && open_bracket == 0 => {
                match t_buf.last() {
                    Some(Token {
                        kind: TokenKind::Semi,
                        span: _,
                    })
                    | Some(Token {
                        kind: TokenKind::LBrace,
                        span: _,
                    })
                    | Some(Token {
                        kind: TokenKind::RBrace,
                        span: _,
                    })
                    | Some(Token {
                        kind: TokenKind::Comma,
                        span: _,
                    })
                    | None => continue,
                    _ => {}
                };

                t_buf.push(Token {
                    kind: TokenKind::Semi,
                    span: t.span,
                });
                continue;
            }
            TokenKind::Nl => continue,
            _ => {}
        }
        t_buf.push(t)
    }
    t_buf
}

#[cfg(test)]
mod tests {

    use pretty_assertions::assert_eq;

    use super::*;

    fn assert_vec_eq(expected: Vec<TokenKind>, actual: Vec<TokenKind>) {
        assert_eq!(expected.len(), actual.len(), "len expected != actual len");
        expected
            .iter()
            .zip(actual.iter())
            .for_each(|(e, a)| assert_eq!(e, a));
    }

    #[test]
    fn lex_fn_header() {
        let test = "fn test(x: Zahl) -> [Text]";

        let actual = Lexer::new(&test)
            .map(|r| r.unwrap().kind)
            .collect::<Vec<_>>();

        let expected = vec![
            TokenKind::Keyword(Keyword::Fun),
            TokenKind::Ident("test".to_string()),
            TokenKind::LParen,
            TokenKind::Ident("x".to_string()),
            TokenKind::Colon,
            TokenKind::Ident("Zahl".to_string()),
            TokenKind::RParen,
            TokenKind::ThinArrow,
            TokenKind::LBracket,
            TokenKind::Ident("Text".to_string()),
            TokenKind::RBracket,
        ];

        assert_vec_eq(expected, actual);
    }
    #[test]
    fn lex_vardef_untyped() {
        let test = "a := 20;";

        let actual = Lexer::new(&test)
            .map(|r| r.unwrap().kind)
            .collect::<Vec<_>>();

        let expected = vec![
            TokenKind::Ident("a".to_string()),
            TokenKind::ColonEq,
            TokenKind::Lit(Lit::Number(20.0)),
            TokenKind::Semi,
        ];

        assert_vec_eq(expected, actual);
    }

    #[test]
    fn lex_vardef_typed() {
        let test = "a : [Zahl] = 20;";

        let actual = Lexer::new(&test)
            .map(|r| r.unwrap().kind)
            .collect::<Vec<_>>();

        let expected = vec![
            TokenKind::Ident("a".to_string()),
            TokenKind::Colon,
            TokenKind::LBracket,
            TokenKind::Ident("Zahl".to_string()),
            TokenKind::RBracket,
            TokenKind::Eq,
            TokenKind::Lit(Lit::Number(20.0)),
            TokenKind::Semi,
        ];

        assert_vec_eq(expected, actual);
    }

    #[test]
    fn lex_struct_decl() {
        let test = "typ Test {a: Foo, b: Bar}";

        let actual = Lexer::new(&test)
            .map(|r| r.unwrap().kind)
            .collect::<Vec<_>>();

        let expected = vec![
            TokenKind::Keyword(Keyword::Struct),
            TokenKind::Ident("Test".to_string()),
            TokenKind::LBrace,
            TokenKind::Ident("a".to_string()),
            TokenKind::Colon,
            TokenKind::Ident("Foo".to_string()),
            TokenKind::Comma,
            TokenKind::Ident("b".to_string()),
            TokenKind::Colon,
            TokenKind::Ident("Bar".to_string()),
            TokenKind::RBrace,
        ];

        assert_vec_eq(expected, actual);
    }

    #[test]
    fn lex_enum_decl() {
        let test = "typ Bool = Wahr | Falsch";

        let actual = Lexer::new(&test)
            .map(|r| r.unwrap().kind)
            .collect::<Vec<_>>();

        let expected = vec![
            TokenKind::Keyword(Keyword::Struct),
            TokenKind::Ident("Bool".to_string()),
            TokenKind::Eq,
            TokenKind::Ident("Wahr".to_string()),
            TokenKind::Sep,
            TokenKind::Ident("Falsch".to_string()),
        ];

        assert_vec_eq(expected, actual);
    }

    #[test]
    fn lex_impl_block_decl() {
        let test = "impl Foo {}";

        let actual = Lexer::new(&test)
            .map(|r| r.unwrap().kind)
            .collect::<Vec<_>>();

        let expected = vec![
            TokenKind::Keyword(Keyword::Impl),
            TokenKind::Ident("Foo".to_string()),
            TokenKind::LBrace,
            TokenKind::RBrace,
        ];

        assert_vec_eq(expected, actual);
    }

    #[test]
    fn lex_range_dotted_no_space() {
        let test = "0..10";

        let actual = Lexer::new(&test)
            .map(|r| r.unwrap().kind)
            .collect::<Vec<_>>();

        let expected = vec![
            TokenKind::Lit(Lit::Number(0.0)),
            TokenKind::Operator(Operator::Range),
            TokenKind::Lit(Lit::Number(10.0)),
        ];

        assert_vec_eq(expected, actual);
    }

    #[test]
    #[should_panic]
    fn lex_range_keyword_no_space_fail() {
        // this is not expected to work because we see 0 as a number and bis10 as an ident
        // Solution 1: would be to insert a space like so 0 bis 10.
        // Solution 2: use the dot operator for ranges: 0..10
        let test = "0bis10";

        let actual = Lexer::new(&test)
            .map(|r| r.unwrap().kind)
            .collect::<Vec<_>>();

        let expected = vec![
            TokenKind::Lit(Lit::Number(0.0)),
            TokenKind::Operator(Operator::Range),
            TokenKind::Lit(Lit::Number(10.0)),
        ];
        assert_vec_eq(expected, actual);
    }

    #[test]
    fn lex_range_keyword_space() {
        let test = "0 bis 10";

        let actual = Lexer::new(&test)
            .map(|r| r.unwrap().kind)
            .collect::<Vec<_>>();

        let expected = vec![
            TokenKind::Lit(Lit::Number(0.0)),
            TokenKind::Operator(Operator::Range),
            TokenKind::Lit(Lit::Number(10.0)),
        ];

        assert_vec_eq(expected, actual);
    }

    #[test]
    fn lex_range_dotted_space() {
        let test = "0 .. 10";

        let actual = Lexer::new(&test)
            .map(|r| r.unwrap().kind)
            .collect::<Vec<_>>();

        let expected = vec![
            TokenKind::Lit(Lit::Number(0.0)),
            TokenKind::Operator(Operator::Range),
            TokenKind::Lit(Lit::Number(10.0)),
        ];

        assert_vec_eq(expected, actual);
    }

    #[test]
    fn lex_number_int() {
        let test = "0 100 420 6969 3141";

        let actual = Lexer::new(&test)
            .map(|r| r.unwrap().kind)
            .collect::<Vec<_>>();

        let expected = vec![
            TokenKind::Lit(Lit::Number(0.0)),
            TokenKind::Lit(Lit::Number(100.0)),
            TokenKind::Lit(Lit::Number(420.0)),
            TokenKind::Lit(Lit::Number(6969.0)),
            TokenKind::Lit(Lit::Number(3141.0)),
        ];

        assert_vec_eq(expected, actual);
    }
    #[test]
    fn lex_number_float() {
        let test = "0.1 100.10 420.123 6969.2 3141.1";

        let actual = Lexer::new(&test)
            .map(|r| r.unwrap().kind)
            .collect::<Vec<_>>();

        let expected = vec![
            TokenKind::Lit(Lit::Number(0.1)),
            TokenKind::Lit(Lit::Number(100.10)),
            TokenKind::Lit(Lit::Number(420.123)),
            TokenKind::Lit(Lit::Number(6969.2)),
            TokenKind::Lit(Lit::Number(3141.1)),
        ];

        assert_vec_eq(expected, actual);
    }

    #[test]
    fn lex_expr_num_1() {
        let test = "-1-(a + 20)";

        let actual = Lexer::new(&test)
            .map(|r| r.unwrap().kind)
            .collect::<Vec<_>>();

        let expected = vec![
            TokenKind::Operator(Operator::Minus),
            TokenKind::Lit(Lit::Number(1.0)),
            TokenKind::Operator(Operator::Minus),
            TokenKind::LParen,
            TokenKind::Ident("a".to_string()),
            TokenKind::Operator(Operator::Plus),
            TokenKind::Lit(Lit::Number(20.0)),
            TokenKind::RParen,
        ];

        assert_vec_eq(expected, actual);
    }

    #[test]
    fn lex_expr_num_2() {
        let test = "-1-(a * 20 / 2)";

        let actual = Lexer::new(&test)
            .map(|r| r.unwrap().kind)
            .collect::<Vec<_>>();

        let expected = vec![
            TokenKind::Operator(Operator::Minus),
            TokenKind::Lit(Lit::Number(1.0)),
            TokenKind::Operator(Operator::Minus),
            TokenKind::LParen,
            TokenKind::Ident("a".to_string()),
            TokenKind::Operator(Operator::Star),
            TokenKind::Lit(Lit::Number(20.0)),
            TokenKind::Operator(Operator::Slash),
            TokenKind::Lit(Lit::Number(2.0)),
            TokenKind::RParen,
        ];

        assert_vec_eq(expected, actual);
    }

    #[test]
    fn lex_expr_num_comment() {
        let test = "-1-(a * 20 // 2)";

        let actual = Lexer::new(&test)
            .map(|r| r.unwrap().kind)
            .collect::<Vec<_>>();

        let expected = vec![
            TokenKind::Operator(Operator::Minus),
            TokenKind::Lit(Lit::Number(1.0)),
            TokenKind::Operator(Operator::Minus),
            TokenKind::LParen,
            TokenKind::Ident("a".to_string()),
            TokenKind::Operator(Operator::Star),
            TokenKind::Lit(Lit::Number(20.0)),
        ];

        assert_vec_eq(expected, actual);
    }

    #[test]
    fn lex_expr_and_op() {
        let test = "!wahr && falsch";

        let actual = Lexer::new(&test)
            .map(|r| r.unwrap().kind)
            .collect::<Vec<_>>();

        let expected = vec![
            TokenKind::Operator(Operator::Not),
            TokenKind::Lit(Lit::Bool(true)),
            TokenKind::Operator(Operator::And),
            TokenKind::Lit(Lit::Bool(false)),
        ];

        assert_vec_eq(expected, actual);
    }
    #[test]
    fn lex_expr_and_keyword() {
        let test = "!wahr und falsch";

        let actual = Lexer::new(&test)
            .map(|r| r.unwrap().kind)
            .collect::<Vec<_>>();
        let expected = vec![
            TokenKind::Operator(Operator::Not),
            TokenKind::Lit(Lit::Bool(true)),
            TokenKind::Operator(Operator::And),
            TokenKind::Lit(Lit::Bool(false)),
        ];

        assert_vec_eq(expected, actual);
    }
    #[test]
    fn lex_bool_ops() {
        let test = "und || && oder !nicht";

        let actual = Lexer::new(&test)
            .map(|r| r.unwrap().kind)
            .collect::<Vec<_>>();
        let expected = vec![
            TokenKind::Operator(Operator::And),
            TokenKind::Operator(Operator::Or),
            TokenKind::Operator(Operator::And),
            TokenKind::Operator(Operator::Or),
            TokenKind::Operator(Operator::Not),
            TokenKind::Operator(Operator::Not),
        ];

        assert_vec_eq(expected, actual);
    }

    #[test]
    fn lex_bool_ops_no_space() {
        let test = "und||&&oder!nicht";

        let actual = Lexer::new(&test)
            .map(|r| r.unwrap().kind)
            .collect::<Vec<_>>();
        let expected = vec![
            TokenKind::Operator(Operator::And),
            TokenKind::Operator(Operator::Or),
            TokenKind::Operator(Operator::And),
            TokenKind::Operator(Operator::Or),
            TokenKind::Operator(Operator::Not),
            TokenKind::Operator(Operator::Not),
        ];

        assert_vec_eq(expected, actual);
    }

    #[test]
    fn lex_math_ops() {
        let test = "+ - * /";

        let actual = Lexer::new(&test)
            .map(|r| r.unwrap().kind)
            .collect::<Vec<_>>();
        let expected = vec![
            TokenKind::Operator(Operator::Plus),
            TokenKind::Operator(Operator::Minus),
            TokenKind::Operator(Operator::Star),
            TokenKind::Operator(Operator::Slash),
        ];

        assert_vec_eq(expected, actual);
    }

    #[test]
    fn lex_math_ops_no_space() {
        let test = "+-/**/";

        let actual = Lexer::new(&test)
            .map(|r| r.unwrap().kind)
            .collect::<Vec<_>>();
        let expected = vec![
            TokenKind::Operator(Operator::Plus),
            TokenKind::Operator(Operator::Minus),
            TokenKind::Operator(Operator::Slash),
            TokenKind::Operator(Operator::Star),
            TokenKind::Operator(Operator::Star),
            TokenKind::Operator(Operator::Slash),
        ];

        assert_vec_eq(expected, actual);
    }

    #[test]
    fn lex_cmp_ops() {
        let test =
            "groesser_gleich ungleich != gleich  == > groesser < kleiner kleiner_gleich >= <= =>";

        let actual = Lexer::new(&test)
            .map(|r| r.unwrap().kind)
            .collect::<Vec<_>>();

        dbg!(&actual);

        let expected = vec![
            TokenKind::Operator(Operator::GreaterEq),
            TokenKind::Operator(Operator::NotEq),
            TokenKind::Operator(Operator::NotEq),
            TokenKind::Operator(Operator::EqEq),
            TokenKind::Operator(Operator::EqEq),
            TokenKind::Operator(Operator::Greater),
            TokenKind::Operator(Operator::Greater),
            TokenKind::Operator(Operator::Less),
            TokenKind::Operator(Operator::Less),
            TokenKind::Operator(Operator::LessEq),
            TokenKind::Operator(Operator::GreaterEq),
            TokenKind::Operator(Operator::LessEq),
            TokenKind::FatArrow,
        ];

        assert_vec_eq(expected, actual);
    }

    #[test]
    fn lex_keywords() {
        let test =
            "funktion fun fn typ Typ selbst solange rueckgabe fuer bis wenn dann sonst stop weiter";

        let actual = Lexer::new(&test)
            .map(|r| r.unwrap().kind)
            .collect::<Vec<_>>();

        dbg!(&actual);

        let expected = vec![
            TokenKind::Keyword(Keyword::Fun),
            TokenKind::Keyword(Keyword::Fun),
            TokenKind::Keyword(Keyword::Fun),
            TokenKind::Keyword(Keyword::Struct),
            TokenKind::Keyword(Keyword::Struct),
            TokenKind::Keyword(Keyword::This),
            TokenKind::Keyword(Keyword::While),
            TokenKind::Keyword(Keyword::Return),
            TokenKind::Keyword(Keyword::For),
            TokenKind::Operator(Operator::Range),
            TokenKind::Keyword(Keyword::If),
            TokenKind::Keyword(Keyword::Then),
            TokenKind::Keyword(Keyword::Else),
            TokenKind::Keyword(Keyword::Break),
            TokenKind::Keyword(Keyword::Continue),
        ];

        assert_vec_eq(expected, actual);
    }
    #[test]
    fn lex_punctuation_tokens() {
        let test = ":: : {} () [] | || , ; . .. = _ := ->";

        let actual = Lexer::new(&test)
            .map(|r| r.unwrap().kind)
            .collect::<Vec<_>>();
        let expected = vec![
            TokenKind::PathSep,
            TokenKind::Colon,
            TokenKind::LBrace,
            TokenKind::RBrace,
            TokenKind::LParen,
            TokenKind::RParen,
            TokenKind::LBracket,
            TokenKind::RBracket,
            TokenKind::Sep,
            TokenKind::Operator(Operator::Or),
            TokenKind::Comma,
            TokenKind::Semi,
            TokenKind::Dot,
            TokenKind::Operator(Operator::Range),
            TokenKind::Eq,
            TokenKind::Underscore,
            TokenKind::ColonEq,
            TokenKind::ThinArrow,
        ];

        assert_vec_eq(expected, actual);
    }

    #[test]
    fn lex_idents() {
        let test = "foo bar_10 test_1_1 bar__f00 D3ADB33F 10A";

        let actual = Lexer::new(&test)
            .map(|r| r.unwrap().kind)
            .collect::<Vec<_>>();
        let expected = vec![
            TokenKind::Ident("foo".to_string()),
            TokenKind::Ident("bar_10".to_string()),
            TokenKind::Ident("test_1_1".to_string()),
            TokenKind::Ident("bar__f00".to_string()),
            TokenKind::Ident("D3ADB33F".to_string()),
            TokenKind::Lit(Lit::Number(10.0)),
            TokenKind::Ident("A".to_string()),
        ];

        assert_vec_eq(expected, actual);
    }

    #[test]
    fn lex_poly_array_ty() {
        let test = "[$T]";

        let actual = Lexer::new(&test)
            .map(|r| r.unwrap().kind)
            .collect::<Vec<_>>();
        let expected = vec![
            TokenKind::LBracket,
            TokenKind::Dollar,
            TokenKind::Ident("T".to_string()),
            TokenKind::RBracket,
        ];
        assert_vec_eq(expected, actual);
    }
}
