use std::iter::*;
use std::vec::IntoIter;

use super::ast::*;
use super::errors::*;
use super::lexer::*;

pub struct Parser {
    iter: Peekable<IntoIter<Token>>,
}

macro_rules! __bin_op_rule (
	($name:ident, $inner:ident, $kind:ident, $($op_pattern:pat)|*) => (
		fn $name(&mut self) -> Result<Expr, SyntaxError> {
			let mut lhs = self.$inner()?;
			while let Ok(tk) = self.peek_kind() {
				let op = match tk {
					$($op_pattern)|* => self.advance()?,
					_ => break,
				};
				let rhs = self.$inner()?;
				let span = lhs.span.combine(&rhs.span);
				lhs = Expr {
					node: ExprKind::$kind(lhs, rhs, op.kind),
					span,
				};
			}
			Ok(lhs)
		}
	);
);

macro_rules! logical_impl (
	($name:ident, $inner:ident, $($op_pattern:pat)|*) => (
		__bin_op_rule!($name, $inner, logical, $($op_pattern)|*);
	);
);
macro_rules! binary_impl (
	($name:ident, $inner:ident, $($op_pattern:pat)|*) => (
		__bin_op_rule!($name, $inner, binary, $($op_pattern)|*);
	);
);

type ParseResult<T> = Result<T, SyntaxError>;

impl Parser {
    pub fn new(i: Vec<Token>) -> Self {
        Parser {
            iter: i.into_iter().peekable(),
        }
    }

    pub fn parse_struct_decl(&mut self) -> ParseResult<Stmt> {
        let start_span = self
            .expect(TokenKind::Keyword(Keyword::Struct), "TypenDeclaration")?
            .span;

        self.expect(TokenKind::Colon, "TypenDeclaration")?;
        let name = self.expect(TokenKind::Ident, "Typendeclaration")?;

        let mut fields = Vec::new();

        self.expect(TokenKind::LBrace, "Typenname")?;

        while self.peek_kind()? != TokenKind::RBrace {
            let name = self.expect(TokenKind::Ident, "Feldname")?;
            self.expect(TokenKind::Colon, "feldname")?;
            let ty = self.parse_ty_specifier()?;

            let span = name.span.combine(&ty.span);
            fields.push(Field::new(name, ty, span));

            match self.peek_kind()? {
                TokenKind::RBrace => break,
                _ => self.expect(TokenKind::Comma, "feld")?,
            };
        }
        let end_span = self.expect(TokenKind::RBrace, "TypenDeclaration")?.span;

        Ok(Stmt::StructDecl(StructDecl {
            name,
            fields,
            span: start_span.combine(&end_span),
        }))
    }

    fn parse_ty_kind(&mut self) -> ParseResult<TyKind> {
        match self.peek_kind()? {
            TokenKind::LBracket => {
                let ty = self.parse_ty_kind()?;
                self.expect(TokenKind::RBracket, "Feldelementtyp")?;
                Ok(TyKind::Array(Box::new(ty)))
            }
            TokenKind::LParen => {
                self.advance()?;

                let mut elems = Vec::new();

                loop {
                    let ty = self.parse_ty_kind()?;
                    elems.push(ty);
                    match self.peek_kind()? {
                        TokenKind::RParen => break,
                        _ => self.expect(TokenKind::Comma, "Tupleelement")?,
                    };
                }

                self.expect(TokenKind::RParen, "Tuple")?;
                Ok(TyKind::Tup(elems))
            }
            TokenKind::Ident => {
                let path = self.parse_path()?;
                Ok(TyKind::Path(path))
            }
            _ => Err(SyntaxError::UnexpectedEOF),
        }
    }

    fn parse_ty_specifier(&mut self) -> ParseResult<Ty> {
        let start = self.peek()?.span;
        let kind = self.parse_ty_kind()?;
        let end = self.peek()?.span;
        Ok(Ty {
            kind,
            span: start.combine(&end),
        })
    }

    fn parse_path(&mut self) -> ParseResult<Path> {
        let mut segments = Vec::new();

        while self.peek_kind()? == TokenKind::Ident {
            let fraq = self.advance()?;
            segments.push(fraq);

            match self.peek_kind()? {
                TokenKind::PathSep => {
                    self.advance()?;
                }
                _ => break,
            }
        }

        let first = segments.first().ok_or(SyntaxError::UnexpectedEOF)?.span;
        let last = segments.last().ok_or(SyntaxError::UnexpectedEOF)?.span;

        Ok(Path::new(segments, first.combine(&last)))
    }

    logical_impl!(parse_and, parse_eq, TokenKind::Operator(Operator::And));
    // equality   → comparison ( ( "!=" | "==" ) comparison )*
    logical_impl!(
        parse_eq,
        parse_cmp,
        TokenKind::Operator(Operator::EqEq) | TokenKind::Operator(Operator::NotEq)
    );
    // comparison → term ( ( ">" | ">=" | "<" | "<=" ) term )*
    binary_impl!(
        parse_cmp,
        parse_term,
        TokenKind::Operator(Operator::Greater)
            | TokenKind::Operator(Operator::GreaterEq)
            | TokenKind::Operator(Operator::Less)
            | TokenKind::Operator(Operator::LessEq)
    );
    // term       → factor ( ( "-" | "+" ) factor )*
    binary_impl!(
        parse_term,
        parse_factor,
        TokenKind::Operator(Operator::Plus) | TokenKind::Operator(Operator::Minus)
    );
    // factor     → unary ( ( "/" | "*" ) unary )*
    binary_impl!(
        parse_factor,
        parse_unary,
        TokenKind::Operator(Operator::Slash) | TokenKind::Operator(Operator::Star)
    );
    pub fn parse_expr(&mut self) -> Result<Expr, SyntaxError> {
        self.parse_and()
    }

    fn parse_unary(&mut self) -> Result<Expr, SyntaxError> {
        match self.peek_kind()? {
            TokenKind::Operator(Operator::Not) | TokenKind::Operator(Operator::Minus) => {
                let op = self.advance().unwrap(); // can never fail because we peeked ahaed to get here
                let rhs = self.parse_unary()?;
                let span = op.span.combine(&rhs.span);
                Ok(Expr {
                    node: ExprKind::unary(rhs, op.kind),
                    span,
                })
            }
            _ => self.parse_call(),
        }
    }

    fn parse_primary(&mut self) -> Result<Expr, SyntaxError> {
        match self.peek_kind()? {
            TokenKind::Keyword(Keyword::This) => {
                let var = Variable::new_local("selbst");
                let span = self.advance()?.span;
                let node = ExprKind::This(var, span);
                Ok(Expr { node, span })
            }
            TokenKind::Literal(l) => {
                let span = self.advance()?.span;
                Ok(Expr {
                    node: ExprKind::Literal(l, span),
                    span,
                })
            }
            TokenKind::LParen => {
                let l_paren = self.advance()?;
                let mut values = Vec::new();
                while self.peek_kind()? != TokenKind::RParen {
                    values.push(self.parse_expr()?);
                    if self.peek_kind()? == TokenKind::RParen {
                        break;
                    } else {
                        self.expect(TokenKind::Comma, "ausdruck")?;
                    }
                }
                Ok(Expr {
                    node: ExprKind::Tup(values),
                    span: l_paren.span.combine(&self.advance()?.span),
                })
            }
            TokenKind::Ident => {
                let token = self.advance()?;
                let var = Variable::new_global(token.lexeme.as_str());
                Ok(Expr {
                    node: ExprKind::Variable(var),
                    span: token.span,
                })
            }
            _ => Err(SyntaxError::UnexpectedEOF),
        }
    }

    fn parse_call(&mut self) -> Result<Expr, SyntaxError> {
        let mut expr = self.parse_primary()?;
        loop {
            match self.peek_kind()? {
                TokenKind::LParen => {
                    self.advance()?;
                    expr = self.finish_call(expr)?;
                }
                TokenKind::Dot => {
                    let token = self.advance()?;
                    let name = self.expect(TokenKind::Ident, "'.'")?;
                    let ident = Ident {
                        name: name.lexeme.clone(), // FIXME
                        span: token.span.combine(&name.span),
                    };
                    let node = ExprKind::field(expr, ident);
                    expr = Expr {
                        node,
                        span: token.span,
                    };
                }
                _ => break,
            }
        }
        Ok(expr)
    }

    fn finish_call(&mut self, callee: Expr) -> Result<Expr, SyntaxError> {
        let mut args = Vec::new();
        while self.peek_kind()? != TokenKind::RParen {
            args.push(self.parse_expr()?);
            if self.peek_kind()? == TokenKind::RParen {
                break;
            } else {
                self.expect(TokenKind::Comma, "Argument")?;
            }
        }
        let paren = self.expect(TokenKind::RParen, "argumente")?;
        Ok(Expr {
            span: callee.span.combine(&paren.span),
            node: ExprKind::call(callee, args),
        })
    }

    fn peek_kind(&mut self) -> Result<TokenKind, SyntaxError> {
        // maybe we can remove this clone, although I doubt it because of the string fields
        match self.iter.peek() {
            Some(t) => Ok(t.kind.clone()),
            None => Ok(TokenKind::EOF),
        }
    }

    fn peek(&mut self) -> ParseResult<Token> {
        self.iter.peek().cloned().ok_or(SyntaxError::UnexpectedEOF)
    }

    fn advance(&mut self) -> Result<Token, SyntaxError> {
        self.iter.next().ok_or(SyntaxError::UnexpectedEOF)
    }

    fn expect(&mut self, expected: TokenKind, before: &'static str) -> Result<Token, SyntaxError> {
        if self.peek_kind()? == expected {
            self.advance()
        } else {
            Err(SyntaxError::Missing(expected.to_string(), before))
        }
    }
}
