use std::iter::*;
use std::vec::IntoIter;

use itertools::multipeek;
use itertools::*;

use super::ast::*;
use super::errors::*;
use super::lexer::*;

pub struct Parser {
    iter: MultiPeek<IntoIter<Token>>,
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
					ty: Ty::default_infer_type(span.clone()),
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
            iter: multipeek(i.into_iter()),
        }
    }

    fn sync_parser_state(&mut self) {
        while let Ok(tk) = self.peek_kind() {
            match tk {
                TokenKind::Semi => {
                    self.advance().unwrap();
                    return;
                }
                TokenKind::Keyword(Keyword::Struct)
                | TokenKind::Keyword(Keyword::Fun)
                | TokenKind::Keyword(Keyword::For)
                | TokenKind::Keyword(Keyword::If)
                | TokenKind::Keyword(Keyword::While)
                | TokenKind::Keyword(Keyword::Return)
                | TokenKind::EOF => return,
                _ => self.advance().unwrap(),
            };
        }
    }

    pub fn parse(&mut self) -> ParseResult<Stmt> {
        self.parse_decl()
    }

    fn parse_decl(&mut self) -> ParseResult<Stmt> {
        match self.peek_kind()? {
            TokenKind::Keyword(Keyword::Struct) => self.parse_ty_decl(),
            TokenKind::Keyword(Keyword::Fun) => self.parse_fn_decl(),
            TokenKind::Keyword(Keyword::Impl) => self.parse_impl_block(),
            _ => panic!("invalide declaration {:#?}", self.peek()),
        }
    }

    fn parse_ty_decl(&mut self) -> ParseResult<Stmt> {
        self.iter.peek();
        self.iter.peek();
        match self.iter.peek().unwrap().kind {
            TokenKind::LBrace => {
                self.iter.reset_peek();
                self.parse_struct_decl()
            }
            TokenKind::Eq => {
                self.iter.reset_peek();
                self.parse_enum_decl()
            }
            _ => panic!("invalider token nach typendeclaration"),
        }
    }

    pub fn parse_fn_header(&mut self) -> ParseResult<FnSig> {
        self.expect(TokenKind::Keyword(Keyword::Fun), "Funktionsdeklaration")?;
        let name: Ident = self
            .expect(TokenKind::Ident, "Funktionsschluesselwort")?
            .into();

        self.expect(TokenKind::LParen, "Funktionsnamen")?;
        let mut params = Vec::new();
        while self.peek_kind()? != TokenKind::RParen {
            let p_name: Ident = self.expect(TokenKind::Ident, "parameter")?.into();
            self.expect(TokenKind::Colon, "Parametername")?;
            let p_ty = self.parse_ty_specifier()?;

            params.push((p_name, p_ty));

            match self.peek_kind()? {
                TokenKind::RParen => break,
                _ => self.expect(TokenKind::Comma, "Functionsparameter")?,
            };
        }
        let closing = self.expect(TokenKind::RParen, "Rueckgabetyp")?;
        let ret_ty = match self.peek_kind()? {
            TokenKind::ThinArrow => {
                self.advance()?;
                self.parse_ty_specifier()?
            }
            _ => Ty::default_unit_type(closing.span),
        };
        Ok(FnSig::new(name, params, ret_ty))
    }

    pub fn parse_fn_decl(&mut self) -> ParseResult<Stmt> {
        let fn_head = self.parse_fn_header()?;
        let body = self.parse_block(false)?;

        Ok(Stmt::FnDecl(FnDecl::new(fn_head, body)))
    }

    fn parse_block(&mut self, break_allowed: bool) -> ParseResult<Block> {
        let start = self.expect(TokenKind::LBrace, "{ vor Block erwartet")?.span;

        let mut block = Vec::new();
        while self.peek_kind()? != TokenKind::RBrace {
            let stmt = match self.peek_kind()? {
                TokenKind::Ident => self.parse_expr_stmt_or_vardef()?,
                TokenKind::Keyword(Keyword::This) => self.parse_expr_stmt()?,
                TokenKind::Keyword(Keyword::While) => self.parse_while_loop()?,
                TokenKind::Keyword(Keyword::For) => self.parse_for_loop()?,
                TokenKind::Keyword(Keyword::Return) => self.parse_return()?,
                TokenKind::Keyword(Keyword::Break) => self.parse_break(break_allowed)?,
                TokenKind::Keyword(Keyword::If) => self.parse_if()?,
                TokenKind::LBrace => Stmt::Block(self.parse_block(break_allowed)?),
                _ => todo!(), // report error because of unknown token
            };
            block.push(stmt);
        }
        let end = self
            .expect(TokenKind::RBrace, "Block nicht geschlossen?")?
            .span;
        Ok(Block::new(block, start.combine(&end)))
    }

    fn parse_while_loop(&mut self) -> ParseResult<Stmt> {
        self.expect(TokenKind::Keyword(Keyword::While), "Solange")?;

        let cond = self.parse_expr()?;
        let body = self.parse_block(true)?;

        Ok(Stmt::While(cond, body))
    }

    fn parse_for_loop(&mut self) -> ParseResult<Stmt> {
        let start = self.expect(TokenKind::Keyword(Keyword::For), "Fuer")?.span;

        let loop_var: Ident = self.expect(TokenKind::Ident, "loopvar")?.into();
        self.expect(TokenKind::ColonEq, "loop")?;

        let it = self.parse_expr()?; // this has to be a range expr like (20..20) or an expr with type array
        let body = self.parse_block(true)?;
        let span = start.combine(&body.span);
        let f_loop = ForLoop::new(it, loop_var, body, span);
        Ok(Stmt::For(f_loop))
    }

    fn parse_if(&mut self) -> ParseResult<Stmt> {
        todo!()
    }

    fn parse_return(&mut self) -> ParseResult<Stmt> {
        let start = self
            .expect(
                TokenKind::Keyword(Keyword::Return),
                "Rueckgabe schluesselwort",
            )?
            .span;
        let ret_val = match self.peek_kind()? {
            TokenKind::Semi => Expr::empty(start),
            _ => self.parse_expr()?,
        };
        let end = self
            .expect(TokenKind::Semi, "; nach rueckgabe erwartet")?
            .span;
        Ok(Stmt::Ret(ret_val, start.combine(&end)))
    }

    fn parse_expr_stmt_or_vardef(&mut self) -> ParseResult<Stmt> {
        if self.next_is_vardef() {
            self.parse_vardef()
        } else {
            self.parse_expr_stmt()
        }
    }

    fn next_is_vardef(&mut self) -> bool {
        while let Some(t) = self.iter.peek() {
            match t.kind {
                TokenKind::ColonEq | TokenKind::Eq | TokenKind::Colon => {
                    self.iter.reset_peek();
                    return true;
                }
                _ => continue,
            };
        }
        self.iter.reset_peek();
        false
    }

    fn parse_vardef(&mut self) -> ParseResult<Stmt> {
        let target = self.parse_vardef_target()?;
        let ty = match self.peek_kind()? {
            TokenKind::ColonEq => {
                // user has not provided a type, we will try to infer it later during type inference
                self.advance()?;
                None
            }
            TokenKind::Colon => {
                // user has provided a concrete type, we will validate during type anlysis
                self.advance()?;
                Some(self.parse_ty_specifier()?)
            }
            _ => {
                eprintln!("failed to parse vardef type");
                return Err(SyntaxError::UnexpectedEOF);
            }
        };

        let init = self.parse_expr()?;

        let end = self
            .expect(TokenKind::Semi, "Semicolon vor variablen Definition")?
            .span;

        let span = target.span.combine(&end);
        let local = Local::new(init, target, ty, span);

        Ok(Stmt::Local(Box::new(local)))
    }

    fn parse_vardef_target(&mut self) -> ParseResult<Path> {
        self.parse_path()
    }

    fn parse_expr_stmt(&mut self) -> ParseResult<Stmt> {
        let expr = self.parse_expr()?;
        self.expect(TokenKind::Semi, "Semicolon nach Ausdruck vergessen")?;
        Ok(Stmt::Expr(expr))
    }

    fn parse_break(&mut self, break_allowed: bool) -> ParseResult<Stmt> {
        if !break_allowed {
            return Err(SyntaxError::BreakOutsideLoop);
        }

        self.expect(TokenKind::Keyword(Keyword::Break), "Stop befehl")?;
        self.expect(TokenKind::Semi, "Stop")?;
        Ok(Stmt::Break)
    }

    fn parse_impl_block(&mut self) -> ParseResult<Stmt> {
        todo!()
    }

    pub fn parse_struct_decl(&mut self) -> ParseResult<Stmt> {
        let start_span = self
            .expect(TokenKind::Keyword(Keyword::Struct), "TypenDeclaration")?
            .span;
        let struct_name = self.expect(TokenKind::Ident, "TypenDeclaration")?;

        let mut fields = Vec::new();

        self.expect(TokenKind::LBrace, "Typenname")?;

        while self.peek_kind()? != TokenKind::RBrace {
            let name = self.expect(TokenKind::Ident, "Feldname")?;
            self.expect(TokenKind::Colon, "feldname")?;
            let ty = self.parse_ty_specifier()?;

            let span = name.span.combine(&ty.span);
            let name = Ident::new(name.lexeme, name.span);
            fields.push(Field::new(name, ty, span));

            match self.peek_kind()? {
                TokenKind::RBrace => break,
                _ => self.expect(TokenKind::Comma, "feld")?,
            };
        }
        let end_span = self.expect(TokenKind::RBrace, "TypenDeclaration")?.span;
        let struct_name = Ident::new(struct_name.lexeme, struct_name.span);
        Ok(Stmt::StructDecl(StructDecl {
            name: struct_name,
            fields,
            span: start_span.combine(&end_span),
        }))
    }

    fn parse_enum_decl(&mut self) -> ParseResult<Stmt> {
        let start = self
            .expect(
                TokenKind::Keyword(Keyword::Struct),
                "enum or struct declaration",
            )?
            .span;
        let name: Ident = self.expect(TokenKind::Ident, "Enum Name")?.into();
        self.expect(TokenKind::Eq, "EnumDecl")?;
        let mut variants = Vec::new();
        loop {
            match self.peek_kind()? {
                TokenKind::Sep => variants.push(self.parse_enum_variant()?),
                _ => break,
            };
        }
        let end = start.combine(&variants.last().unwrap().span); // TODO(Simon): provide better error if enum has no fields
        let decl = EnumDecl::new(name, variants, start.combine(&end));
        Ok(Stmt::EnumDecl(decl))
    }

    fn parse_enum_variant(&mut self) -> ParseResult<Variant> {
        let start = self.expect(TokenKind::Sep, "enum variante")?.span;
        let ident: Ident = self.expect(TokenKind::Ident, "Feldname")?.into();
        let (data, end) = match self.peek_kind()? {
            TokenKind::LParen => {
                self.advance()?;
                let mut elems = Vec::new();
                loop {
                    match self.peek_kind()? {
                        TokenKind::RParen => break,
                        _ => elems.push(self.parse_ty_specifier()?),
                    };
                }
                let end = self.expect(TokenKind::RParen, "enum arm")?.span;
                (VariantData::Tuple(elems), end)
            }
            _ => (VariantData::Unit, ident.span),
        };
        Ok(Variant {
            span: start.combine(&end),
            ident,
            data,
        })
    }

    fn parse_ty_kind(&mut self) -> ParseResult<TyKind> {
        match self.peek_kind()? {
            TokenKind::LBracket => {
                self.advance()?;
                let ty = self.parse_ty_kind()?;
                self.expect(TokenKind::RBracket, "Feldelementtyp")?;
                Ok(TyKind::Array(Box::new(ty)))
            }
            TokenKind::LParen => {
                self.advance()?;

                let mut elems = Vec::new();
                while self.peek_kind()? != TokenKind::RParen {
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
            _ => {
                println!("failed to parse type");
                Err(SyntaxError::UnexpectedEOF)
            }
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
            let t = self.advance()?;
            segments.push(Ident::new(t.lexeme, t.span));

            match self.peek_kind()? {
                TokenKind::PathSep => {
                    self.advance()?;
                }
                _ => break,
            };
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
    // term
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

    fn parse_unary(&mut self) -> ParseResult<Expr> {
        match self.peek_kind()? {
            TokenKind::Operator(Operator::Not) | TokenKind::Operator(Operator::Minus) => {
                let op = self.advance()?;
                let rhs = self.parse_unary()?;
                let span = op.span.combine(&rhs.span);
                Ok(Expr {
                    node: ExprKind::unary(rhs, op.kind),
					span: span.clone(),
					ty: Ty::default_infer_type(span),
                })
            }
            _ => self.parse_literal(),
        }
    }

    fn parse_literal(&mut self) -> ParseResult<Expr> {
        match self.peek_kind()? {
            TokenKind::Literal(lit) => {
                let span = self.advance()?.span;
                Ok(Expr {
                    node: ExprKind::Literal(lit, span),
					ty: Ty::default_infer_type(span),
					span,
                })
            }
            TokenKind::LParen => self.parse_tup(),
            TokenKind::RBracket => self.parse_arr(),
            _ => self.parse_call_or_struct_lit(),
        }
    }

    fn parse_call_or_struct_lit(&mut self) -> ParseResult<Expr> {
        // advance base iterator by 1 position and make sure we leave it in a correct state if we exit
        self.iter.peek();
        let res = match self.peek_kind()? {
            TokenKind::LParen => self.parse_call(),
            TokenKind::LBrace => self.parse_struct_lit(),
            _ => panic!("cant parse lit {:#?}", self.peek()),
        };
        self.iter.reset_peek();
        res
    }

    fn parse_struct_lit(&mut self) -> ParseResult<Expr> {
        let pat = self.parse_path()?;
        self.expect(TokenKind::LBrace, "Offene Klammer nach typenliteral")?;

        let mut members = Vec::new();
        while self.peek_kind()? != TokenKind::RBrace {
            let ident: Ident = self.expect(TokenKind::Ident, "feldname")?.into();
            self.expect(
                TokenKind::Colon,
                ": Seperator zwischen feldname und init Ausdruck",
            )?;
            let expr = self.parse_expr()?;

            let span = ident.span.combine(&expr.span);
            let member = Member::new(ident, expr, span);
            members.push(member);

            match self.peek_kind()? {
                TokenKind::RBrace => break,
                _ => self.expect(TokenKind::Comma, "literalfeld")?,
            };
        }
        let end = self
            .expect(TokenKind::RBrace, "schlissende Klammer vergessen?")?
            .span;
        let span = pat.span.combine(&end);
        let expr = Expr {
            node: ExprKind::struct_lit(pat.clone(), members),
            span,
			ty: Ty {
				kind: TyKind::Path(pat.clone()),
				span,
			}
		};
        Ok(expr)
    }

    fn parse_primary(&mut self) -> Result<Expr, SyntaxError> {
        match self.peek_kind()? {
            TokenKind::Keyword(Keyword::This) => {
                let var = Variable::new_local("selbst");
                let span = self.advance()?.span;
                let node = ExprKind::This(var, span);
                Ok(Expr::new(node, span))
            }
            TokenKind::Ident => {
                let token = self.advance()?;
                let var = Variable::new_global(token.lexeme.as_str());
                Ok(Expr {
                    node: ExprKind::Variable(var),
                    span: token.span,
					ty: Ty::default_infer_type(token.span),
                })
            }
            _ => Err(SyntaxError::UnexpectedEOF),
        }
    }

    fn parse_tup(&mut self) -> ParseResult<Expr> {
        let start = self.advance()?.span;
        let mut values = Vec::new();
        while self.peek_kind()? != TokenKind::RParen {
            values.push(self.parse_expr()?);
            match self.peek_kind()? {
                TokenKind::RParen => break,
                _ => self.expect(TokenKind::Comma, "ausdruck")?,
            };
        }
        let end = self.expect(TokenKind::RParen, "schliessende Klammer")?.span;
		let span = start.combine(&end);
		Ok(Expr {
			node: ExprKind::Tup(values),
			span,
			ty: Ty::default_infer_type(span),
		})
    }

    fn parse_arr(&mut self) -> ParseResult<Expr> {
        let start = self.expect(TokenKind::LBracket, "Feldliteral")?.span;
        let mut values = Vec::new();
        while self.peek_kind()? != TokenKind::RBracket {
            values.push(self.parse_expr()?);
            match self.peek_kind()? {
                TokenKind::RBracket => break,
                _ => self.expect(TokenKind::Comma, "Feldelement")?,
            };
        }
        let end = self.expect(TokenKind::RBracket, "Feldliteral")?.span;
		let span = start.combine(&end);
		Ok(Expr {
			node: ExprKind::Array(values),
			span: start.combine(&end),
			ty: Ty::default_infer_type(span),
		})
    }

    fn parse_call(&mut self) -> Result<Expr, SyntaxError> {
        let mut expr = self.parse_primary()?;
        loop {
            match self.peek_kind()? {
                TokenKind::LParen => {
                    self.advance()?;
                    expr = self.finish_call(expr)?;
                }
                TokenKind::LBracket => {
                    expr = self.parse_index(expr)?;
                }
                TokenKind::Dot => {
                    let start = self.advance()?.span;
                    let name = self.advance()?;
                    let span = start.combine(&name.span);
                    let ident = Ident::new(name.lexeme, name.span);
                    let node = ExprKind::field(expr, ident);
                    expr = Expr::new(node, span)
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
        let end = self.expect(TokenKind::RParen, "argumente")?.span;
		let span = callee.span.combine(&end);
		Ok(Expr {
			span,
			node: ExprKind::call(callee, args),
			ty: Ty::default_infer_type(span),
		})
    }

    fn parse_index(&mut self, callee: Expr) -> ParseResult<Expr> {
        let start = self.expect(TokenKind::LBracket, "Feldindex")?.span;
        let index = self.parse_expr()?;
        let end = self.expect(TokenKind::RBracket, "] nach Feldindex")?.span;
		let span = start.combine(&end);
		Ok(Expr {
			node: ExprKind::index(callee, index),
			span,
			ty: Ty::default_infer_type(span),
		})
    }

    fn peek_kind(&mut self) -> Result<TokenKind, SyntaxError> {
        // maybe we can remove this clone, although I doubt it because of the string fields
        let item = match self.iter.peek() {
            Some(t) => Ok(t.kind.clone()),
            None => Ok(TokenKind::EOF),
        };
        self.iter.reset_peek();
        item
    }

    fn peek(&mut self) -> ParseResult<Token> {
        let elem = self.iter.peek().cloned().ok_or(SyntaxError::UnexpectedEOF);
        self.iter.reset_peek();
        elem
    }

    fn advance(&mut self) -> Result<Token, SyntaxError> {
        self.iter.next().ok_or(SyntaxError::UnexpectedEOF)
    }

    fn has_next(&mut self) -> bool {
        let res = self.iter.peek().is_some();
        self.iter.reset_peek();
        res
    }

    fn expect(&mut self, expected: TokenKind, before: &'static str) -> ParseResult<Token> {
        if self.peek_kind()? == expected {
            self.advance()
        } else {
            Err(SyntaxError::Missing(expected.to_string(), before))
        }
    }
}

impl Iterator for Parser {
    type Item = ParseResult<Stmt>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.has_next() {
            let test = self.parse();
            Some(test)
        } else {
            None
        }
    }
}
