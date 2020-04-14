use std::cell::RefCell;
use std::convert::TryInto;
use std::iter::*;
use std::rc::Rc;
use std::vec::IntoIter;

use itertools::multipeek;
use itertools::*;

use super::ast::*;
use super::errors::*;
use super::lexer::*;
use crate::session::*;

type ParseResult<T> = Result<T, Diagnostic>;

pub struct Parser {
    iter: MultiPeek<IntoIter<Token>>,
    sess: Rc<RefCell<Session>>,
    last: Option<Token>,
}

/// `FnParsingMode` tells the `parse_fn_decl()` if we are allowed to have a `self` param in the function signature.
/// If we parse an associated function in an impl Block, we pass the type which the impl block implements as an value
/// in Method. During fn_signature_parsing the `self` param get's desuggared into a normal function parameter
enum FnParsingMode {
    Method(Path),
    Function,
}

macro_rules! __bin_op_rule (
	($name:ident, $inner:ident, $conv:ty, $kind:ident, $($op_pattern:pat)|*) => (
		fn $name(&mut self) -> ParseResult<Expr> {
			let mut lhs = self.$inner()?;
			while let Ok(tk) = self.peek_kind() {
				let op = match tk {
					$($op_pattern)|* => self.advance()?,
					_ => break,
				};
				let rhs = self.$inner()?;
				let span = lhs.span.combine(&rhs.span);
				let op: $conv = op.kind.try_into().unwrap();
				lhs = Expr {
					node: ExprKind::$kind(lhs, rhs, op),
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
		__bin_op_rule!($name, $inner, CmpOp, logical, $($op_pattern)|*);
	);
);
macro_rules! binary_impl (
	($name:ident, $inner:ident, $($op_pattern:pat)|*) => (
		__bin_op_rule!($name, $inner, BinOp, binary, $($op_pattern)|*);
	);
);

impl Parser {
    pub fn new(i: Vec<Token>, sess: Rc<RefCell<Session>>) -> Self {
        let last = i.last().cloned();
        Parser {
            iter: multipeek(i.into_iter()),
            sess,
            // NOTE(Simon): this only gets used for error reporting if we unexpectedly reach the end of a file
            // NOTE(Simon): this could be `None`, but in this we don't ever try to parse anything beecause `has_next` in our iter implementation will return false and we will stop parsing
            last,
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
                | TokenKind::Keyword(Keyword::Impl)
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
            TokenKind::Keyword(Keyword::Fun) => self.parse_fn_decl(FnParsingMode::Function),
            TokenKind::Keyword(Keyword::Impl) => self.parse_impl_block(),
            // FIXME
            _ => {
                let sp = self.peek()?.span;
                Err(self.span_err("An dieser Stelle haben wir einen der folgenden Woerter erwartet: `fun`, `typ`, `implementiere`.", &sp))
            }
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

    fn parse_fn_header(&mut self, parse_mode: FnParsingMode) -> ParseResult<FnSig> {
        self.expect(TokenKind::Keyword(Keyword::Fun), "Funktionsdeklaration")?;

        let name = self.parse_ident()?;
        self.expect(TokenKind::LParen, "Funktionsnamen")?;

        let mut params = Vec::new();

        match parse_mode {
            FnParsingMode::Method(p) => {
                if self.peek_kind()? == TokenKind::Keyword(Keyword::This) {
                    let self_ty = Ty::new(TyKind::Path(p.clone()), p.span);
                    params.push((Ident::new("selbst".into(), p.span), self_ty));

                    if self.peek_kind()? != TokenKind::RParen {
                        self.expect(TokenKind::Comma, "Nach dem `selbst` Parameter und den restlichen Parameter der Funktion haben wir ein Komma erwartet!")?;
                    }
                }
            }
            FnParsingMode::Function => {
                if self.peek_kind()? == TokenKind::Keyword(Keyword::This) {
                    let sp = self.peek()?.span;
                    return Err(self.span_err("Mit dem `selbst` Parameter kannst du Werte eines Objekts aendern. Dafuer muss die Function, die jetzt 'Methode' heisst, in einem impl Block stehen. Der `selbst` Paramter muss immer der erste Parameter einer 'Methode sein. Seinen Datentyp brauchst du nicht festzulegen. Er steht durch den `impl block` fest!'", &sp));
                }
            }
        }
        while self.peek_kind()? != TokenKind::RParen {
            let p_name = self.parse_ident()?;
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

    fn parse_fn_decl(&mut self, parse_mode: FnParsingMode) -> ParseResult<Stmt> {
        let fn_head = self.parse_fn_header(parse_mode)?;
        let body = self.parse_block(false)?;
        Ok(Stmt::FnDecl(FnDecl::new(fn_head, body)))
    }

    fn parse_block(&mut self, break_allowed: bool) -> ParseResult<Block> {
        let start = self.expect(TokenKind::LBrace, "{ vor Block erwartet")?.span;

        let mut block = Vec::new();
        while self.peek_kind()? != TokenKind::RBrace {
            let stmt = match self.peek_kind()? {
                TokenKind::Ident(_) => self.parse_vardef()?, // FIXME(Simon): use parse_exprstmt_or_vardef
                TokenKind::Keyword(Keyword::This) => self.parse_expr_stmt()?,
                TokenKind::Keyword(Keyword::While) => self.parse_while_loop()?,
                TokenKind::Keyword(Keyword::For) => self.parse_for_loop()?,
                TokenKind::Keyword(Keyword::Return) => self.parse_return()?,
                TokenKind::Keyword(Keyword::Break) => self.parse_break(break_allowed)?,
                TokenKind::Keyword(Keyword::If) => self.parse_if()?,
                TokenKind::LBrace => Stmt::Block(self.parse_block(break_allowed)?),
                TokenKind::EOF => {
                    let mut sp = self.last.as_ref().unwrap().span;
                    sp.lo += 1;
                    sp.hi += 1;
                    return Err(self.span_err(
                        "An dieser Stelle haben wir eine schliessende Klammer: `} erwartet!`",
                        &sp,
                    ));
                }
                _ => {
                    let sp = self.last.as_ref().unwrap().span;
                    let tk = self.peek_kind()?.to_string();
                    return Err(self.span_err(
                        format!(
                            "An dieser Stelle haben wir einen unerwarteten Token gefunden: `{}`",
                            tk
                        ),
                        &sp,
                    ));
                }
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

        let loop_var = self.parse_ident()?;
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
        let target = self.parse_ident()?;
        let ty = match self.peek_kind()? {
            TokenKind::ColonEq => {
                // user has not provided a type, we will try to infer it later during type inference
                let infer_span = self.advance()?.span;
                Ty::default_infer_type(infer_span)
            }
            TokenKind::Colon => {
                // user has provided a concrete type, we will validate during type anlysis
                self.advance()?;
                self.parse_ty_specifier()?
            }
            _ => {
                let pk = self.peek()?;
                return Err(self.span_err(
                    format!(
                        "Invalides Zeichen: `{}` in Zuweisungsziel gefunden!",
                        pk.kind
                    ),
                    &pk.span,
                ));
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

    fn parse_expr_stmt(&mut self) -> ParseResult<Stmt> {
        let expr = self.parse_expr()?;
        self.expect(TokenKind::Semi, "Semicolon nach Ausdruck vergessen")?;
        Ok(Stmt::Expr(expr))
    }

    fn parse_break(&mut self, break_allowed: bool) -> ParseResult<Stmt> {
        if !break_allowed {
            let sp = self.advance()?.span;
            return Err(self.span_err(
                "Der`stop` Befehl ist nur im Koerper von Schleifen erlaubt",
                &sp,
            ));
        }

        self.expect(TokenKind::Keyword(Keyword::Break), "Stop befehl")?;
        self.expect(TokenKind::Semi, "Stop")?;
        Ok(Stmt::Break)
    }

    fn parse_impl_block(&mut self) -> ParseResult<Stmt> {
        let start = self
            .expect(
                TokenKind::Keyword(Keyword::Impl),
                "An dieser Stelle haben wir das Impl Schluesselwort erwartet!",
            )?
            .span;

        let impl_target = self.parse_path()?; // FIXME(Simon): we should expect a path here to impl structs from other modules
        self.expect(
            TokenKind::LBrace,
            "An dieser Stelle haben wir eine oeffnende Klammer: `{` erwartet",
        )?;

        let mut fn_decls = Vec::new();
        while self.peek_kind()? != TokenKind::RBrace {
            let p_mode = FnParsingMode::Method(impl_target.clone());
            fn_decls.push(self.parse_fn_decl(p_mode)?);
        }

        let end = self
            .expect(
                TokenKind::RBrace,
                "An dieser Stelle haben wir eine schliessende Klammer: `}` erwartet",
            )?
            .span;
        let fn_decls = fn_decls
            .into_iter()
            .map(|s| match s {
                Stmt::FnDecl(f) => f,
                _ => unreachable!(),
            })
            .collect();
        Ok(Stmt::ImplBlock {
            target: impl_target,
            fn_decls: fn_decls,
            span: start.combine(&end),
        })
    }

    pub fn parse_struct_decl(&mut self) -> ParseResult<Stmt> {
        let start = self
            .expect(TokenKind::Keyword(Keyword::Struct), "TypenDeclaration")?
            .span;
        let struct_name = self.parse_ident()?;

        let mut fields = Vec::new();

        self.expect(TokenKind::LBrace, "Typenname")?;

        while self.peek_kind()? != TokenKind::RBrace {
            let name = self.parse_ident()?;
            self.expect(TokenKind::Colon, "feldname")?;
            let ty = self.parse_ty_specifier()?;

            let span = name.span.combine(&ty.span);
            fields.push(Field::new(name, ty, span));

            match self.peek_kind()? {
                TokenKind::RBrace => break,
                _ => self.expect(TokenKind::Comma, "feld")?,
            };
        }
        let end = self.expect(TokenKind::RBrace, "TypenDeclaration")?.span;
        Ok(Stmt::StructDecl(StructDecl {
            name: struct_name,
            fields,
            span: start.combine(&end),
        }))
    }

    fn parse_enum_decl(&mut self) -> ParseResult<Stmt> {
        let start = self
            .expect(
                TokenKind::Keyword(Keyword::Struct),
                "enum or struct declaration",
            )?
            .span;
        let name = self.parse_ident()?;
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
        let ident = self.parse_ident()?;
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
            TokenKind::Ident(_) => {
                let path = self.parse_path()?;
                Ok(TyKind::Path(path))
            }
            _ => {
                let sp = self.peek()?.span;
                Err(self.span_err(
                    "An dieser Stelle habe ich einen Datentypkennzeichner erwartet",
                    &sp,
                ))
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

        while let TokenKind::Ident(_) = self.peek_kind()? {
            let frag = self.parse_ident()?;
            segments.push(frag);

            match self.peek_kind()? {
                TokenKind::PathSep => {
                    self.advance()?;
                }
                _ => break,
            };
        }
        let first = segments.first().unwrap().span;
        let last = segments.last().unwrap().span;

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
    pub fn parse_expr(&mut self) -> ParseResult<Expr> {
        self.parse_and()
    }

    fn parse_unary(&mut self) -> ParseResult<Expr> {
        match self.peek_kind()? {
            TokenKind::Operator(Operator::Not) | TokenKind::Operator(Operator::Minus) => {
                let op = self.advance()?;
                let rhs = self.parse_unary()?;
                let span = op.span.combine(&rhs.span);
                Ok(Expr {
                    node: ExprKind::unary(rhs, op.kind.try_into().unwrap()),
                    span: span.clone(),
                    ty: Ty::default_infer_type(span),
                })
            }
            _ => self.parse_call(),
        }
    }

    fn parse_struct_lit(&mut self, pat: Path) -> ParseResult<Expr> {
        self.expect(TokenKind::LBrace, "Offene Klammer nach typenliteral")?;

        let mut members = Vec::new();
        while self.peek_kind()? != TokenKind::RBrace {
            let name = self.parse_ident()?;
            self.expect(
                TokenKind::Colon,
                ": Seperator zwischen feldname und init Ausdruck",
            )?;
            let expr = self.parse_expr()?;

            let span = name.span.combine(&expr.span);
            let member = Member::new(name, expr, span);
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
            },
        };
        Ok(expr)
    }

    fn parse_primary(&mut self) -> ParseResult<Expr> {
        match self.peek_kind()? {
            TokenKind::Keyword(Keyword::This) => {
                let var = Variable::new_local("selbst");
                let span = self.advance()?.span;
                let node = ExprKind::This(var, span);
                Ok(Expr::new(node, span))
            }
            TokenKind::Literal(lit) => {
                let span = self.advance()?.span;
                Ok(Expr {
                    node: ExprKind::Literal(lit, span),
                    ty: Ty::default_infer_type(span),
                    span,
                })
            }
            TokenKind::LParen => self.parse_tup(),
            TokenKind::LBracket => self.parse_arr(),
            TokenKind::Ident(_) => self.parse_primary_ident(),
            _ => panic!("{:#?}", self.peek()),
        }
    }

    fn parse_primary_ident(&mut self) -> ParseResult<Expr> {
        let pat = self.parse_path()?;
        match self.peek_kind()? {
            TokenKind::LBrace => self.parse_struct_lit(pat),
            _ => {
                let span = pat.span;
                Ok(Expr {
                    node: ExprKind::Path(pat),
                    span,
                    ty: Ty::default_infer_type(span),
                })
            }
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

    fn parse_call(&mut self) -> ParseResult<Expr> {
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
                    let node = ExprKind::field(expr, self.parse_ident()?);
                    expr = Expr::new(node, span)
                }
                _ => break,
            }
        }
        Ok(expr)
    }

    fn finish_call(&mut self, callee: Expr) -> ParseResult<Expr> {
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

    fn parse_ident(&mut self) -> ParseResult<Ident> {
        match self.peek_kind()? {
            TokenKind::Ident(_) => Ok(self.advance()?.try_into().unwrap()),
            _ => {
                let sp = self.peek()?.span;
                Err(self.span_err(
                    "An dieser Stelle habe ich eigentlich einen `Bezeichner` erwartet",
                    &sp,
                ))
            }
        }
    }

    fn peek_kind(&mut self) -> ParseResult<TokenKind> {
        // maybe we can remove this clone, although I doubt it because of the string fields
        let item = match self.iter.peek() {
            Some(t) => Ok(t.kind.clone()),
            None => Ok(TokenKind::EOF),
        };
        self.iter.reset_peek();
        item
    }

    fn peek(&mut self) -> ParseResult<Token> {
        let sp = self.last.as_ref().unwrap().span;
        let elem = self
            .iter
            .peek()
            .cloned()
            .ok_or(self.span_err("Wir haben unerwartet das Ende der Datei erreicht!", &sp));
        self.iter.reset_peek();
        elem
    }

    fn advance(&mut self) -> ParseResult<Token> {
        match self.iter.next() {
            Some(t) => {
                self.last = Some(t.clone());
                Ok(t.clone())
            }
            None => Err(self.span_err(
                "Ich habe unerwartet das Ende der Datei erreicht!",
                &self.last.as_ref().unwrap().span,
            )),
        }
    }

    fn has_next(&mut self) -> bool {
        let res = self.iter.peek().is_some();
        self.iter.reset_peek();
        res
    }

    fn expect<S: Into<String>>(&mut self, expected: TokenKind, msg: S) -> ParseResult<Token> {
        if self.peek_kind()? == expected {
            self.advance()
        } else {
            let sp = self.peek()?.span;
            Err(self.span_err(msg, &sp))
        }
    }

    fn span_err<S: Into<String>>(&self, msg: S, span: &Span) -> Diagnostic {
        self.sess
            .borrow_mut()
            .span_err("Fehler beim Parsen", &msg.into(), span)
    }
}

impl Iterator for Parser {
    type Item = ParseResult<Stmt>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.has_next() {
            let test = self.parse();
            if test.is_err() {
                self.sync_parser_state();
            }
            Some(test)
        } else {
            None
        }
    }
}
