use std::collections::HashMap;
use std::convert::TryInto;
use std::iter::*;
use std::vec::IntoIter;

use itertools::multipeek;
use itertools::*;

use crate::ast::*;
use crate::errors::*;
use crate::lexer::*;
use crate::typer::{Ty, TyKind};

type ParseResult<T> = Result<T, Diagnostic>;

pub struct Parser {
    iter: MultiPeek<IntoIter<Token>>,
    last: Option<Token>,
}

/// `FnParsingMode` tells the `parse_fn_decl()` if we are allowed to have a `self` param in the function signature.
/// If we parse an associated function in an impl Block, we pass the type which the impl block implements as an value
/// in Method. During fn_signature_parsing the `self` param get's desuggared into a normal function parameter
#[derive(PartialEq, Debug)]
enum FnParsingMode {
    Method(Path),
    Function,
}

#[derive(PartialEq, Debug, Copy, Clone)]
enum BlockParsingMode {
    Loop,
    Normal,
}

enum Directive {
    Expr,
    VarDef,
    Assign,
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
				let op: $conv = op.try_into()?;
				lhs = Expr {
					node: ExprKind::$kind{
						lhs: Box::new(lhs),
						rhs: Box::new(rhs),
						op,
					},
					ty: Ty {
						kind: TyKind::Infer,
						span: span.clone(),
					},
					span,
				};
			}
			Ok(lhs)
		}
	);
);

macro_rules! logical_impl (
	($name:ident, $inner:ident, $($op_pattern:pat)|*) => (
		__bin_op_rule!($name, $inner, CmpOp, Logical, $($op_pattern)|*);
	);
);
macro_rules! binary_impl (
	($name:ident, $inner:ident, $($op_pattern:pat)|*) => (
		__bin_op_rule!($name, $inner, BinaryOp, Binary, $($op_pattern)|*);
	);
);

impl Parser {
    pub fn new(i: Vec<Token>) -> Self {
        let last = i.last().cloned();
        Parser {
            iter: multipeek(i.into_iter()),
            // NOTE(Simon): this only gets used for error reporting if we unexpectedly reach the end of a file
            // NOTE(Simon): this could be `None`, but in this we don't ever try to parse anything beecause `has_next` in our iter implementation will return false and we will stop parsing
            last,
        }
    }

    fn sync_parser_state(&mut self) {
        loop {
            if let Ok(tk) = self.peek_kind() {
                match tk {
                    // TokenKind::Semi => {
                    //     self.advance().unwrap();
                    //     if let Ok(TokenKind::RBrace) = self.peek_kind() {
                    //         self.advance().unwrap();
                    //     }
                    //     return;
                    // }
                    TokenKind::EOF => {
                        return;
                    }
                    TokenKind::Keyword(Keyword::Struct)
                    | TokenKind::Keyword(Keyword::Fun)
                    | TokenKind::Keyword(Keyword::For)
                    // | TokenKind::Keyword(Keyword::If)
                    // | TokenKind::Keyword(Keyword::While)
                    // | TokenKind::Keyword(Keyword::Return)
                    | TokenKind::Keyword(Keyword::Impl) => return,
                    _ => self.advance().unwrap(),
                };
            }
        }
    }

    pub fn parse(&mut self) -> ParseResult<Decl> {
        self.parse_decl()
    }

    pub fn parse_decl(&mut self) -> ParseResult<Decl> {
        match self.peek_kind()? {
            TokenKind::Keyword(Keyword::Fun) => {
                Ok(Decl::Fn(self.parse_fn(FnParsingMode::Function)?))
            }
            TokenKind::Keyword(Keyword::Impl) => self.parse_impl(),
            TokenKind::Keyword(Keyword::Struct) => Ok(Decl::TyDecl(self.parse_ty()?)),
            _ => {
                let expected = vec![
                    TokenKind::Keyword(Keyword::Fun),
                    TokenKind::Keyword(Keyword::Struct),
                    TokenKind::Keyword(Keyword::Impl),
                ];
                let t = self.advance()?;
                let kind = ErrKind::Syntax(SyntaxErr::MissingToken {
                    expected,
                    actual: t.kind,
                });
                Err(self.span_err(kind, t.span))
            }
        }
    }

    fn parse_ty(&mut self) -> ParseResult<TyDecl> {
        match self.look_ahead(3)? {
            TokenKind::LBrace => Ok(TyDecl::Struct(self.parse_struct()?)),
            TokenKind::Eq => Ok(TyDecl::Enum(self.parse_enum()?)),
            _ => {
                let span = self.last.as_ref().unwrap().span;
                let kind = ErrKind::Syntax(SyntaxErr::MissingToken {
                    expected: vec![TokenKind::LBrace, TokenKind::Eq],
                    actual: self.look_ahead(3)?,
                });
                return Err(self.span_err(kind, span));
            }
        }
    }

    fn parse_fn_header(&mut self, parse_mode: FnParsingMode) -> ParseResult<FnSig> {
        let start = self
            .expect(
                TokenKind::Keyword(Keyword::Fun),
                "An dieser Stelle haben wir das `fun` Schluesselwort erwartet!",
            )?
            .span;

        let name = self.parse_ident()?;
        self.expect(
            TokenKind::LParen,
            "An dieser Stelle haben wir eine öffnende Klammer `(` erwartet!",
        )?;

        let mut params = Vec::new();

        match parse_mode {
            FnParsingMode::Method(p) => {
                if self.peek_kind()? == TokenKind::Keyword(Keyword::This) {
                    self.advance()?;
                    let sp = p.span;

                    let self_ty = Ty {
                        kind: TyKind::Path(p),
                        span: sp,
                    };
                    params.push(Param::new(Ident::new("selbst".into(), sp), self_ty, sp));
                    if self.peek_kind()? != TokenKind::RParen {
                        self.expect(TokenKind::Comma, "Nach dem `selbst` Parameter und den restlichen Parametern der Funktion haben wir ein Komma erwartet!")?;
                    }
                }
            }
            FnParsingMode::Function => {
                if self.peek_kind()? == TokenKind::Keyword(Keyword::This) {
                    let sp = self.advance()?.span;
                    return Err(self.span_err(ErrKind::Syntax(SyntaxErr::SelfOutsideImpl), sp));
                }
            }
        }
        while self.peek_kind()? != TokenKind::RParen {
            let p_name = self.parse_ident()?;
            self.expect(TokenKind::Colon, "Name und Typ eines Funktionsparameters werden durch einen `:` voneinander getrennt!")?;
            let p_ty = self.parse_ty_specifier()?;
            let sp = p_name.span.clone().combine(&p_ty.span.clone());
            params.push(Param::new(p_name.clone(), p_ty.clone(), sp));

            match self.peek_kind()? {
                TokenKind::RParen => break,
                _ => self.expect(TokenKind::Comma, "Die einzelnen Parameter einer Funktion werden durch ein Komma `,` voneinander getrennt!")?,
            };
        }
        let closing = self.expect(TokenKind::RParen, "Rueckgabetyp")?;

        let ret_ty = match self.peek_kind()? {
            TokenKind::ThinArrow => {
                self.advance()?;
                self.parse_ty_specifier()?
            }
            _ => {
                // FIXME(Simon): fix the span if we manually insert the return type of the function
                let sp = Span::new(closing.span.lo + 4, closing.span.hi + 6);
                Ty::default_unit_type(sp)
            }
        };
        let span = ret_ty.span.combine(&start);
        Ok(FnSig {
            name,
            params,
            ret_ty: box ret_ty,
            span,
        })
    }

    fn parse_fn(&mut self, parse_mode: FnParsingMode) -> ParseResult<FnDecl> {
        let header = self.parse_fn_header(parse_mode)?;
        let body = self.parse_block(BlockParsingMode::Normal)?;
        let span = header.span.combine(&body.span);
        Ok(FnDecl { header, body, span })
    }

    fn parse_block(&mut self, mode: BlockParsingMode) -> ParseResult<Block> {
        let start = self
            .expect(
                TokenKind::LBrace,
                "Geschweifte Klammer { vor Block erwartet",
            )?
            .span;

        let mut block = Vec::new();
        while self.peek_kind()? != TokenKind::RBrace {
            block.push(self.parse_stmt(mode)?);
        }
        let end = self
            .expect(TokenKind::RBrace, "Block nicht geschlossen?")?
            .span;
        Ok(Block::new(block, start.combine(&end)))
    }

    fn parse_stmt(&mut self, mode: BlockParsingMode) -> ParseResult<Stmt> {
        match self.peek_kind()? {
            TokenKind::Keyword(Keyword::While) => self.parse_while_loop(),
            TokenKind::Keyword(Keyword::For) => self.parse_for_loop(),
            TokenKind::Keyword(Keyword::Return) => self.parse_return(),
            TokenKind::Keyword(Keyword::Continue) => self.parse_continue(mode),
            TokenKind::Keyword(Keyword::Break) => self.parse_break(mode),
            TokenKind::Keyword(Keyword::If) => self.parse_if(mode),
            TokenKind::LBrace => Ok(Stmt::Block(self.parse_block(mode)?)),
            _ => match self.peek_directive()? {
                Directive::VarDef => Ok(self.parse_vardef_stmt()?),
                Directive::Assign => Ok(self.parse_assign()?),
                Directive::Expr => Ok(self.parse_expr_stmt()?),
            },
        }
    }

    fn parse_while_loop(&mut self) -> ParseResult<Stmt> {
        let start = self
            .expect(TokenKind::Keyword(Keyword::While), "Solange")?
            .span;
        let cond = self.parse_expr()?;

        let body = self.parse_block(BlockParsingMode::Loop)?;
        let end = body.span;
        Ok(Stmt::While {
            cond,
            body,
            span: start.combine(&end),
        })
    }

    fn parse_for_loop(&mut self) -> ParseResult<Stmt> {
        let start = self.expect(TokenKind::Keyword(Keyword::For), "Fuer")?.span;

        let vardef = self.parse_vardef()?;

        let body = self.parse_block(BlockParsingMode::Loop)?;
        let span = start.combine(&body.span);
        Ok(Stmt::For { vardef, body, span })
    }

    fn parse_if(&mut self, mode: BlockParsingMode) -> ParseResult<Stmt> {
        let start = self.expect(TokenKind::Keyword(Keyword::If), "An dieser Stelle haben wir das `wenn` Schluesselwort erwartet. Mit `wenn` kann dein Programm Entscheidungen treffen. Der Programmtext innerhalb des Koerpers des `wenn` Befehls wird nur dann ausgefuehrt wenn sich seine Bedingung bewahrheitet!")?.span;
        let cond = self.parse_expr()?;

        self.expect(
            TokenKind::Keyword(Keyword::Then),
            "Einem `wenn` muss auch ein `dann` folgen :D",
        )?;

        let body = self.parse_block(mode)?;
        let mut else_branches = Vec::new();
        loop {
            match (self.peek_kind()?, self.look_ahead(2)?) {
                (TokenKind::Keyword(Keyword::Else), TokenKind::Keyword(Keyword::If)) => {
                    else_branches.push(self.parse_elif_branch(mode)?)
                }
                _ => break,
            }
        }

        let final_branch = if self.peek_kind()? == TokenKind::Keyword(Keyword::Else) {
            let start = self.advance()?.span;
            let body = self.parse_block(mode)?;
            let sp = start.combine(&body.span.clone());
            Some(FinalBranch { body, span: sp })
        } else {
            None
        };

        let span = match final_branch {
            Some(ref b) => start.combine(&b.span.clone()),
            None => {
                if !else_branches.is_empty() {
                    start.combine(&else_branches.last().unwrap().span)
                } else {
                    start.combine(&body.span.clone())
                }
            }
        };

        Ok(Stmt::If {
            cond,
            body,
            else_branches,
            final_branch,
            span,
        })
    }

    fn parse_elif_branch(&mut self, mode: BlockParsingMode) -> ParseResult<ElseBranch> {
        let start = self.expect(TokenKind::Keyword(Keyword::Else), "An dieser Stelle haben wir das `sonst` Schluesselwort erwartet! Es erlaubt dir nach einem primaeren `wenn` Befehl noch weitere Bedingung zu beachten.")?.span;
        self.expect(TokenKind::Keyword(Keyword::If), "An dieser Stelle haben wir das `wenn` Schluesselwort erwartet! Es erlaubt dir feinere Entscheidungen nach einem `sonst` Befehl zu treffen")?;

        let cond = self.parse_expr()?;

        self.expect(
            TokenKind::Keyword(Keyword::Then),
            "Wenn du eine 'Wenn-dann'-Abfrage machst, muss auf das 'Wenn' immer ein 'dann' folgen, so wissen wir, was wir machen müssen wenn das 'wenn'-statement erfüllt ist,Einem `wenn` muss auch ein `dann` folgen!",//torben
        )?;
        let body = self.parse_block(mode)?;
        let span = start.combine(&body.span.clone());
        Ok(ElseBranch { cond, body, span })
    }

    fn parse_return(&mut self) -> ParseResult<Stmt> {
        let start = self
            .expect(
                TokenKind::Keyword(Keyword::Return),
                "Wenn du etwas zuruückgeben willst musst du das Wort 'Rückgabe' benutzen, es zeigt uns was du zurückgeben willst! Das was du zurückgeben willst muss immer hinter 'Rückgabe'stehen. Als letztes kommt immer ein Semikolon(;)! Rueckgabe schluesselwort",//torben
            )?
            .span;
        let ret_val = match self.peek_kind()? {
            TokenKind::Semi => Expr::empty(start),
            _ => self.parse_expr()?,
        };
        let end = self
            .expect(TokenKind::Semi, "Wenn du etwas zurückgeben willst musst du immer ein Semikolon `;` dahinter schreiben!(; nach rueckgabe erwartet)")?//Torben
            .span;
        Ok(Stmt::Ret(ret_val, start.combine(&end)))
    }

    fn peek_directive(&mut self) -> ParseResult<Directive> {
        let mut i = 1;
        loop {
            match self.look_ahead(i)? {
                TokenKind::Colon | TokenKind::ColonEq => return Ok(Directive::VarDef),
                TokenKind::Eq => return Ok(Directive::Assign),
                TokenKind::Semi => return Ok(Directive::Expr),
                TokenKind::EOF => {
                    let sp = self.last.as_ref().unwrap().span;
                    return Err(self.span_err(ErrKind::Syntax(SyntaxErr::UnexpectedEOF), sp));
                }
                _ => i += 1,
            }
        }
    }

    fn parse_vardef(&mut self) -> ParseResult<VarDef> {
        let pat = self.parse_ident()?;
        let ty = match self.peek_kind()? {
            TokenKind::ColonEq => {
                // user has not provided a type, we will try to infer it later during type inference
                let span = self.advance()?.span;
                Ty {
                    kind: TyKind::Infer,
                    span,
                }
            }
            TokenKind::Colon => {
                // user has provided a concrete type, we will validate during type anlysis
                self.advance()?;
                self.parse_ty_specifier()?
            }
            _ => {
                let pk = self.advance()?;
                return Err(self.span_err(ErrKind::Syntax(SyntaxErr::InvalidVarDefTarget), pk.span));
            }
        };

        let init = self.parse_expr()?;

        let span = pat.span.combine(&init.span);
        Ok(VarDef {
            pat,
            init,
            ty,
            span,
        })
    }

    fn parse_vardef_stmt(&mut self) -> ParseResult<Stmt> {
        let vardef = self.parse_vardef()?;
        self.expect(
            TokenKind::Semi,
            "Wenn du eine Variable definieren willst musst du immer ein Semikolon(;) schreiben, wir wissen dann, wann die definition aufhört., Nach einer Variablendefinition haben wir ein Semicolon erwartet!",//torben
        )?;
        Ok(Stmt::VarDef(vardef))
    }

    fn parse_assign(&mut self) -> ParseResult<Stmt> {
        let lhs = self.parse_expr()?;
        self.expect(TokenKind::Eq, "Gleichheitszeichen")?;
        let rhs = self.parse_expr()?;
        let span = lhs.span.combine(&rhs.span);
        self.expect(TokenKind::Semi, "Semicolon")?;
        match lhs.node {
            ExprKind::Path(..) | ExprKind::Field(..) | ExprKind::Index { .. } | ExprKind::This => {
                Ok(Stmt::Assign { lhs, rhs, span })
            }
            _ => Err(self.span_err(
                ErrKind::Syntax(SyntaxErr::InvalidAssignmentTarget),
                lhs.span,
            )),
        }
    }

    fn parse_expr_stmt(&mut self) -> ParseResult<Stmt> {
        let expr = self.parse_expr()?;
        self.expect(TokenKind::Semi, "Semicolon nach Ausdruck vergessen")?;
        Ok(Stmt::Expr(expr))
    }

    fn parse_break(&mut self, mode: BlockParsingMode) -> ParseResult<Stmt> {
        if mode == BlockParsingMode::Normal {
            let span = self.advance()?.span;
            return Err(self.span_err(ErrKind::Syntax(SyntaxErr::BreakOutsideLoop), span));
        }
        let start = self
            .expect(TokenKind::Keyword(Keyword::Break), "Stop befehl")?
            .span;
        let end = self.expect(TokenKind::Semi, "Stop")?.span;
        Ok(Stmt::Break(start.combine(&end)))
    }

    fn parse_continue(&mut self, mode: BlockParsingMode) -> ParseResult<Stmt> {
        if mode == BlockParsingMode::Normal {
            let span = self.advance()?.span;
            // FIXME(Simon): generate correct error for continue
            return Err(self.span_err(ErrKind::Syntax(SyntaxErr::BreakOutsideLoop), span));
        }
        let start = self
            .expect(TokenKind::Keyword(Keyword::Continue), "weiter befehl")?
            .span;
        let end = self.expect(TokenKind::Semi, "weiter")?.span;
        Ok(Stmt::Continue(start.combine(&end)))
    }

    fn parse_impl(&mut self) -> ParseResult<Decl> {
        let start = self
            .expect(
                TokenKind::Keyword(Keyword::Impl),
                "Hier haben wir eine Implementierung erwartet. Schau was hier Implementiert wird, und Implementiere da dann.An dieser Stelle haben wir das Impl Schluesselwort erwartet!",//torben
            )?
            .span;

        let impl_target = self.parse_path()?;

        self.expect(
            TokenKind::LBrace,
            "Wir denken, dass du an dieser Stelle vergessen hast eine öffnende geschweifte Klamer ´{´ zu schreiben. An dieser Stelle haben wir eine oeffnende Klammer: `{` erwartet",//torben
        )?;
        let mut fn_decls = Vec::new();
        loop {
            match self.peek_kind()? {
                TokenKind::RBrace => break,
                TokenKind::Keyword(Keyword::Fun) => {
                    let mode = FnParsingMode::Method(impl_target.clone());
                    fn_decls.push(self.parse_fn(mode)?);
                }
                _ => {
                    let sp = self.last.as_ref().unwrap().span;

                    let expected = vec![TokenKind::Keyword(Keyword::Fun), TokenKind::RBrace];
                    let err = ErrKind::Syntax(SyntaxErr::MissingToken {
                        expected,
                        actual: self.peek_kind()?,
                    });
                    return Err(self.span_err(err, sp));
                }
            }
        }
        let end = self
            .expect(
                TokenKind::RBrace,
                "Wir denken, dass du an dieser Stelle vergessen hast eine schließende geschweifte Klamer ´}´ zu schreiben. Wir denken An dieser Stelle haben wir eine schliessende Klammer: `}` erwartet",//torben
            )?
            .span;
        Ok(Decl::Impl {
            target: impl_target,
            fn_decls,
            span: start.combine(&end),
        })
    }

    fn parse_struct(&mut self) -> ParseResult<Struct> {
        let start = self
            .expect(TokenKind::Keyword(Keyword::Struct), "TypenDeclaration")?
            .span;
        let name = self.parse_ident()?;

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
        Ok(Struct {
            name,
            fields,
            methods: Vec::new(),
            span: start.combine(&end),
        })
    }

    fn parse_enum(&mut self) -> ParseResult<Enum> {
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
                TokenKind::Sep => {
                    self.advance()?;
                    variants.push(self.parse_enum_variant()?)
                }
                TokenKind::Ident(_) => variants.push(self.parse_enum_variant()?),
                _ => break,
            };
        }
        let end = match variants.last() {
            Some(v) => v.span,
            None => name.span,
        };
        Ok(Enum {
            name,
            variants,
            methods: Vec::new(),
            span: start.combine(&end),
        })
    }

    fn parse_enum_variant(&mut self) -> ParseResult<Variant> {
        let name = self.parse_ident()?;
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
                (VariantData::Val(elems), end)
            }
            _ => (VariantData::Unit, name.span),
        };
        Ok(Variant {
            span: name.span.combine(&end),
            ident: name,
            data,
        })
    }

    fn parse_ty_kind(&mut self) -> ParseResult<TyKind> {
        match self.peek_kind()? {
            TokenKind::LBracket => {
                self.advance()?;
                let ty = self.parse_ty_specifier()?;
                self.expect(TokenKind::RBracket, "Feldelementtyp")?;
                Ok(TyKind::Array(Box::new(ty)))
            }
            TokenKind::LParen => {
                self.advance()?;

                let mut elems = Vec::new();
                while self.peek_kind()? != TokenKind::RParen {
                    let ty = self.parse_ty_specifier()?;
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
                let p = self.parse_path()?;
                Ok(TyKind::Path(p))
            }
            TokenKind::Dollar => {
                self.advance()?;
                let name = self.parse_ident()?;
                Ok(TyKind::Poly(name))
            }
            _ => {
                let sp = self.advance()?.span;
                Err(self.span_err(ErrKind::Syntax(SyntaxErr::ExpectedTy), sp))
            }
        }
    }

    fn parse_ty_specifier(&mut self) -> ParseResult<Ty> {
        let start = self.last.as_ref().unwrap().span;
        let kind = self.parse_ty_kind()?;
        let end = self.last.as_ref().unwrap().span;
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

    logical_impl!(parse_or, parse_and, TokenKind::Operator(Operator::Or));
    logical_impl!(parse_and, parse_eq, TokenKind::Operator(Operator::And));
    // equality   → comparison ( ( "!=" | "==" ) comparison )*
    logical_impl!(
        parse_eq,
        parse_cmp,
        TokenKind::Operator(Operator::EqEq) | TokenKind::Operator(Operator::NotEq)
    );
    // comparison → term ( ( ">" | ">=" | "<" | "<=" ) term )*
    logical_impl!(
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
    fn parse_expr(&mut self) -> ParseResult<Expr> {
        self.parse_range()
    }

    fn parse_range(&mut self) -> ParseResult<Expr> {
        let lhs = self.parse_or()?;
        if self.peek_kind()? == TokenKind::Operator(Operator::Range) {
            self.advance()?;
            let rhs = self.parse_or()?;
            let span = lhs.span.combine(&rhs.span);
            return Ok(Expr {
                node: ExprKind::Range(Box::new(lhs), Box::new(rhs)),
                span,
                ty: Ty {
                    kind: TyKind::Infer,
                    span,
                },
            });
        }
        Ok(lhs)
    }

    // fn parse_assign(&mut self) -> ParseResult<Expr> {
    //     let lhs = self.parse_or()?;
    //     if self.peek_kind()? == TokenKind::Eq {
    //         self.advance()?;
    //         let rhs = self.parse_expr()?;
    //         let sp = lhs.span.clone().combine(&rhs.span);
    //         match lhs.node {
    //             ExprKind::Path(..)
    //             | ExprKind::Field(..)
    //             | ExprKind::Index { .. }
    //             | ExprKind::This => {
    //                 let node = ExprKind::Assign {
    //                     target: Box::new(lhs),
    //                     value: Box::new(rhs),
    //                 };
    //                 return Ok(Expr::new(node, sp));
    //             }
    //             _ => return Err(self.span_err("Invalides Zuweisungsziel", &lhs.span)),
    //         };
    //     }
    //     Ok(lhs)
    // }

    fn parse_unary(&mut self) -> ParseResult<Expr> {
        match self.peek_kind()? {
            TokenKind::Operator(Operator::Not) | TokenKind::Operator(Operator::Minus) => {
                let op = self.advance()?;
                let rhs = self.parse_unary()?;
                let span = op.span.combine(&rhs.span);
                Ok(Expr {
                    node: ExprKind::Unary {
                        rhs: Box::new(rhs),
                        op: op.try_into()?,
                    },
                    span,
                    ty: Ty {
                        kind: TyKind::Infer,
                        span,
                    },
                })
            }
            TokenKind::Keyword(Keyword::Print)
            | TokenKind::Keyword(Keyword::Read)
            | TokenKind::Keyword(Keyword::Write) => self.parse_intrinsic(),
            _ => self.parse_call(),
        }
    }

    fn parse_intrinsic(&mut self) -> ParseResult<Expr> {
        match self.peek_kind()? {
            TokenKind::Keyword(Keyword::Print) => self.parse_print(),
            TokenKind::Keyword(Keyword::Read) => self.parse_read(),
            TokenKind::Keyword(Keyword::Write) => self.parse_print(),
            _ => unreachable!(),
        }
    }

    fn parse_print(&mut self) -> ParseResult<Expr> {
        let start = self
            .expect(TokenKind::Keyword(Keyword::Print), "Ausgabe schluesselwort")?
            .span;
        self.expect(
            TokenKind::LParen,
            "Kompiler intrinsiche Funktionen werden wie normale Funktionen aufgerufen!",
        )?;
        let mut args = Vec::new();
        args.push(self.parse_expr()?);
        loop {
            match self.peek_kind()? {
                TokenKind::RParen => break,
                _ => {
                    self.expect(TokenKind::Comma, "Auch bei intrinsichen Funktionen werden Argumente mit einem Komma getrennt!")?;
                    args.push(self.parse_expr()?);
                }
            }
        }
        let end = self.expect(TokenKind::RParen, "Es scheint als haettest du eine schliessende Klammer fuer den #ausgabe befehl vergessen")?.span;
        let span = start.combine(&end);
        Ok(Expr {
            node: ExprKind::Intrinsic {
                kind: Intrinsic::Print,
                args,
            },
            span,
            ty: Ty {
                kind: TyKind::Infer,
                span,
            },
        })
    }

    fn parse_read(&mut self) -> ParseResult<Expr> {
        let start = self
            .expect(
                TokenKind::Keyword(Keyword::Read),
                "An dieser stelle haben wir den intrinsichen Lese Befehl erwartet!",
            )?
            .span;
        self.expect(
            TokenKind::LParen,
            "Kompiler intrinsiche Funktionen werden wie normale Funktionen aufgerufen!",
        )?;
        let file_name = self.parse_expr()?;
        let end = self
            .expect(
                TokenKind::RParen,
                "Kompiler intrinsiche Funktionen werden wie normale Funktionen aufgerufen!",
            )?
            .span;
        let span = start.combine(&end);
        Ok(Expr {
            node: ExprKind::Intrinsic {
                kind: Intrinsic::Read,
                args: vec![file_name],
            },
            span,
            ty: Ty {
                kind: TyKind::Infer,
                span,
            },
        })
    }

    fn parse_write(&mut self) -> ParseResult<Expr> {
        let start = self
            .expect(
                TokenKind::Keyword(Keyword::Read),
                "An dieser stelle haben wir den intrinsichen Lese Befehl erwartet!",
            )?
            .span;
        self.expect(
            TokenKind::LParen,
            "Kompiler intrinsiche Funktionen werden wie normale Funktionen aufgerufen!",
        )?;
        let file_name = self.parse_expr()?;
        self.expect(
            TokenKind::Comma,
            "Auch die Argumente einer intrinsichen Funktion werden mit einem Komma getrennt",
        )?;
        let content = self.parse_expr()?;
        let end = self
            .expect(
                TokenKind::RParen,
                "Kompiler intrinsiche Funktionen werden wie normale Funktionen aufgerufen!",
            )?
            .span;
        let span = start.combine(&end);
        Ok(Expr {
            node: ExprKind::Intrinsic {
                kind: Intrinsic::Write,
                args: vec![file_name, content],
            },
            span,
            ty: Ty {
                kind: TyKind::Infer,
                span,
            },
        })
    }

    fn parse_struct_lit(&mut self, name: Ident) -> ParseResult<Expr> {
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
            .expect(TokenKind::RBrace, "Wir denken du hast hier eine schließende Klammer `(` vergessen. schlissende Klammer vergessen?")?//torben
            .span;
        let span = name.span.combine(&end);
        let expr = Expr {
            node: ExprKind::Struct { name, members },
            span,
            ty: Ty {
                kind: TyKind::Infer,
                span,
            },
        };
        Ok(expr)
    }

    fn parse_primary(&mut self) -> ParseResult<Expr> {
        match self.peek_kind()? {
            TokenKind::Keyword(Keyword::This) => {
                let sp = self.advance()?.span;
                let node = ExprKind::This;
                Ok(Expr::new(node, sp))
            }
            TokenKind::Lit(lit) => {
                let span = self.advance()?.span;
                Ok(Expr {
                    node: ExprKind::Lit(lit),
                    ty: Ty {
                        kind: TyKind::Infer,
                        span,
                    },
                    span,
                })
            }
            TokenKind::LParen => self.parse_tup(),
            TokenKind::LBracket => self.parse_arr(),
            TokenKind::Ident(_) => self.parse_primary_ident(),
            _ => {
                let sp = self.advance()?.span;
                Err(self.span_err(ErrKind::Syntax(SyntaxErr::ExpectedExpr), sp))
            }
        }
    }

    fn parse_primary_ident(&mut self) -> ParseResult<Expr> {
        let pat = self.parse_path()?;
        match self.peek_kind()? {
            TokenKind::LBrace => match pat.len() {
                1 => self.parse_struct_lit(pat.first().unwrap().clone()),
                _ => {
                    let expected = vec![TokenKind::LBrace, TokenKind::PathSep];
                    let err = ErrKind::Syntax(SyntaxErr::MissingToken {
                        expected,
                        actual: self.peek_kind()?,
                    });
                    let span = self.advance()?.span;
                    Err(self.span_err(err, span))
                }
            },
            _ => {
                let span = pat.span;
                Ok(Expr {
                    node: ExprKind::Path(pat),
                    span,
                    ty: Ty {
                        kind: TyKind::Infer,
                        span,
                    },
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
            ty: Ty {
                kind: TyKind::Infer,
                span,
            },
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
            ty: Ty {
                kind: TyKind::Infer,
                span,
            },
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
                    let name = self.parse_ident()?;
                    let span = start.combine(&name.span);
                    let node = ExprKind::Field(Box::new(expr), name);
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
            node: ExprKind::Call {
                callee: Box::new(callee),
                args,
            },
            ty: Ty {
                kind: TyKind::Infer,
                span,
            },
        })
    }

    fn parse_index(&mut self, callee: Expr) -> ParseResult<Expr> {
        let start = self.expect(TokenKind::LBracket, "Wenn du ein Feld erstellten willst, musst du ´[´ benutzen. Hier ist ´[´ der Feldindex! Feldindex")?.span; //torben
        let index = self.parse_expr()?;
        let end = self.expect(TokenKind::RBracket, "Wenn du ein Feld erstellen willst, musst du ´]´ benutzen. Hier ist ´]´ der Feldindex! ] nach Feldindex")?.span; //torben
        let span = start.combine(&end);
        Ok(Expr {
            node: ExprKind::Index {
                callee: Box::new(callee),
                index: Box::new(index),
            },
            span,
            ty: Ty {
                kind: TyKind::Infer,
                span,
            },
        })
    }

    // TODO(Simon): provide suggestion for ident
    fn parse_ident(&mut self) -> ParseResult<Ident> {
        match self.peek_kind()? {
            TokenKind::Ident(_) => self.advance()?.try_into(),
            _ => {
                let sp = self.advance()?.span;
                let err = ErrKind::Syntax(SyntaxErr::ExpectedTy);
                Err(self.span_err(err, sp))
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

    fn look_ahead(&mut self, i: u8) -> ParseResult<TokenKind> {
        debug_assert!(i > 0, "Can't peek into the void!");
        for _ in 0..i - 1 {
            self.iter.peek();
        }
        let item = match self.iter.peek() {
            Some(t) => Ok(t.kind.clone()),
            None => Ok(TokenKind::EOF),
        };
        self.iter.reset_peek();
        item
    }

    fn advance(&mut self) -> ParseResult<Token> {
        match self.iter.next() {
            Some(t) => {
                self.last = Some(t.clone());
                Ok(t)
            }
            None => Err(self.span_err(
                ErrKind::Syntax(SyntaxErr::UnexpectedEOF),
                self.last.as_ref().unwrap().span,
            )),
        }
    }

    fn has_next(&mut self) -> bool {
        let res = self.iter.peek().is_some();
        self.iter.reset_peek();
        res
    }

    fn expect(&mut self, expected: TokenKind, s: &str) -> ParseResult<Token> {
        if self.peek_kind()? == expected {
            self.advance()
        } else {
            let span = self.last.as_ref().unwrap().span;
            let diag = Diagnostic {
                kind: ErrKind::Syntax(SyntaxErr::MissingToken {
                    expected: vec![expected],
                    actual: self.peek_kind()?,
                }),
                suggestions: vec![s.to_string()],
                span,
            };
            Err(diag)
        }
    }

    fn span_err(&self, kind: ErrKind, span: Span) -> Diagnostic {
        Diagnostic {
            kind,
            suggestions: Vec::new(),
            span,
        }
    }
}

impl Iterator for Parser {
    type Item = ParseResult<Decl>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.has_next() {
            match self.parse() {
                Ok(decl) => Some(Ok(decl)),
                Err(err) => {
                    self.sync_parser_state();
                    Some(Err(err))
                }
            }
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {

    use pretty_assertions::assert_eq;

    use super::*;
    use crate::ast::dsl::*;

    fn parse_expr_setup(test: &str) -> Expr {
        let t_stream = Lexer::new(&test.to_string())
            .map(Result::unwrap)
            .collect::<Vec<_>>();
        let ast = Parser::new(t_stream).parse_expr().unwrap();
        ast
    }

    fn parse_stmt_setup(test: &str) -> Stmt {
        let t_stream = Lexer::new(&test.to_string())
            .map(Result::unwrap)
            .collect::<Vec<_>>();
        let t_stream = infer_semis(t_stream);
        Parser::new(t_stream)
            .parse_stmt(BlockParsingMode::Normal)
            .unwrap()
    }

    fn parse_decl_setup(test: &str) -> Decl {
        let t_stream = Lexer::new(&test.to_string())
            .map(Result::unwrap)
            .collect::<Vec<_>>();
        let t_stream = infer_semis(t_stream);
        Parser::new(t_stream).parse().unwrap()
    }

    #[test]
    fn parse_bin_expr_plus() {
        let actual = parse_expr_setup("a + 3");
        let expected = bin(path_expr(path!(a)), num(3), BinaryOp::Plus);
        assert_eq!(actual, expected);
    }

    #[test]
    fn parse_struct_lit_expr() {
        let actual = parse_expr_setup("foo::fazz{ bar: 20, buzz: WochenTag::Montag }");
        let expected = struct_lit(
            path!(foo::fazz),
            vec![
                member(ident!(bar), num(20)),
                member(ident!(buzz), path_expr(path!(WochenTag::Montag))),
            ],
        );
        assert_eq!(actual, expected);
    }

    #[test]
    fn parse_bin_expr_div() {
        let actual = parse_expr_setup("a / 3");
        let expected = bin(path_expr(path!(a)), num(3), BinaryOp::Divide);
        assert_eq!(actual, expected);
    }

    #[test]
    fn parse_bin_expr_mul() {
        let actual = parse_expr_setup("(a * 3) / 1");
        let expected = bin(
            tup!(bin(path_expr(path!(a)), num(3), BinaryOp::Multiply)),
            num(1),
            BinaryOp::Divide,
        );
        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_bin_expr_call() {
        let actual = parse_expr_setup("-foo((42, 42, 42)) / 1");

        let expected = bin(
            unary(
                call(path_expr(path!(foo)), vec![tup!(num(42), num(42), num(42))]),
                UnaryOp::Minus,
            ),
            num(1),
            BinaryOp::Divide,
        );
        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_method_call() {
        let actual = parse_expr_setup("foo.bar()");
        let expected = call(field(path_expr(path!(foo)), ident!(bar)), vec![]);
        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_self_method_call() {
        let actual = parse_expr_setup("selbst.bar()");
        let expected = call(field(this(), ident!(bar)), vec![]);
        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_self_field_method_call() {
        let actual = parse_expr_setup("selbst.foo.bar()");
        let expected = call(field(field(this(), ident!(foo)), ident!(bar)), vec![]);
        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_static_call() {
        let actual = parse_expr_setup("foo::bazz::bar()");
        let expected = call(path_expr(path!(foo::bazz::bar)), vec![]);
        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_path() {
        let actual = parse_expr_setup("foo::bazz::bar");
        let expected = path_expr(path!(foo::bazz::bar));
        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_array_lit() {
        let actual = parse_expr_setup("[[1, 2, 3], [4, 5, 6], [7, 8, 9]]");
        let expected = array![
            array![num(1), num(2), num(3)],
            array![num(4), num(5), num(6)],
            array![num(7), num(8), num(9)]
        ];
        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_ty_specifier() {
        let test = String::from("([(Foo, Bar)], [(Bar, Foo)])");
        let t_stream = Lexer::new(&test.to_string())
            .map(Result::unwrap)
            .collect::<Vec<_>>();
        let actual = Parser::new(t_stream).parse_ty_specifier().unwrap();
        let expected = tup_ty(vec![
            array_ty(tup_ty(vec![path_ty(path!(Foo)), path_ty(path!(Bar))])),
            array_ty(tup_ty(vec![path_ty(path!(Bar)), path_ty(path!(Foo))])),
        ]);
        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_poly_array_ty() {
        let test = String::from("[$T]");
        let t_stream = Lexer::new(&test.to_string())
            .map(Result::unwrap)
            .collect::<Vec<_>>();
        let actual = Parser::new(t_stream).parse_ty_specifier().unwrap();
        let expected = array_ty(poly_ty(ident!(T)));
        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_tup_lit() {
        let actual = parse_expr_setup("((20, 20), (29, 29), (10, 10))");
        let expected = tup!(
            tup!(num(20), num(20)),
            tup!(num(29), num(29)),
            tup!(num(10), num(10))
        );
        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_fn_decl_no_param_void() {
        let actual = parse_decl_setup("fun test() {}");
        let expected = Decl::Fn(FnDecl {
            header: FnSig {
                name: ident!(test),
                params: Vec::new(),
                ret_ty: unit_ty(),
                span: span(),
            },
            body: block(Vec::new()),
            span: span(),
        });
        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_fn_decl_multi_param_void() {
        let actual = parse_decl_setup("fun test(x: Zahl, y: [Test]) {}");
        let expected = Decl::Fn(FnDecl {
            header: FnSig {
                name: ident!(test),
                params: vec![
                    param(ident!(x), path_ty(path!(Zahl))),
                    param(ident!(y), array_ty(path_ty(path!(Test)))),
                ],
                ret_ty: unit_ty(),
                span: span(),
            },
            body: block(Vec::new()),
            span: span(),
        });
        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_while_loop() {
        let actual = parse_stmt_setup("solange wahr {}");
        let expected = Stmt::While {
            cond: bol(true),
            body: block(Vec::new()),
            span: Span::default(),
        };
        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_for_loop() {
        let actual = parse_stmt_setup("fuer i :=  0..10 {}");
        let vardef = VarDef {
            pat: ident!(i),
            init: range(num(0), num(10)),
            ty: infer_ty(),
            span: span(),
        };
        let expected = Stmt::For {
            vardef,
            body: block(Vec::new()),
            span: Span::default(),
        };
        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_var_def() {
        let actual = parse_stmt_setup("a := 20;");
        let expected = Stmt::VarDef(VarDef {
            pat: ident!(a),
            init: num(20),
            ty: infer_ty(),
            span: span(),
        });
        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_assign_field() {
        let actual = parse_stmt_setup("selbst.foo[0] = 20;");
        let expected = Stmt::Expr(assign(index(field(this(), ident!(foo)), num(0)), num(20)));
        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_assign_index() {
        let actual = parse_stmt_setup("foo[0] = 20;");
        let expected = Stmt::Expr(assign(index(path_expr(path!(foo)), num(0)), num(20)));
        assert_eq!(actual, expected);
    }
    #[test]
    fn parse_assign_self_index() {
        let actual = parse_stmt_setup("selbst[0] = 20;");
        let expected = Stmt::Expr(assign(index(this(), num(0)), num(20)));
        assert_eq!(actual, expected);
    }

    #[test]
    fn parse_assign_self() {
        let actual = parse_stmt_setup("selbst = [20, 20];");
        let expected = Stmt::Expr(assign(this(), array![num(20), num(20)]));
        assert_eq!(actual, expected);
    }

    #[test]
    fn parse_impl_block() {
        let prog = r#"
impl Mathe::Zahl {
    fn ist_null(selbst) -> Bool {
rueckgabe selbst == 0;
}
}
"#
        .to_string();
        let actual = parse_decl_setup(&prog);
        let expr = cmp(this(), num(0), CmpOp::EqEq);
        let expected = Decl::Impl {
            target: path!(Mathe::Zahl),
            fn_decls: vec![fn_decl(
                ident!(ist_null),
                vec![param(ident!(selbst), path_ty(path!(Mathe::Zahl)))],
                path_ty(path!(Bool)),
                block(vec![ret(expr)]),
            )],
            span: span(),
        };
        assert_eq!(actual, expected);
    }

    #[test]
    fn parse_enum_decl_unit_types() {
        let prog = r#"
typ Wochentag = Montag | Dienstag | Mittwoch | Donnerstag | Freitag | Samstag | Sonntag
"#;
        let actual = parse_decl_setup(&prog);
        let expected = Decl::TyDecl(TyDecl::Enum(Enum {
            name: ident!(Wochentag),
            variants: vec![
                variant(ident!(Montag), VariantData::Unit),
                variant(ident!(Dienstag), VariantData::Unit),
                variant(ident!(Mittwoch), VariantData::Unit),
                variant(ident!(Donnerstag), VariantData::Unit),
                variant(ident!(Freitag), VariantData::Unit),
                variant(ident!(Samstag), VariantData::Unit),
                variant(ident!(Sonntag), VariantData::Unit),
            ],
            span: span(),
            methods: Vec::new(),
        }));
        assert_eq!(actual, expected);
    }

    #[test]
    fn parse_struct_decl() {
        let prog = r#"
typ Liste {
speicher: [$T],
pos: Zahl,
kapazitaet: Zahl,
}
"#;
        let actual = parse_decl_setup(&prog);

        let expected = Decl::TyDecl(TyDecl::Struct(Struct {
            name: ident!(Liste),
            fields: vec![
                Field {
                    name: ident!(speicher),
                    ty: array_ty(poly_ty(ident!(T))),
                    span: span(),
                },
                Field {
                    name: ident!(pos),
                    ty: path_ty(path!(Zahl)),
                    span: span(),
                },
                Field {
                    name: ident!(kapazitaet),
                    ty: path_ty(path!(Zahl)),
                    span: span(),
                },
            ],
            methods: Vec::new(),
            span: span(),
        }));
        assert_eq!(actual, expected);
    }
    #[test]
    fn parse_enum_decl_val_types() {
        let actual = parse_decl_setup("typ Feld = Spieler(Text) | Leer");
        let expected = Decl::TyDecl(TyDecl::Enum(Enum {
            name: ident!(Feld),
            variants: vec![
                variant(
                    ident!(Spieler),
                    VariantData::Val(vec![path_ty(path!(Text))]),
                ),
                variant(ident!(Leer), VariantData::Unit),
            ],
            methods: vec![],
            span: span(),
        }));
        assert_eq!(actual, expected);
    }

    #[test]
    fn parse_block() {
        let prog = r#"
{
solange wahr {
stop;
weiter;
}
}
"#;
        let actual = parse_stmt_setup(&prog);
        let expected = Stmt::Block(block(vec![while_stmt(
            bol(true),
            block(vec![Stmt::Break(span()), Stmt::Continue(span())]),
        )]));
        assert_eq!(actual, expected);
    }

    #[test]
    fn parse_if_no_else() {
        let actual = parse_stmt_setup("wenn wahr dann {}");
        let expected = if_stmt(bol(true), block(Vec::new()), Vec::new(), None);
        assert_eq!(actual, expected);
    }

    #[test]
    fn parse_if_with_else() {
        let prog = r#"
wenn wahr dann {} sonst wenn wahr dann {} sonst wenn a == 3 dann{} sonst {

}
"#;
        let actual = parse_stmt_setup(&prog);
        let expected = if_stmt(
            bol(true),
            block(Vec::new()),
            vec![
                else_branch(bol(true), block(Vec::new())),
                else_branch(
                    cmp(path_expr(path!(a)), num(3), CmpOp::EqEq),
                    block(Vec::new()),
                ),
            ],
            Some(final_branch(block(Vec::new()))),
        );
        assert_eq!(actual, expected);
    }

    #[test]
    fn parse_if_only_final() {
        let prog = r#"
wenn wahr dann {} sonst {

}
"#;
        let actual = parse_stmt_setup(&prog);
        let expected = if_stmt(
            bol(true),
            block(Vec::new()),
            Vec::new(),
            Some(final_branch(block(Vec::new()))),
        );
        assert_eq!(actual, expected);
    }
}
