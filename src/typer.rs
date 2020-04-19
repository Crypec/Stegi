use colored::*;
use std::collections::HashMap;

use ngrammatic::{CorpusBuilder, Pad};

use crate::ast::*;
use crate::errors::Diagnostic;
use crate::lexer::*;

pub const DUMMY_TYPE_ID: usize = usize::MAX;

#[derive(Derivative)]
#[derivative(Debug)]
#[derive(PartialEq, Clone)]
pub enum TyKind {
    #[derivative(Debug = "transparent")]
    Array(Box<Ty>),

    Struct(Path),

    Enum(Path),

    #[derivative(Debug = "transparent")]
    Tup(Vec<Ty>),

    Num,

    Bool,

    Text,

    #[derivative(Debug = "transparent")]
    Infer(usize),

    Poly(Ident),

    #[derivative(Debug = "transparent")]
    Path(Path),
}

impl Default for TyKind {
    fn default() -> Self {
        TyKind::Tup(Vec::new())
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Ty {
    pub kind: TyKind,
    pub span: Span,
}

impl Default for Ty {
    fn default() -> Self {
        Self {
            kind: TyKind::default(),
            span: Span::default(),
        }
    }
}

impl Ty {
    pub fn default_unit_type(start: Span) -> Self {
        Ty {
            kind: TyKind::Tup(Vec::new()),
            // TODO(Simon): are these correct and do we really need these
            span: Span::new(start.lo + 4, start.hi + 6),
        }
    }

    pub fn default_infer_type(span: Span) -> Self {
        Self {
            kind: TyKind::Infer(DUMMY_TYPE_ID),
            span,
        }
    }

    pub fn new_unit(kind: Ty, span: Span) -> Self {
        Self {
            kind: TyKind::Tup(vec![kind]), // NOTE(Simon): maybe we dont even need this, but I think it is going to make type checking easier later on
            span,
        }
    }

    pub fn new(kind: TyKind, span: Span) -> Self {
        Self { kind, span }
    }

    pub fn is_unit(&self) -> bool {
        match self.kind {
            TyKind::Tup(ref t) => t.len() == 1,
            _ => false,
        }
    }
}

// NOTE(Simon): we might need to adjust this threshold to avoid too many false positives
const WORD_CMP_TRESHOLD: f32 = 0.2;

pub struct Typer {
    stack: Vec<HashMap<String, Ty>>,
    fn_table: HashMap<String, FnDecl>,
    ty_table: HashMap<String, StructDecl>,
}

impl Typer {
    pub fn new() -> Self {
        Self {
            stack: Vec::new(),
            fn_table: HashMap::new(),
            ty_table: HashMap::new(),
        }
    }

    pub fn infer(&mut self, ast: &mut Vec<Stmt>) {
        self.stack.push(HashMap::new());
        ast.iter_mut().for_each(|stmt| stmt.accept(self));
    }

    fn infer_block(&mut self, b: &mut Block) {
        self.make_cxt();
        b.stmts.iter_mut().for_each(|stmt| stmt.accept(self));
        self.drop_cxt();
    }
    fn infer_vardef(&mut self, pat: &mut Ident, init: &mut Expr, ty: &mut Ty) {
        init.accept(self);
        self.insert_cxt(&pat.name, ty.clone());

        // if the user has not provided a type, we set it to the inferred expr type
        // but if the user has specified a type, we will use the specified type because it is
        // more likely it is correct, we are  going to emit in an error during the
        // type checking phase if the types are not compatible
        if let TyKind::Infer(_) = ty.kind {
            *ty = init.ty.clone();
        }
    }

    fn infer_var(&mut self, p: &Path) -> Ty {
        // can never fail because we only got there because len of p is 1, otherwiese we have to infer an enum
        let var = p.segments.first().unwrap();
        match self.lookup_cxt(&var.name) {
            Some(ty) => ty,
            None => {
                let mut err = self.span_err(
                    "Typenfehler",
                    format!(
                        "Wir haben die Variable `{}` nicht gefunden!",
                        var.name.bold()
                    )
                    // I don't get why we need the conversion here, String implements Into String
                    .as_str(),
                    &var.span,
                );
                self.find_similar_var_names(&var.name)
                    .iter()
                    .for_each(|sug| {
                        let sim = format!("{:.2}", sug.1 * 100.0);
                        err.add_suggestion(format!(
                            "Meintest du vielleicht `{}`? [Uebereinstimmung: {}%]",
                            sug.0.bold(),
                            sim
                        ))
                    });
                Ty::default()
            }
        }
    }

    fn infer_enum_arm(&self) {
        todo!()
    }

    fn make_cxt(&mut self) {
        self.stack.push(self.stack.last().unwrap().clone());
    }

    fn insert_cxt(&mut self, name: &String, ty: Ty) {
        self.stack.last_mut().unwrap().insert(name.to_string(), ty);
    }

    fn lookup_cxt(&self, name: &String) -> Option<Ty> {
        self.stack.last().unwrap().get(name).cloned()
    }

    fn drop_cxt(&mut self) {
        self.stack.pop();
    }

    fn find_similar_var_names(&mut self, needle: &String) -> Vec<(String, f32)> {
        let mut corpus = CorpusBuilder::new().arity(2).pad_full(Pad::Auto).finish();
        self.stack
            .last()
            .unwrap()
            .iter()
            .for_each(|(k, _)| corpus.add_text(k));
        corpus
            .search(needle, WORD_CMP_TRESHOLD)
            .into_iter()
            .map(|res| (res.text, res.similarity))
            .collect()
    }

    fn span_err<S: Into<String>>(&mut self, _desc: S, _msg: S, _span: &Span) -> Diagnostic {
        todo!();
    }

    // fn infer_branch(&mut self, _b: &mut Branch) {
    //     todo!();
    // }
}

impl Visitor for Typer {
    type Result = ();

    fn visit_stmt(&mut self, s: &mut Stmt) -> Self::Result {
        match s {
            Stmt::Block(ref mut b) => self.infer_block(b),
            Stmt::VarDef {
                ref mut pat,
                ref mut init,
                ref mut ty,
                ..
            } => self.infer_vardef(pat, init, ty),
            // TODO(Simon): typecheck branches
            // Stmt::If(b) => {
            //     self.infer_branch(b);
            // }
            _ => todo!(),
        }
    }

    fn visit_expr(&mut self, e: &mut Expr) -> Self::Result {
        match e.node {
            ExprKind::Binary {
                ref mut lhs,
                ref mut rhs,
                ..
            } => {
                lhs.accept(self);
                rhs.accept(self);
            }
            ExprKind::Logical {
                ref mut lhs,
                ref mut rhs,
                ..
            } => {
                lhs.accept(self);
                rhs.accept(self);
            }
            ExprKind::Lit(ref lit, _) => {
                e.ty.kind = match lit {
                    Lit::String(_) => TyKind::Text,
                    Lit::Bool(_) => TyKind::Bool,
                    Lit::Number(_) => TyKind::Num,
                };
            }
            ExprKind::Path(ref p) => {
                if p.segments.len() == 1 {
                    // unwrap can never fail
                    self.infer_var(p);
                } else {
                    self.infer_enum_arm();
                }
            }

            _ => unimplemented!(),
        }
    }
}
