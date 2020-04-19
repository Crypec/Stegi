use std::collections::HashMap;

use crate::errors::Severity;
use crate::lexer::*;

use derivative::*;
//use ngrammatic::{CorpusBuilder, Pad}; TODO(Simon): reimplement

use crate::ast::*;
use crate::errors::Diagnostic;

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Clone)]
pub struct Ty {
    pub kind: TyKind,

    #[derivative(Debug = "ignore")]
    pub span: Span,
}

enum TyCons {
    Eq(Ty, Ty),
}

pub const DUMMY_TYPE_ID: usize = usize::MAX;

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Clone)]
pub enum TyKind {
    #[derivative(Debug = "transparent")]
    Array(Box<Ty>),

    #[derivative(Debug = "transparent")]
    Tup(Vec<Ty>),

    Num,

    Bool,

    Text,

    Infer(usize),

    #[derivative(Debug = "transparent")]
    Poly(Ident),

    #[derivative(Debug = "transparent")]
    Path(Path),
}

impl TyKind {
    fn from_lit(l: &Lit) -> Self {
        match l {
            Lit::Number(_) => TyKind::Num,
            Lit::String(_) => TyKind::Text,
            Lit::Bool(_) => TyKind::Bool,
        }
    }
}

impl Ty {
    pub fn default_unit_type(span: Span) -> Self {
        Ty {
            kind: TyKind::Tup(Vec::new()),
            // TODO(Simon): are these correct and do we really need these
            span,
        }
    }

    pub fn default_infer_type(span: Span) -> Self {
        Self {
            kind: TyKind::Infer(DUMMY_TYPE_ID),
            span,
        }
    }
}

// NOTE(Simon): we might need to adjust this threshold to avoid too many false positives
const WORD_CMP_TRESHOLD: f32 = 0.2;

pub struct TypeAnnotator {
    index: usize,
    stack: Vec<HashMap<String, TyKind>>,
    diagnostics: Vec<Diagnostic>,
}

impl TypeAnnotator {
    pub fn new() -> Self {
        Self {
            index: 0,
            stack: Vec::new(),
            diagnostics: Vec::new(),
        }
    }

    fn new_ty_id(&mut self) -> TyKind {
        let id = self.index;
        self.index += 1;
        TyKind::Infer(id)
    }

    pub fn annotate(&mut self, ast: &mut Vec<Stmt>) -> Vec<Diagnostic> {
        ast.into_iter().for_each(|s| s.accept(self));
        self.diagnostics.clone()
    }

    pub fn annotate_block(&mut self, block: &mut Block) {
        self.make_cxt();
        for stmt in &mut block.stmts {
            stmt.accept(self);
        }
        self.destroy_cxt();
    }

    pub fn annotate_fn(&mut self, fn_decl: &mut FnDecl) {
        for param in &mut fn_decl.head.params {
            self.insert_cxt(param.name.lexeme.clone(), param.ty.kind.clone());
        }
        self.annotate_block(&mut fn_decl.body);
    }

    pub fn make_cxt(&mut self) {
        let env = match self.stack.last() {
            Some(env) => env.clone(),
            None => HashMap::new(),
        };
        self.stack.push(env);
    }

    pub fn destroy_cxt(&mut self) {
        self.stack.pop();
    }

    fn get_local(&mut self, name: &str) -> Option<TyKind> {
        self.stack.last().unwrap().get(name).cloned()
    }

    fn insert_cxt(&mut self, name: String, tk: TyKind) {
        self.stack.last_mut().unwrap().insert(name.to_string(), tk);
    }

    fn span_err<S: Into<String>>(&mut self, msg: S, span: Span) {
        self.diagnostics.push(Diagnostic::new(
            "Typenfehler",
            &msg.into(),
            Vec::new(),
            Severity::Fatal,
            span,
        ))
    }
}

impl Visitor for TypeAnnotator {
    type Result = ();

    fn visit_expr(&mut self, e: &mut Expr) -> Self::Result {
        match e.node {
            ExprKind::Lit(ref l) => {
                e.ty = Ty {
                    kind: TyKind::from_lit(l),
                    span: e.span,
                }
            }
            ExprKind::Path(ref p) => {
                if p.len() == 1 {
                    let seg = p.first().unwrap();
                    e.ty.kind = match self.get_local(&seg.lexeme) {
                        Some(tk) => tk,
                        None => {
                            self.span_err(
                                format!("Wir konnten die Variable `{}`, nicht finden!", seg.lexeme),
                                seg.span,
                            );
                            return;
                        }
                    };
                }
            }
            _ => todo!(),
        }
    }

    fn visit_stmt(&mut self, s: &mut Stmt) -> Self::Result {
        match s {
            Stmt::FnDecl(ref mut fn_decl) => {
                self.annotate_fn(fn_decl);
            }
            Stmt::Block(b) => {
                self.annotate_block(b);
            }
            Stmt::VarDef {
                ref pat,
                ref mut ty,
                ref mut init,
                ..
            } => {
                let id = self.new_ty_id();

                // NOTE(Simon): if the user has not provied a type for the vardef we assign it a new type id and try to infer it
                // NOTE(Simon): if a type is specified we assume the user has made the correct choice and leave his type in place
                if let TyKind::Infer(_) = ty.kind {
                    ty.kind = id.clone();
                }
                self.insert_cxt(pat.lexeme.clone(), id);
                init.accept(self);
            }
            Stmt::Expr(ref mut e) => {
                e.accept(self);
            }
            Stmt::If {
                ref mut cond,
                ref mut body,
                ref mut else_branches,
                ref mut final_branch,
                ..
            } => {
                cond.accept(self);
                self.annotate_block(body);
                for branch in else_branches {
                    branch.cond.accept(self);
                    self.annotate_block(&mut branch.body);
                }
                if let Some(fb) = final_branch {
                    self.annotate_block(&mut fb.body);
                }
            }
            Stmt::While {
                ref mut cond,
                ref mut body,
                ..
            } => {
                cond.accept(self);
                self.annotate_block(body);
            }
            Stmt::ImplBlock {
                target: _,
                ref mut fn_decls,
                ..
            } => {
                for fn_decl in fn_decls {
                    self.annotate_fn(fn_decl);
                }
            }
            Stmt::For {
                ref mut var,
                ref mut it,
                ref mut ty,
                ref mut body,
                ..
            } => {
                let id = self.new_ty_id();
                self.insert_cxt(var.lexeme.clone(), id.clone());
                ty.kind = id;
                it.accept(self);
                self.annotate_block(body);
            }
            Stmt::StructDecl(_) => {}
            Stmt::EnumDecl { .. } => {} // TODO(Simon): Provide enum for type inference
            Stmt::Ret(ref mut expr, ..) => expr.accept(self),
            Stmt::Break(_) | Stmt::Continue(_) => {}
        }
    }
}
