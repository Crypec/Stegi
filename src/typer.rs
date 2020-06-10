use crate::cxt::Cxt;
use std::convert::TryFrom;
use std::fmt;

use crate::errors::*;
use crate::lexer::*;

use derivative::*;
//use ngrammatic::{CorpusBuilder, Pad}; TODO(Simon): reimplement

use crate::ast::*;
use crate::errors::Diagnostic;

// NOTE(Simon): we might need to adjust this threshold to avoid too many false positives
#[allow(dead_code)]
const WORD_CMP_TRESHOLD: f32 = 0.2;

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Clone)]
pub struct Ty {
    pub kind: TyKind,

    #[derivative(Debug = "ignore")]
    pub span: Span,
}

impl Ty {
    pub fn infer_internal(&mut self) {
        self.kind = self.kind.infer_internal_types();
    }

    pub fn default_unit_type(span: Span) -> Self {
        Ty {
            kind: TyKind::Tup(Vec::new()),
            // TODO(Simon): are these correct and do we really need these
            span,
        }
    }

    pub fn is_unit(&self) -> bool {
        match &self.kind {
            TyKind::Tup(t) if t.is_empty() => true,
            _ => false,
        }
    }
}

#[derive(Clone)]
enum Constraint {
    Eq(TyKind, TyKind),
}

impl fmt::Debug for Constraint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Constraint::Eq(lhs, rhs) => write!(f, "{} == {}", lhs.to_str(), rhs.to_str()),
        }
    }
}

#[allow(dead_code)]
pub const DUMMY_TYPE_ID: usize = std::usize::MAX;

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

    Infer,

    Id(usize),

    #[derivative(Debug = "transparent")]
    Poly(Ident),

    #[derivative(Debug = "transparent")]
    Path(Path),
}

impl fmt::Display for TyKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.to_str())
    }
}

impl TryFrom<Ident> for TyKind {
    type Error = ();
    fn try_from(ident: Ident) -> Result<TyKind, Self::Error> {
        match ident.lexeme.as_str() {
            "Zahl" => Ok(TyKind::Num),
            "Bool" => Ok(TyKind::Bool),
            "Text" => Ok(TyKind::Text),
            _ => Err(()),
        }
    }
}

impl TyKind {
    pub fn infer_internal_types(&self) -> TyKind {
        match self {
            TyKind::Path(ref p) if p.len() == 1 => {
                // NOTE(Simon): We expect interal compiler types to be a single name without any namespace information!
                // NOTE(Simon): Right now num, bool, and txt are interal types provided by the compiler
                let seg = &p.first().unwrap().lexeme;
                match seg.as_str() {
                    "Zahl" => TyKind::Num,
                    "Text" => TyKind::Text,
                    "Bool" => TyKind::Bool,
                    _ => self.clone(),
                }
            }
            TyKind::Array(ref t) => TyKind::Array(Box::new(Ty {
                kind: t.kind.infer_internal_types(),
                span: t.span,
            })),
            TyKind::Tup(ref elems) => {
                let mut new_types = Vec::new();
                for e in elems {
                    new_types.push(Ty {
                        kind: e.kind.infer_internal_types(),
                        span: e.span,
                    });
                }
                TyKind::Tup(new_types)
            }
            _ => self.clone(),
        }
    }

    fn from_lit(l: &Lit) -> Self {
        match l {
            Lit::Number(_) => TyKind::Num,
            Lit::String(_) => TyKind::Text,
            Lit::Bool(_) => TyKind::Bool,
        }
    }

    fn to_str(&self) -> String {
        match self {
            TyKind::Array(elem) => format!("[{}]", elem.kind),
            TyKind::Id(id) => format!("${}", id),
            TyKind::Infer => "infer".to_string(),
            TyKind::Poly(elem) => format!("${}$", elem.lexeme),
            TyKind::Num => "num".to_string(),
            TyKind::Bool => "bool".to_string(),
            TyKind::Path(p) => format!("{}", p),
            TyKind::Text => "txt".to_string(),
            TyKind::Tup(elems) => {
                let mut sb = String::from("(");
                for e in elems {
                    sb.push_str(format!("{}", e.kind).as_str());
                }
                sb.push(')');
                sb
            }
        }
    }
}

pub struct Typer {
    cxt: Cxt<String, TyKind>,
    subst: Vec<TyKind>,
    cons: Vec<Constraint>,
    diagnostics: Vec<Diagnostic>,
}

impl Typer {
    pub fn new() -> Self {
        Self {
            cons: Vec::new(),
            cxt: Cxt::new(),
            subst: Vec::new(),
            diagnostics: Vec::new(),
        }
    }

    fn new_id(&mut self) -> TyKind {
        let res = TyKind::Id(self.subst.len());
        self.subst.push(res.clone());
        res
    }

    pub fn infer_types(&mut self, ast: &mut AST) {
        for d in ast.iter_mut() {
            if let Decl::Fn(f) = d {
                self.infer_fn(f);
            }
        }
    }

    fn infer_fn(&mut self, f: &mut FnDecl) {
        self.cxt.make_clean();
        for p in f.header.params.iter() {
            match p.ty.kind {
                TyKind::Poly(_) => todo!(),
                _ => self.cxt.insert(p.name.lexeme.clone(), p.ty.kind.clone()),
            }
        }
    }

    pub fn span_err(&mut self, kind: ErrKind, span: Span) -> Diagnostic {
        let diag = Diagnostic {
            kind,
            suggestions: Vec::new(),
            span,
        };
        self.diagnostics.push(diag.clone());
        diag
    }

    fn check_enum_arm(&mut self, enum_arm: Path) -> Result<Ty, Diagnostic> {
        let name = enum_arm.first().unwrap();
        todo!()
    }

    pub fn infer(&mut self, e: &Expr) -> Result<TyKind, Diagnostic> {
        match e.node {
            ExprKind::Binary {
                ref lhs,
                op: _,
                ref rhs,
            } => {
                let lhs = self.infer(lhs)?;
                let rhs = self.infer(rhs)?;
                self.cons.push(Constraint::Eq(lhs, TyKind::Num));
                self.cons.push(Constraint::Eq(rhs, TyKind::Num));
                Ok(TyKind::Num)
            }
            ExprKind::Logical {
                ref lhs,
                op: _,
                ref rhs,
            } => {
                let lhs = self.infer(lhs)?;
                let rhs = self.infer(rhs)?;
                self.cons.push(Constraint::Eq(lhs, TyKind::Bool));
                self.cons.push(Constraint::Eq(rhs, TyKind::Bool));
                Ok(TyKind::Bool)
            }
            ExprKind::Unary { ref rhs, ref op } => {
                let rhs = self.infer(rhs)?;
                let tk = match op {
                    UnaryOp::Minus => TyKind::Num,
                    UnaryOp::Not => TyKind::Bool,
                };
                self.cons.push(Constraint::Eq(rhs, tk.clone()));
                Ok(tk)
            }
            ExprKind::Array(ref arr) => {
                let elem_ty = match arr.first() {
                    Some(e) => self.infer(e)?,
                    None => self.new_id(),
                };
                for elem in arr {
                    self.cons
                        .push(Constraint::Eq(elem.ty.kind.clone(), elem_ty.clone()));
                }
                Ok(elem_ty)
            }
            ExprKind::Tup(ref tup) => {
                let mut t = Vec::new();
                for elem in tup {
                    t.push(Ty {
                        span: elem.span,
                        kind: self.infer(elem)?,
                    });
                }
                Ok(TyKind::Tup(t))
            }
            ExprKind::Path(ref path) => {
                let name = path.first().unwrap().lexeme.clone();
                match path.len() {
                    1 => match self.cxt.get(&name) {
                        Some(tk) => Ok(tk.clone()),
                        None => Err(self.span_err(
                            ErrKind::Type(TypeErr::VarNotFound(name.clone())),
                            path.span,
                        )),
                    },
                    _ => {
                        // NOTE(Simon): Handle enums
                        let name = path.first().unwrap();
                        todo!();
                    }
                }
            }
            ExprKind::Struct {
                ref name,
                ref members,
            } => todo!(),
            ExprKind::Range(ref from, ref to) => {
                let ty = Ty {
                    kind: TyKind::Num,
                    span: from.span.combine(&to.span),
                };
                Ok(TyKind::Array(Box::new(ty)))
            }
            ExprKind::Lit(ref lit) => Ok(Self::infer_lit(lit)),
            ExprKind::Index {
                ref callee,
                ref index,
            } => todo!(),
            ExprKind::This {} => todo!(),
            ExprKind::Call {
                ref callee,
                ref args,
            } => todo!(),
            ExprKind::Intrinsic { ref kind, ref args } => todo!(),
            ExprKind::Field(ref callee, ref field) => todo!(),
            ExprKind::Val(ref val) => todo!(),
        }
    }
    fn infer_lit(lit: &Lit) -> TyKind {
        match lit {
            Lit::Number(_) => TyKind::Num,
            Lit::String(_) => TyKind::Text,
            Lit::Bool(_) => TyKind::Bool,
        }
    }
}

impl Visitor for Typer {
    type Result = ();
    fn visit_decl(&mut self, decl: &mut Decl) -> Self::Result {
        match decl {
            Decl::Fn(f) => self.infer_fn(f),
            _ => {}
        }
    }
    fn visit_stmt(&mut self, stmt: &mut Stmt) -> Self::Result {}
    fn visit_expr(&mut self, expr: &mut Expr) -> Self::Result {}
}
