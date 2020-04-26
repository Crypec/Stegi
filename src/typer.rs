use std::collections::HashMap;
use std::convert::TryFrom;
use std::fmt;

use crate::errors::Severity;
use crate::lexer::*;

use derivative::*;
//use ngrammatic::{CorpusBuilder, Pad}; TODO(Simon): reimplement

use crate::ast::*;
use crate::errors::Diagnostic;

// NOTE(Simon): we might need to adjust this threshold to avoid too many false positives
const WORD_CMP_TRESHOLD: f32 = 0.2;

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Clone)]
pub struct Ty {
    pub kind: TyKind,

    #[derivative(Debug = "ignore")]
    pub span: Span,
}

#[derive(Clone)]
enum Constraint {
    Eq(TyKind, TyKind),
}

impl Constraint {
    fn to_str(&self) -> String {
        match self {
            Constraint::Eq(a, b) => format!("{} == {}", a, b),
        }
    }
}

impl fmt::Debug for Constraint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Constraint::Eq(lhs, rhs) => write!(f, "{} == {}", lhs.to_str(), rhs.to_str()),
        }
    }
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

struct Cxt(Vec<HashMap<String, TyKind>>);

impl Cxt {
    fn new() -> Self {
        let mut v = Vec::new();
        v.push(HashMap::new());
        Self(v)
    }

    fn make(&mut self) {
        let env = match self.0.last() {
            Some(env) => env.clone(),
            None => HashMap::new(),
        };
        self.0.push(env)
    }

    fn drop(&mut self) {
        self.0.pop();
    }

    fn insert(&mut self, n: &str, t: TyKind) {
        self.0.last_mut().unwrap().insert(n.to_string(), t);
    }

    fn get(&self, s: &str) -> Option<TyKind> {
        self.0.last().unwrap().get(s).cloned()
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
}

pub struct TypeInferencePass {
    cons: Vec<Constraint>,
    ty_id_index: usize,
    cxt: Cxt,
    subst: Vec<TyKind>,
    diagnostics: Vec<Diagnostic>,
}

impl TypeInferencePass {
    pub fn new() -> Self {
        Self {
            ty_id_index: 0,
            cons: Vec::new(),
            cxt: Cxt::new(),
            subst: Vec::new(),
            diagnostics: Vec::new(),
        }
    }

    pub fn infer(&mut self, ast: &mut Vec<Stmt>) {
        for stmt in ast {
            stmt.accept(self);
        }
    }

    fn infer_block(&mut self, block: &mut Block) {
        self.cxt.make();
        for stmt in &mut block.stmts {
            stmt.accept(self);
        }
        self.cxt.drop()
    }

    fn infer_fn(&mut self, fn_decl: &mut FnDecl) {
        self.cxt.make();
        for p in &mut fn_decl.head.params {
            self.cxt.insert(&p.name.lexeme, p.ty.kind.clone());
        }
        self.infer_block(&mut fn_decl.body);
        self.cxt.drop();
    }

    fn add_con(&mut self, con: Constraint) {
        self.cons.push(con);
    }

    fn new_ty_id(&mut self) -> TyKind {
        let id = self.ty_id_index;
        self.ty_id_index += 1;
        TyKind::Id(id)
    }

    fn span_err<S: Into<String>>(&mut self, msg: S, span: Span) {
        let diag = Diagnostic::new(
            "Typenfehler",
            &msg.into(),
            Vec::new(),
            Severity::Fatal,
            span,
        );
        self.diagnostics.push(diag);
    }
}

impl Visitor for TypeInferencePass {
    type Result = ();

    fn visit_expr(&mut self, e: &mut Expr) {
        match e.node {
            ExprKind::Binary {
                ref mut rhs,
                ref mut lhs,
                ..
            } => {
                lhs.accept(self);
                rhs.accept(self);
                let lhs = &lhs.ty.kind;
                let rhs = &rhs.ty.kind;

                self.add_con(Constraint::Eq(lhs.clone(), rhs.clone()));
                self.add_con(Constraint::Eq(lhs.clone(), TyKind::Num));
                self.add_con(Constraint::Eq(rhs.clone(), TyKind::Num));
            }
            ExprKind::Logical {
                ref mut lhs,
                ref mut rhs,
                ..
            } => {
                lhs.accept(self);
                rhs.accept(self);
                let lhs = &lhs.ty.kind;
                let rhs = &rhs.ty.kind;
                self.add_con(Constraint::Eq(lhs.clone(), rhs.clone()));
            }
            ExprKind::Unary {
                ref mut rhs,
                ref op,
            } => {
                rhs.accept(self);
                match op {
                    UnaryOp::Minus => {
                        self.add_con(Constraint::Eq(rhs.ty.kind.clone(), TyKind::Num))
                    }
                    UnaryOp::Not => self.add_con(Constraint::Eq(rhs.ty.kind.clone(), TyKind::Bool)),
                }
            }
            ExprKind::Array(ref mut elems) => {
                let elem_ty = match elems.first() {
                    Some(t) => t.ty.kind.clone(),
                    None => self.new_ty_id(),
                };
                for e in elems {
                    e.accept(self);
                    self.add_con(Constraint::Eq(e.ty.kind.clone(), elem_ty.clone()));
                }
            }
            ExprKind::Tup(ref mut elems) => {
                for e in elems {
                    e.accept(self);
                }
            }
            ExprKind::Struct {
                path: _,
                ref mut members,
            } => {
                for m in members {
                    m.init.accept(self);
                }
            }
            ExprKind::Path(ref p) => {
                // TODO(Simon): implement enum inference
                if p.len() == 1 {
                    let name = p.first().unwrap().lexeme.clone();

                    if let None = self.cxt.get(&name) {
                        self.span_err(format!("Variable nicht gefuden: `{}`", name), p.span);
                        let id = self.new_ty_id();
                        self.cxt.insert(&name, id.clone());
                        e.ty.kind = id.clone();
                        self.add_con(Constraint::Eq(id.clone(), e.ty.kind.clone()));
                    }
                }
            }
            ExprKind::Index {
                ref mut callee,
                ref mut index,
            } => {
                callee.accept(self);
                index.accept(self);

                self.add_con(Constraint::Eq(index.ty.kind.clone(), TyKind::Num));
            }
            ExprKind::Assign {
                ref mut target,
                ref mut value,
            } => {
                target.accept(self);
                value.accept(self);
                let t = target.ty.kind.clone();
                let v = target.ty.kind.clone();
                self.add_con(Constraint::Eq(t, v));
            }
            ExprKind::Range(ref mut lo, ref mut hi) => {
                lo.accept(self);
                hi.accept(self);
                self.add_con(Constraint::Eq(lo.ty.kind.clone(), TyKind::Num));
                self.add_con(Constraint::Eq(hi.ty.kind.clone(), TyKind::Num));
                self.add_con(Constraint::Eq(
                    e.ty.kind.clone(),
                    TyKind::Array(Box::new(Ty {
                        kind: TyKind::Num,
                        span: e.span,
                    })),
                ));
            }
            ExprKind::Field(ref mut callee, ref _ident) => {
                callee.accept(self);
            }
            ExprKind::Lit(ref l) => {
                e.ty.kind = TyKind::from_lit(l);
            }
            ExprKind::Call {
                ref mut callee,
                ref mut args,
            } => {
                callee.accept(self);
                for a in args {
                    a.accept(self);
                }
            }
            ExprKind::This => {}
        }
    }
    fn visit_stmt(&mut self, s: &mut Stmt) {
        match s {
            Stmt::Block(ref mut block) => {
                self.infer_block(block);
            }
            Stmt::VarDef(ref mut vd) => {
                vd.init.accept(self);

                if vd.ty.kind == TyKind::Infer {
                    vd.ty.kind = self.new_ty_id();
                }

                self.cxt.insert(&vd.pat.lexeme, vd.ty.kind.clone());
                self.add_con(Constraint::Eq(vd.ty.kind.clone(), vd.init.ty.kind.clone()));
            }
            Stmt::Ret(ref mut val, ..) => {
                // FIXME(Simon): we should have a constrait to the return type of the function
                val.accept(self);
            }
            Stmt::FnDecl(ref mut fn_decl) => {
                self.infer_fn(fn_decl);
            }
            Stmt::If {
                ref mut cond,
                ref mut body,
                ref mut else_branches,
                ref mut final_branch,
                ..
            } => {
                cond.accept(self);
                self.add_con(Constraint::Eq(cond.ty.kind.clone(), TyKind::Bool));
                self.infer_block(body);
                for branch in else_branches {
                    branch.cond.accept(self);
                    self.add_con(Constraint::Eq(branch.cond.ty.kind.clone(), TyKind::Bool));
                }
                if let Some(fb) = final_branch {
                    self.infer_block(&mut fb.body);
                }
            }
            Stmt::While {
                ref mut cond,
                ref mut body,
                ..
            } => {
                cond.accept(self);
                self.add_con(Constraint::Eq(cond.ty.kind.clone(), TyKind::Bool));
                self.infer_block(body);
            }
            Stmt::For {
                ref mut vardef,
                ref mut body,
                ..
            } => {
                self.cxt.make();
                self.cxt.insert(&vardef.pat.lexeme, vardef.ty.kind.clone());
                self.infer_block(body);
                self.cxt.drop();
                self.add_con(Constraint::Eq(
                    TyKind::Array(Box::new(Ty {
                        kind: vardef.ty.kind.clone(),
                        span: vardef.init.span,
                    })),
                    vardef.init.ty.kind.clone(),
                ));
            }
            Stmt::ImplBlock {
                ref mut fn_decls, ..
            } => {
                for fn_decl in fn_decls {
                    self.infer_fn(fn_decl);
                }
            }
            Stmt::Expr(ref mut e) => e.accept(self),
            Stmt::Break(_) | Stmt::Continue(_) | Stmt::StructDecl(..) | Stmt::EnumDecl { .. } => {}
        }
    }
}
