use std::collections::HashMap;
use std::fmt;

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
    Eq(TyKind, TyKind),
}

impl TyCons {
    fn to_str(&self) -> String {
        match self {
            TyCons::Eq(a, b) => format!("{} == {}", a, b),
        }
    }
}

impl fmt::Debug for TyCons {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TyCons::Eq(lhs, rhs) => write!(f, "{} == {}", lhs.to_str(), rhs.to_str()),
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

    Infer(usize),

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
            TyKind::Infer(id) => format!("${}", id),
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

pub struct TypeAnnotatorPass {
    index: usize,
    stack: Vec<HashMap<String, TyKind>>,
    diagnostics: Vec<Diagnostic>,
}

impl TypeAnnotatorPass {
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

impl Visitor for TypeAnnotatorPass {
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
            ExprKind::Binary {
                ref mut lhs,
                ref mut rhs,
                ..
            } => {
                lhs.accept(self);
                rhs.accept(self);
            }
            ExprKind::Logical {
                ref mut rhs,
                ref mut lhs,
                ..
            } => {
                rhs.accept(self);
                lhs.accept(self);
            }
            ExprKind::Unary { ref mut rhs, .. } => {
                rhs.accept(self);
            }
            ExprKind::Struct {
                path: _,
                ref mut members,
                ..
            } => {
                for member in members {
                    member.init.accept(self);
                }
            }
            ExprKind::Tup(ref mut elems) | ExprKind::Array(ref mut elems) => {
                for elem in elems {
                    elem.accept(self);
                }
            }
            ExprKind::Assign {
                ref mut target,
                ref mut value,
            } => {
                target.accept(self);
                value.accept(self);
            }
            ExprKind::Range(ref mut lo, ref mut hi) => {
                lo.accept(self);
                hi.accept(self);
            }
            ExprKind::Field(ref mut lhs, ref mut ident) => {
                // TODO(Simon): do we need give the accessed field a type id?
                lhs.accept(self);
            }
            ExprKind::Call {
                ref mut callee,
                ref mut args,
            } => {
                callee.accept(self);
                for arg in args {
                    arg.accept(self);
                }
            }
            ExprKind::Index {
                ref mut callee,
                ref mut index,
            } => {
                callee.accept(self);
                index.accept(self);
            }
            ExprKind::This => {}
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
            Stmt::VarDef(ref mut vd) => {
                let id = self.new_ty_id();

                // NOTE(Simon): if the user has not provied a type for the vardef we assign it a new type id and try to infer it
                // NOTE(Simon): if a type is specified we assume the user has made the correct choice and leave his type in place
                if let TyKind::Infer(_) = vd.ty.kind {
                    vd.ty.kind = id.clone();
                }
                self.insert_cxt(vd.pat.lexeme.clone(), id);
                vd.init.accept(self);
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
                ref mut vardef,
                ref mut body,
                ..
            } => {
                let id = self.new_ty_id();
                self.insert_cxt(vardef.pat.lexeme.clone(), id.clone());
                vardef.ty.kind = id;
                vardef.init.accept(self);
                self.annotate_block(body);
            }
            Stmt::StructDecl(_) => {}
            Stmt::EnumDecl { .. } => {} // TODO(Simon): Provide enum for type inference
            Stmt::Ret(ref mut expr, ..) => expr.accept(self),
            Stmt::Break(_) | Stmt::Continue(_) => {}
        }
    }
}

pub struct TypeInferencePass {
    cons: Vec<TyCons>,
    stack: Vec<HashMap<String, TyKind>>,
    diagnostics: Vec<Diagnostic>,
}

impl TypeInferencePass {
    pub fn new() -> Self {
        Self {
            cons: Vec::new(),
            stack: Vec::new(),
            diagnostics: Vec::new(),
        }
    }

    pub fn infer(&mut self, ast: &mut Vec<Stmt>) {
        for stmt in ast {
            stmt.accept(self);
        }
        dbg!(&self.cons);
    }

    pub fn make_cxt(&mut self) {
        let env = match self.stack.last() {
            Some(env) => env.clone(),
            None => HashMap::new(),
        };
        self.stack.push(env);
    }

    pub fn drop_cxt(&mut self) {
        self.stack.pop();
    }

    fn get_local(&mut self, name: &str) -> Option<TyKind> {
        self.stack.last().unwrap().get(name).cloned()
    }

    fn infer_block(&mut self, block: &mut Block) {
        self.make_cxt();
        for stmt in &mut block.stmts {
            stmt.accept(self);
        }
        self.drop_cxt();
    }

    fn infer_fn(&mut self, fn_decl: &mut FnDecl) {
        self.make_cxt();
        for p in &mut fn_decl.head.params {
            self.insert_cxt(p.name.lexeme.clone(), p.ty.kind.clone());
        }
        self.infer_block(&mut fn_decl.body);
        self.drop_cxt();
    }

    fn insert_cxt(&mut self, name: String, tk: TyKind) {
        self.stack.last_mut().unwrap().insert(name.to_string(), tk);
    }

    fn add_con(&mut self, con: TyCons) {
        self.cons.push(con);
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

                self.add_con(TyCons::Eq(lhs.clone(), rhs.clone()));
                self.add_con(TyCons::Eq(lhs.clone(), TyKind::Num));
                self.add_con(TyCons::Eq(rhs.clone(), TyKind::Num));
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

                self.add_con(TyCons::Eq(lhs.clone(), rhs.clone()));
            }
            ExprKind::Unary {
                ref mut rhs,
                ref op,
            } => {
                rhs.accept(self);
                match op {
                    UnaryOp::Minus => self.add_con(TyCons::Eq(rhs.ty.kind.clone(), TyKind::Num)),
                    UnaryOp::Not => self.add_con(TyCons::Eq(rhs.ty.kind.clone(), TyKind::Bool)),
                }
            }
            ExprKind::Array(ref mut elems) => {
                // FIXME(Simon): This loop seems really horrible!!!
                let arr_len = elems.len();
                for i in 0..arr_len {
                    elems[i].accept(self);
                    // NOTE(Simon): This is O(n^2) complexity, and I am not even shure if we need all of the cross constraints in an array.
                    // NOTE(Simon): But because array literals are typically not really large I think it is fine for now. And if it's ever a problem
                    // NOTE(Simon): then there is this comment to remind me to implement a better solution.
                    for j in 0..arr_len {
                        if i == j {
                            break;
                        }
                        let lhs = elems[i].ty.kind.clone();
                        let rhs = elems[j].ty.kind.clone();
                        self.add_con(TyCons::Eq(lhs, rhs));
                    }
                }
            }
            ExprKind::Tup(ref mut elems) => {
                for e in elems {
                    e.accept(self);
                }
            }
            ExprKind::Struct {
                ref path,
                ref mut members,
            } => {
                for m in members {
                    m.init.accept(self);
                }
            }
            ExprKind::Path(_) => { // TODO(Simon): implement enum inference
            }
            ExprKind::Index {
                ref mut callee,
                ref mut index,
            } => {
                callee.accept(self);
                index.accept(self);

                self.add_con(TyCons::Eq(index.ty.kind.clone(), TyKind::Num));
            }
            ExprKind::Assign {
                ref mut target,
                ref mut value,
            } => {
                target.accept(self);
                value.accept(self);
                let t = target.ty.kind.clone();
                let v = target.ty.kind.clone();
                self.add_con(TyCons::Eq(t, v));
            }
            ExprKind::Range(ref mut lo, ref mut hi) => {
                lo.accept(self);
                hi.accept(self);
                self.add_con(TyCons::Eq(lo.ty.kind.clone(), TyKind::Num));
                self.add_con(TyCons::Eq(hi.ty.kind.clone(), TyKind::Num));
                self.add_con(TyCons::Eq(
                    e.ty.kind.clone(),
                    TyKind::Array(Box::new(Ty {
                        kind: TyKind::Num,
                        span: e.span,
                    })),
                ));
            }
            ExprKind::Field(ref mut callee, ref ident) => {
                callee.accept(self);
            }
            ExprKind::Lit(ref l) => {
                let tk = TyKind::from_lit(l);
                self.add_con(TyCons::Eq(e.ty.kind.clone(), tk));
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
                self.insert_cxt(vd.pat.lexeme.clone(), vd.ty.kind.clone());
                self.add_con(TyCons::Eq(vd.ty.kind.clone(), vd.init.ty.kind.clone()));
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
                self.add_con(TyCons::Eq(cond.ty.kind.clone(), TyKind::Bool));
                self.infer_block(body);
                for branch in else_branches {
                    branch.cond.accept(self);
                    self.add_con(TyCons::Eq(branch.cond.ty.kind.clone(), TyKind::Bool));
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
                self.add_con(TyCons::Eq(cond.ty.kind.clone(), TyKind::Bool));
                self.infer_block(body);
            }
            Stmt::For {
                ref mut vardef,
                ref mut body,
                ..
            } => {
                self.make_cxt();
                self.insert_cxt(vardef.pat.lexeme.clone(), vardef.ty.kind.clone());
                self.infer_block(body);
                self.drop_cxt();
                self.add_con(TyCons::Eq(
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
