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
        self.kind = self.kind.infer_internal();
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
    pub fn infer_internal(&self) -> TyKind {
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
                kind: t.kind.infer_internal(),
                span: t.span,
            })),
            TyKind::Tup(ref elems) => {
                let mut new_types = Vec::new();
                for e in elems {
                    new_types.push(Ty {
                        kind: e.kind.infer_internal(),
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

pub struct TyConsGen {
    cxt: Cxt<String, TyKind>,
    subst: Vec<TyKind>,
    cons: Vec<Constraint>,
    diagnostics: Vec<Diagnostic>,
}

impl TyConsGen {
    pub fn new() -> Self {
        Self {
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
        println!("=============== cons: ===============");
        self.cons.iter().for_each(|c| println!("{:#?}", c));
        self.diagnostics.iter().for_each(|c| println!("{:#?}", c));
        self.solve_cons();
        println!("\n=============== subst: ===============");
        self.subst.iter().for_each(|c| println!("{:#?}", c));
    }

    fn solve_cons(&mut self) {
        self.cons
            .clone()
            .iter()
            .map(|Constraint::Eq(t1, t2)| (t1, t2))
            .for_each(|(t1, t2)| self.unify(t1, t2));
    }

    fn infer_block(&mut self, block: &mut Block) {
        self.cxt.make();
        for stmt in &mut block.stmts {
            stmt.accept(self);
        }

        self.cxt.drop()
    }

    fn new_id(&mut self) -> TyKind {
        let i = self.subst.len();
        self.subst.push(TyKind::Id(i));
        TyKind::Id(i)
    }

    fn infer_fn(&mut self, fn_decl: &mut FnDecl) {
        self.cxt.make();
        for p in &mut fn_decl.head.params {
            self.cxt.insert(p.name.lexeme.clone(), p.ty.kind.clone());
        }
        self.infer_block(&mut fn_decl.body);
        self.cxt.drop();
    }

    fn add_con(&mut self, con: Constraint) {
        self.cons.push(con);
    }

    fn span_err(&mut self, kind: ErrKind, span: Span) {
        let diag = Diagnostic {
            kind,
            suggestions: Vec::new(),
            span,
        };
        self.diagnostics.push(diag);
    }

    fn unify(&mut self, t1: &TyKind, t2: &TyKind) {
        match (t1, t2) {
            (TyKind::Id(i), _) if self.get_subst(i) != TyKind::Id(*i) => {
                let t3 = self.get_subst(i);
                self.unify(&t3, t2);
            }
            (_, TyKind::Id(i)) if self.get_subst(i) != TyKind::Id(*i) => {
                let t3 = self.get_subst(i);
                self.unify(t1, &t3);
            }
            (TyKind::Id(i), _) => {
                if self.occurs_in(*i, t2) {
                    self.span_err(
                        ErrKind::Type(TypeErr::InfRec(t1.clone(), t2.clone())),
                        Span::default(),
                    );
                    return;
                }
                self.subst[*i] = t2.clone();
            }
            (_, TyKind::Id(i)) => {
                if self.occurs_in(*i, t1) {
                    self.span_err(
                        ErrKind::Type(TypeErr::InfRec(t1.clone(), t2.clone())),
                        Span::default(),
                    );
                    return;
                }
                self.subst[*i] = t1.clone();
            }
            _ => panic!("{:#?}", (t1, t2)),
        }
    }

    fn occurs_in(&self, index: usize, t: &TyKind) -> bool {
        match t {
            TyKind::Id(i) if self.get_subst(i) != TyKind::Id(*i) => {
                self.occurs_in(index, &self.get_subst(i))
            }
            TyKind::Id(i) => *i == index,
            _ => false,
        }
    }

    fn get_subst(&self, i: &usize) -> TyKind {
        self.subst.get(*i).unwrap().clone()
    }
}

impl Visitor for TyConsGen {
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
                let lk = &lhs.ty.kind;
                let rk = &rhs.ty.kind;
                self.add_con(Constraint::Eq(lk.clone(), rk.clone()));
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
                    None => self.new_id(),
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
                    e.ty.kind = match self.cxt.get(&name) {
                        Some(ty) => ty.clone(),
                        None => {
                            self.span_err(
                                ErrKind::Type(TypeErr::VarNotFound(name.clone())),
                                p.span,
                            );
                            let id = self.new_id();
                            self.cxt.insert(name.clone(), id.clone());
                            id
                        }
                    };
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
            ExprKind::Val(_) => todo!(),
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
                    vd.ty.kind = self.new_id();
                }

                self.cxt.insert(vd.pat.lexeme.clone(), vd.ty.kind.clone());
                self.add_con(Constraint::Eq(vd.ty.kind.clone(), vd.init.ty.kind.clone()));
            }
            Stmt::Assign {
                ref mut lhs,
                ref mut rhs,
                span: _,
            } => {
                lhs.accept(self);
                rhs.accept(self);
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
                self.cxt
                    .insert(vardef.pat.lexeme.clone(), vardef.ty.kind.clone());
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
