use crate::cxt::Cxt;
use std::collections::*;
use std::convert::TryFrom;
use std::fmt;

use crate::ast::Path;

use crate::errors::*;
use crate::lexer::*;

use derivative::*;
use itertools::Itertools;
//use ngrammatic::{CorpusBuilder, Pad}; TODO(Simon): reimplement

use crate::ast::*;
use crate::errors::Diagnostic;

macro_rules! is_type(
    ($val:expr, $p:pat) => {
        match $val {
            $p => true,
            _ => false,
        }
    }
);

// NOTE(Simon): we might need to adjust this threshold to avoid too many false positives
#[allow(dead_code)]
const WORD_CMP_TRESHOLD: f32 = 0.2;

#[derive(PartialEq, Derivative)]
#[derivative(Debug, Clone)]
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
    Eq(Ty, Ty),
}

impl fmt::Debug for Constraint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Constraint::Eq(lhs, rhs) => write!(f, "{} == {}", lhs, rhs),
        }
    }
}

#[allow(dead_code)]
pub const DUMMY_TYPE_ID: usize = std::usize::MAX;

#[derive(PartialEq, Derivative)]
#[derivative(Debug, Clone)]
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

    Fn(Vec<Ty>, Box<Ty>),

    #[derivative(Debug = "transparent")]
    Poly(Ident),

    #[derivative(Debug = "transparent")]
    Struct(Struct),

    #[derivative(Debug = "transparent")]
    Enum(Enum),

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
                span: t.span.clone(),
            })),
            TyKind::Tup(ref elems) => {
                let mut new_types = Vec::new();
                for e in elems {
                    new_types.push(Ty {
                        kind: e.kind.infer_internal_types(),
                        span: e.span.clone(),
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
            TyKind::Infer => "Infer".to_string(),
            TyKind::Poly(elem) => format!("${}$", elem.lexeme),
            TyKind::Num => "Zahl".to_string(),
            TyKind::Bool => "Bool".to_string(),
            TyKind::Path(p) => format!("{}", p),
            TyKind::Text => "Text".to_string(),
            TyKind::Fn(params, ret) => {
                let params = params.iter().map(|p| format!("{}", p)).join(",");
                format!("fun: ({}) -> {}", params, ret)
            }
            TyKind::Tup(elems) => {
                let mut sb = String::from("(");
                for e in elems {
                    sb.push_str(format!("{}", e.kind).as_str());
                }
                sb.push(')');
                sb
            }
            // FIXME(Simon): do some propper pretty printing
            TyKind::Struct(strct) => format!("struct: {}", strct.name.lexeme),
            TyKind::Enum(enm) => format!("enum: {}", enm.name.lexeme),
        }
    }

    pub fn empty_array_ty(span: Span) -> Self {
        TyKind::Array(box Ty {
            kind: TyKind::Infer,
            span,
        })
    }
}

pub struct Typer;

impl Typer {
    pub fn new() -> Self {
        Self
    }

    pub fn infer(&self, ast: &mut AST) -> Vec<Diagnostic> {
        let mut errs = Vec::new();
        errs.extend(TyLoweringPass::new().apply(ast));
        errs.extend(TyInferencePrePass::new().apply(ast));
        // let (subst, diags) = TyConsGenPass::new().gen(ast);
        // if !diags.is_empty() {
        //     errs.extend(diags);
        //     return errs;
        // }

        // TypeSubstitutor::new(subst).apply_subst(ast);
        Vec::new()
    }
}

pub struct TyLoweringPass {
    ty_table: HashMap<String, TyDecl>,
}

impl TyLoweringPass {
    fn new() -> Self {
        Self {
            ty_table: HashMap::new(),
        }
    }
    fn apply(&mut self, ast: &mut AST) -> Vec<Diagnostic> {
        let mut diag = Vec::new();
        self.fill_ty_table(&ast);
        for decl in ast.iter_mut() {
            match decl {
                Decl::TyDecl(TyDecl::Struct(s)) => {
                    for (_, ty) in s.fields.iter_mut() {
                        if !self.is_available(&ty) {
                            diag.push(Diagnostic {
                                kind: ErrKind::Type(TypeErr::TyNotFound(format!("{}", &ty))),
                                span: ty.span.clone(),
                                suggestions: Vec::new(),
                            })
                        }
                        ty.infer_internal();
                    }
                }
                Decl::TyDecl(TyDecl::Enum(e)) => {
                    for var in e.variants.iter_mut() {
                        if let VariantData::Val(ref mut elems) = var.data {
                            for e in elems.iter_mut() {
                                if !self.is_available(&e) {
                                    diag.push(Diagnostic {
                                        kind: ErrKind::Type(TypeErr::TyNotFound(format!("{}", &e))),
                                        span: e.span.clone(),
                                        suggestions: Vec::new(),
                                    })
                                }
                                e.infer_internal();
                            }
                        }
                    }
                }
                Decl::Fn(ref mut f) => {
                    for p in &mut f.header.params {
                        p.ty.infer_internal();
                    }
                    f.header.ret_ty.infer_internal();
                }
                _ => continue,
            }
        }
        diag
    }

    fn is_available(&self, ty: &Ty) -> bool {
        match ty.kind {
            TyKind::Num | TyKind::Text | TyKind::Bool => true,
            TyKind::Array(ref elem) => self.is_available(elem),
            TyKind::Path(ref path) => {
                if path.len() > 1 {
                    panic!(
                        "Externe Typenmodule sind zum aktuellen Zeitpunkt noch nicht unterstuezt!"
                    );
                } else {
                    self.ty_table.contains_key(&path.first().unwrap().lexeme)
                }
            }
            TyKind::Tup(ref elems) => elems.iter().any(|e| !self.is_available(&e)),
            TyKind::Id(_)
            | TyKind::Infer
            | TyKind::Enum(_)
            | TyKind::Struct(_)
            | TyKind::Fn(..)
            | TyKind::Poly(_) => false,
        }
    }

    fn fill_ty_table(&mut self, ast: &AST) {
        for d in ast.iter() {
            if let Decl::TyDecl(t) = d {
                self.ty_table.insert(t.name().lexeme.clone(), t.clone());
            }
        }
    }
}

struct TyInferencePrePass {
    cxt: Cxt<String, Ty>,
    ty_table: HashMap<String, TyDecl>,
    err: Vec<Diagnostic>,
}

impl TyInferencePrePass {
    fn new() -> Self {
        Self {
            cxt: Cxt::new(),
            ty_table: HashMap::new(),
            err: Vec::new(),
        }
    }

    fn fill_ty_table(&mut self, ast: &AST) {
        for d in ast.iter() {
            if let Decl::TyDecl(t) = d {
                self.ty_table.insert(t.name().lexeme.clone(), t.clone());
            }
        }
    }

    fn apply(&mut self, ast: &mut AST) -> Vec<Diagnostic> {
        self.fill_ty_table(ast);
        for node in ast {
            node.accept(self)
        }
        self.err.clone()
    }

    fn infer_block(&mut self, block: &mut Block) {
        self.cxt.push_scope();
        for stmt in &mut block.stmts {
            stmt.accept(self)
        }
        self.cxt.pop_scope();
    }

    fn infer_fn(&mut self, f: &mut FnDecl) {
        self.cxt.push_frame();
        for param in &f.header.params {
            self.cxt.insert(param.name.lexeme.clone(), param.ty.clone());
        }
        self.infer_block(&mut f.body);
        self.cxt.pop_frame();
    }

    pub fn infer_expr(&mut self, e: &mut Expr) {
        e.accept(self);
    }

    fn match_assign(&mut self, target: &AssingKind) -> Option<Ty> {
        match target {
            AssingKind::Var(var) => match self.cxt.get(&var.lexeme) {
                Some(t) => Some(t.clone()),
                None => {
                    self.span_err(TypeErr::VarNotFound(var.lexeme.clone()), var.span.clone());
                    None
                }
            },
            AssingKind::Field {
                ref callee,
                ref name,
            } => match self.match_assign(callee) {
                Some(t) => {
                    if let TyKind::Struct(s) = t.kind {
                        match s.fields.get(&name) {
                            Some(t) => Some(t.clone()),
                            None => {
                                self.span_err(
                                    TypeErr::FieldNotFound {
                                        ty: TyKind::Struct(s),
                                        field: name.lexeme.clone(),
                                    },
                                    name.span.clone(),
                                );
                                None
                            }
                        }
                    } else {
                        self.span_err(
                            TypeErr::FieldNotFound {
                                ty: t.kind,
                                field: name.lexeme.clone(),
                            },
                            name.span.clone(),
                        );
                        None
                    }
                }
                None => return None,
            },
            AssingKind::Index { ref callee, .. } => match self.match_assign(callee) {
                Some(t) => {
                    if let TyKind::Array(ref elem) = t.kind {
                        Some(*elem.clone())
                    } else {
                        self.span_err(
                            TypeErr::InvalidType {
                                expected: TyKind::empty_array_ty(Span::default()),
                                actual: t.clone(),
                            },
                            t.span.clone(),
                        );
                        None
                    }
                }
                None => None,
            },
        }
    }

    fn infer_struct_lit(&mut self, name: &Ident, members: &mut Vec<Member>) {
        let ty = self.cxt.get(&name.lexeme);
        match ty {
            Some(t) => {
                if let TyKind::Struct(s) = &t.kind {
                    for member in members {
                        match s.fields.get(&member.name) {
                            Some(tk) if *tk == member.init.ty => {}
                            Some(tk) => {
                                self.err.push(Diagnostic {
                                    kind: ErrKind::Type(TypeErr::InvalidType {
                                        expected: tk.kind.clone(),
                                        actual: member.init.ty.clone(),
                                    }),
                                    span: member.span.clone(),
                                    suggestions: Vec::new(),
                                });
                                member.init.ty.kind = tk.kind.clone();
                            }
                            None => {
                                self.err.push(Diagnostic {
                                    kind: ErrKind::Type(TypeErr::FieldNotFound {
                                        ty: t.kind.clone(),
                                        field: member.name.lexeme.clone(),
                                    }),
                                    span: name.span.clone(),
                                    suggestions: Vec::new(),
                                });
                            }
                        }
                    }
                } else {
                    todo!();
                }
            }
            None => {
                // TODO(Simon): Provide suggestions
                self.span_err(TypeErr::TyNotFound(name.lexeme.clone()), name.span.clone());
            }
        }
    }

    fn span_err(&mut self, kind: TypeErr, span: Span) {
        self.err.push(Diagnostic {
            kind: ErrKind::Type(kind),
            span,
            suggestions: Vec::new(),
        })
    }
}

impl Visitor for TyInferencePrePass {
    type Result = ();

    fn visit_decl(&mut self, decl: &mut Decl) -> Self::Result {
        if let Decl::Fn(f) = decl {
            self.infer_fn(f);
        }
    }
    fn visit_stmt(&mut self, stmt: &mut Stmt) -> Self::Result {
        match stmt {
            Stmt::VarDef(ref mut vardef) => {
                self.infer_expr(&mut vardef.init);
                self.cxt
                    .insert(vardef.pat.lexeme.clone(), vardef.init.ty.clone());
            }
            Stmt::Block(ref mut block) => self.infer_block(block),
            Stmt::For {
                ref mut vardef,
                ref mut body,
                ..
            } => {
                self.infer_expr(&mut vardef.init);
                if !is_type!(vardef.init.ty.kind, TyKind::Array(_)) {
                    self.span_err(
                        TypeErr::InvalidType {
                            expected: TyKind::empty_array_ty(Span::default()),
                            actual: vardef.init.ty.clone(),
                        },
                        vardef.init.span.clone(),
                    );
                }
                self.cxt.push_scope();
                self.cxt
                    .insert(vardef.pat.lexeme.clone(), vardef.init.ty.clone());
                self.infer_block(body);
                self.cxt.pop_scope();
            }
            Stmt::If {
                ref mut cond,
                ref mut body,
                ref mut else_branches,
                ref mut final_branch,
                ..
            } => {
                self.infer_expr(cond);
                if !is_type!(cond.ty.kind, TyKind::Bool) {
                    self.span_err(
                        TypeErr::InvalidType {
                            expected: TyKind::Bool,
                            actual: cond.ty.clone(),
                        },
                        cond.span.clone(),
                    );
                }
                self.infer_block(body);
                for branch in else_branches {
                    self.infer_expr(&mut branch.cond);
                    if !is_type!(cond.ty.kind, TyKind::Bool) {
                        self.span_err(
                            TypeErr::InvalidType {
                                expected: TyKind::Bool,
                                actual: cond.ty.clone(),
                            },
                            cond.span.clone(),
                        );
                    }
                    self.infer_block(&mut branch.body);
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
                self.infer_expr(cond);
                if !is_type!(cond.ty.kind, TyKind::Bool) {
                    self.span_err(
                        TypeErr::InvalidType {
                            expected: TyKind::Bool,
                            actual: cond.ty.clone(),
                        },
                        cond.span.clone(),
                    )
                }

                self.infer_block(body);
            }
            Stmt::Expr(ref mut e) => self.infer_expr(e),
            Stmt::Assign {
                ref target,
                ref mut rhs,
                ..
            } => {
                self.infer_expr(rhs);
                match self.match_assign(&target.kind) {
                    Some(t) => {
                        if t.kind != rhs.ty.kind {
                            self.span_err(
                                TypeErr::InvalidType {
                                    actual: Ty::default_unit_type(target.span.clone()),
                                    expected: rhs.ty.kind.clone(),
                                },
                                target.span.clone(),
                            );
                        }
                    }
                    None => self.span_err(
                        TypeErr::InvalidType {
                            actual: Ty::default_unit_type(target.span.clone()),
                            expected: rhs.ty.kind.clone(),
                        },
                        target.span.clone(),
                    ),
                }
            }
            Stmt::Ret(e, _) => self.infer_expr(e),
            Stmt::Break(_) | Stmt::Continue(_) => {}
        }
    }
    fn visit_expr(&mut self, expr: &mut Expr) -> Self::Result {
        match expr.node {
            ExprKind::Binary {
                ref mut lhs,
                op: _,
                ref mut rhs,
            } => {
                self.infer_expr(lhs);
                self.infer_expr(rhs);
                match (&lhs.ty.kind, &rhs.ty.kind) {
                    (TyKind::Num, TyKind::Num) => {}
                    (TyKind::Num, _) => self.span_err(
                        TypeErr::InvalidType {
                            expected: TyKind::Num,
                            actual: rhs.ty.clone(),
                        },
                        rhs.span.clone(),
                    ),
                    (_, TyKind::Num) => self.span_err(
                        TypeErr::InvalidType {
                            expected: TyKind::Num,
                            actual: lhs.ty.clone(),
                        },
                        lhs.span.clone(),
                    ),
                    _ => {
                        self.span_err(
                            TypeErr::InvalidType {
                                expected: TyKind::Num,
                                actual: rhs.ty.clone(),
                            },
                            rhs.span.clone(),
                        );
                        self.span_err(
                            TypeErr::InvalidType {
                                expected: TyKind::Num,
                                actual: lhs.ty.clone(),
                            },
                            lhs.span.clone(),
                        );
                    }
                };
                expr.ty.kind = TyKind::Num;
            }
            ExprKind::Logical {
                ref mut lhs,
                ref op,
                ref mut rhs,
            } => {
                self.infer_expr(lhs);
                self.infer_expr(rhs);
                match op {
                    CmpOp::And | CmpOp::Or => {
                        match (&lhs.ty.kind, &rhs.ty.kind) {
                            (TyKind::Bool, TyKind::Bool) => {}
                            (TyKind::Bool, _) => self.span_err(
                                TypeErr::InvalidType {
                                    expected: TyKind::Bool,
                                    actual: rhs.ty.clone(),
                                },
                                rhs.span.clone(),
                            ),
                            (_, TyKind::Bool) => self.span_err(
                                TypeErr::InvalidType {
                                    expected: TyKind::Bool,
                                    actual: lhs.ty.clone(),
                                },
                                lhs.span.clone(),
                            ),
                            _ => {
                                self.span_err(
                                    TypeErr::InvalidType {
                                        expected: TyKind::Bool,
                                        actual: rhs.ty.clone(),
                                    },
                                    rhs.span.clone(),
                                );
                                self.span_err(
                                    TypeErr::InvalidType {
                                        expected: TyKind::Bool,
                                        actual: lhs.ty.clone(),
                                    },
                                    lhs.span.clone(),
                                );
                            }
                        };
                    }
                    CmpOp::EqEq | CmpOp::NotEq => {
                        self.span_err(
                            TypeErr::InvalidType {
                                actual: lhs.ty.clone(),
                                expected: rhs.ty.kind.clone(),
                            },
                            expr.span.clone(),
                        );
                    }
                    CmpOp::Greater | CmpOp::GreaterEq | CmpOp::Less | CmpOp::LessEq => {
                        match (&lhs.ty.kind, &rhs.ty.kind) {
                            (TyKind::Num, TyKind::Num) => {}
                            (TyKind::Num, _) => self.span_err(
                                TypeErr::InvalidType {
                                    expected: TyKind::Num,
                                    actual: rhs.ty.clone(),
                                },
                                rhs.span.clone(),
                            ),
                            (_, TyKind::Num) => self.span_err(
                                TypeErr::InvalidType {
                                    expected: TyKind::Num,
                                    actual: lhs.ty.clone(),
                                },
                                lhs.span.clone(),
                            ),
                            _ => {
                                self.span_err(
                                    TypeErr::InvalidType {
                                        expected: TyKind::Num,
                                        actual: rhs.ty.clone(),
                                    },
                                    rhs.span.clone(),
                                );
                                self.span_err(
                                    TypeErr::InvalidType {
                                        expected: TyKind::Num,
                                        actual: lhs.ty.clone(),
                                    },
                                    lhs.span.clone(),
                                );
                            }
                        };
                    }
                }
                expr.ty.kind = TyKind::Bool;
            }
            ExprKind::Unary {
                ref mut rhs,
                ref op,
            } => {
                self.infer_expr(rhs);
                let ty = match op {
                    UnaryOp::Minus => TyKind::Num,
                    UnaryOp::Not => TyKind::Bool,
                };
                if rhs.ty.kind != ty {
                    self.span_err(
                        TypeErr::InvalidType {
                            expected: ty,
                            actual: rhs.ty.clone(),
                        },
                        rhs.span.clone(),
                    )
                } else {
                    expr.ty.kind = ty;
                }
            }
            ExprKind::Tup(ref mut tuple) => {
                for elem in tuple.iter_mut() {
                    self.infer_expr(elem);
                }

                expr.ty.kind = TyKind::Tup(tuple.iter().map(|elem| elem.ty.clone()).collect());

                // transform tuple into normal node if it has only 1 element
                if tuple.len() <= 1 {
                    expr.node = tuple.first().unwrap().clone().node;
                }
            }
            ExprKind::Index {
                ref mut callee,
                ref mut index,
            } => {
                self.infer_expr(callee);
                self.infer_expr(index);

                // TODO(Simon): Allow for indexing tuple types
                if !is_type!(callee.ty.kind, TyKind::Array(_)) {
                    self.span_err(
                        TypeErr::InvalidType {
                            expected: TyKind::empty_array_ty(callee.span.clone()),
                            actual: callee.ty.clone(),
                        },
                        callee.span.clone(),
                    );
                    expr.ty.kind = TyKind::Array(box Ty::default_unit_type(callee.span.clone()))
                }
                if !is_type!(index.ty.kind, TyKind::Num) {
                    self.span_err(
                        TypeErr::InvalidType {
                            expected: TyKind::empty_array_ty(callee.span.clone()),
                            actual: callee.ty.clone(),
                        },
                        callee.span.clone(),
                    );
                    index.ty.kind = TyKind::Num;
                    expr.ty.kind = TyKind::Array(box Ty::default_unit_type(callee.span.clone()))
                }
            }
            ExprKind::Struct {
                ref name,
                ref mut members,
            } => {
                members
                    .iter_mut()
                    .for_each(|member| self.infer_expr(&mut member.init));
                self.infer_struct_lit(name, members);
            }
            ExprKind::Var(ref var) | ExprKind::This(ref var) => match self.cxt.get(&var.lexeme) {
                Some(t) => expr.ty.kind = t.clone().kind,
                None => {
                    self.span_err(TypeErr::VarNotFound(var.lexeme.clone()), var.span.clone());
                    expr.ty.kind = Ty::default_unit_type(expr.span.clone()).kind;
                }
            },
            ExprKind::Array(ref mut array) => {
                for elem in array.iter_mut() {
                    self.infer_expr(elem);
                }
                let kind = match array.first().cloned() {
                    Some(e) => e.ty.kind,
                    None => Ty::default_unit_type(expr.span.clone()).kind,
                };
                for elem in array {
                    if elem.ty.kind != kind {
                        self.span_err(
                            TypeErr::InvalidType {
                                expected: kind.clone(),
                                actual: elem.ty.clone(),
                            },
                            elem.span.clone(),
                        )
                    }
                }
                expr.ty.kind = TyKind::Array(box Ty {
                    kind,
                    span: expr.span.clone(),
                });
            }
            ExprKind::Call {
                ref mut callee,
                ref mut args,
            } => {
                // TODO(Simon): check parameter names
                args.iter_mut().for_each(|arg| self.infer_expr(arg));
                self.infer_expr(callee);
                if !is_type!(callee.ty.kind, TyKind::Fn(_, _)) {
                    let arg_types = args.iter().map(|arg| arg.ty.clone()).collect();
                    self.span_err(
                        TypeErr::InvalidType {
                            expected: TyKind::Fn(
                                arg_types,
                                box Ty::default_unit_type(callee.span.clone()),
                            ),
                            actual: callee.ty.clone(),
                        },
                        callee.span.clone(),
                    )
                }
            }
            ExprKind::Intrinsic {
                ref kind,
                ref mut args,
            } => {
                args.iter_mut().for_each(|arg| self.infer_expr(arg));
                match kind {
                    Intrinsic::Read => {
                        if args.len() != 1 {
                            self.span_err(
                                TypeErr::Parity {
                                    name: "#ausgabe".to_string(),
                                    expected: 1,
                                    actual: args.len(),
                                },
                                expr.span.clone(),
                            );
                            return;
                        } else {
                            let fmter = args.first().unwrap();
                            if !is_type!(fmter.ty.kind, TyKind::Text) {
                                self.span_err(
                                    TypeErr::InvalidType {
                                        expected: TyKind::Text,
                                        actual: fmter.ty.clone(),
                                    },
                                    fmter.span.clone(),
                                )
                            }
                        }
                    }
                    Intrinsic::Print => {}
                    _ => todo!(),
                }
            }
            ExprKind::Range(ref mut lo, ref mut hi) => {
                self.infer_expr(lo);
                self.infer_expr(hi);

                match (&lo.ty.kind, &hi.ty.kind) {
                    (TyKind::Num, TyKind::Num) => {}
                    (TyKind::Num, _) => self.span_err(
                        TypeErr::InvalidType {
                            expected: TyKind::Num,
                            actual: hi.ty.clone(),
                        },
                        hi.span.clone(),
                    ),
                    (_, TyKind::Num) => self.span_err(
                        TypeErr::InvalidType {
                            expected: TyKind::Num,
                            actual: lo.ty.clone(),
                        },
                        lo.span.clone(),
                    ),
                    _ => {
                        self.span_err(
                            TypeErr::InvalidType {
                                expected: TyKind::Num,
                                actual: lo.ty.clone(),
                            },
                            lo.span.clone(),
                        );
                        self.span_err(
                            TypeErr::InvalidType {
                                expected: TyKind::Num,
                                actual: hi.ty.clone(),
                            },
                            hi.span.clone(),
                        );
                    }
                };
                // NOTE(Simon): Do we really want the compiler to force these types?
                lo.ty.kind = TyKind::Num;
                hi.ty.kind = TyKind::Num;
                expr.ty.kind = TyKind::Array(box Ty {
                    kind: TyKind::Num,
                    span: expr.span.clone(),
                })
            }
            ExprKind::Path(ref path) => {
                if path.len() != 2 {
                    panic!();
                    // self.span_err(ErrKind::Internal("Typenpfade mit mehr als 2 Segmenten werden zurzeit noch nicht unterstuezt!".to_string()), path.span.clone());
                    //return;
                }
                let ty_name = &path.first().unwrap();
                let fn_name = &path.second().unwrap();
                match self.ty_table.get(&ty_name.lexeme) {
                    Some(t) => match t.get_method(&fn_name.lexeme) {
                        Some(f) => {
                            let arg_types = f.header.params.iter().map(|p| p.ty.clone()).collect();
                            expr.ty.kind = TyKind::Fn(arg_types, f.header.ret_ty.clone());
                        }
                        None => self.span_err(
                            TypeErr::StaticFnNotFound {
                                ty_name: ty_name.lexeme.clone(),
                                fn_name: fn_name.lexeme.clone(),
                            },
                            fn_name.span.clone(),
                        ),
                    },
                    None => self.span_err(
                        TypeErr::TyNotFound(ty_name.lexeme.clone()),
                        ty_name.span.clone(),
                    ),
                }
            }
            ExprKind::Lit(ref lit) => {
                expr.ty.kind = match lit {
                    Lit::Number(_) => TyKind::Num,
                    Lit::String(_) => TyKind::Text,
                    Lit::Bool(_) => TyKind::Bool,
                }
            }
            ExprKind::Field(ref mut callee, ref name) => {
                self.infer_expr(callee);
                if let TyKind::Struct(s) = &callee.ty.kind {
                    match s.fields.get(&name) {
                        Some(t) => expr.ty.kind = t.kind.clone(),
                        None => self.span_err(
                            TypeErr::FieldNotFound {
                                ty: callee.ty.kind.clone(),
                                field: name.lexeme.clone(),
                            },
                            name.span.clone(),
                        ),
                    }
                } else {
                    self.span_err(
                        TypeErr::FieldNotFound {
                            ty: callee.ty.kind.clone(),
                            field: name.lexeme.clone(),
                        },
                        name.span.clone(),
                    );
                }
            }
        }
    }
}

pub struct TyConsGenPass {
    cxt: Cxt<String, Ty>,
    ty_table: HashMap<String, TyDecl>,
    subst: Vec<Ty>,
    cons: Vec<Constraint>,
    diagnostics: Vec<Diagnostic>,
}

impl TyConsGenPass {
    pub fn new() -> Self {
        Self {
            cons: Vec::new(),
            ty_table: HashMap::new(),
            cxt: Cxt::new(),
            subst: Vec::new(),
            diagnostics: Vec::new(),
        }
    }

    fn new_id(&mut self, span: Span) -> Ty {
        let res = Ty {
            kind: TyKind::Id(self.subst.len()),
            span,
        };
        self.subst.push(res.clone());
        res
    }

    fn unify(&mut self, lhs: &Ty, rhs: &Ty) {
        match (&lhs.kind, &rhs.kind) {
            (TyKind::Id(i), _) if self.subst(*i).kind != TyKind::Id(*i) => {
                self.unify(&self.subst(*i), rhs)
            }
            (_, TyKind::Id(i)) if self.subst(*i).kind != TyKind::Id(*i) => {
                self.unify(lhs, &self.subst(*i))
            }
            (TyKind::Id(i), _) => {
                if self.occurs_in(*i, rhs) {
                    let err = ErrKind::Type(TypeErr::InfRec(lhs.clone(), rhs.clone()));
                    // FIXME(Simon): use ty instead of tykind to report errors properly
                    self.span_err(err, lhs.span.clone());
                } else {
                    self.subst[*i] = rhs.clone();
                }
            }
            (_, TyKind::Id(i)) => {
                if self.occurs_in(*i, lhs) {
                    let err = ErrKind::Type(TypeErr::InfRec(lhs.clone(), rhs.clone()));
                    // FIXME(Simon): use ty instead of tykind to report errors properly
                    self.span_err(err, lhs.span.clone());
                } else {
                    self.subst[*i] = lhs.clone();
                }
            }
            (TyKind::Array(box lt), TyKind::Array(box rt)) => self.unify(&lt, &rt),
            (TyKind::Tup(lt), TyKind::Tup(rt)) => {
                if lt.len() != rt.len() {
                    let err = ErrKind::Type(TypeErr::GenericsMismatch(lhs.clone(), rhs.clone()));
                    self.span_err(err, lhs.span.clone());
                } else {
                    lt.iter()
                        .zip(rt.iter())
                        .for_each(|(t1, t2)| self.unify(&t1, &t2));
                }
            }
            (TyKind::Fn(lp, l_ret), TyKind::Fn(rp, r_ret)) => {
                if lp.len() != rp.len() {
                    let err = ErrKind::Type(TypeErr::GenericsMismatch(lhs.clone(), rhs.clone()));
                    self.span_err(err, lhs.span.clone());
                } else {
                    lp.iter()
                        .zip(rp.iter())
                        .for_each(|(t1, t2)| self.unify(&t1, &t2));
                }
                self.unify(&l_ret, &r_ret)
            }
            (TyKind::Bool, TyKind::Bool)
            | (TyKind::Text, TyKind::Text)
            | (TyKind::Num, TyKind::Num) => {}
            _ => {
                // TODO(Simon): is the order of actual vs expected still right?
                self.span_err(
                    ErrKind::Type(TypeErr::InvalidType {
                        expected: lhs.kind.clone(),
                        actual: rhs.clone(),
                    }),
                    rhs.span.clone(),
                );
            }
        };
    }

    fn occurs_in(&self, index: usize, tk: &Ty) -> bool {
        match tk.kind {
            TyKind::Id(i) if self.subst(i).kind != TyKind::Id(i) => {
                self.occurs_in(index, &self.subst(i))
            }
            TyKind::Id(i) => i == index,
            TyKind::Tup(ref tup) => tup.iter().any(|elem| self.occurs_in(index, &elem)),
            _ => false,
        }
    }

    fn subst(&self, i: usize) -> Ty {
        self.subst[i].clone()
    }

    fn fill_ty_table(&mut self, ast: &AST) {
        for node in ast {
            if let Decl::TyDecl(t) = node {
                self.ty_table.insert(t.name().lexeme.clone(), t.clone());
            }
        }
    }

    pub fn gen(&mut self, ast: &mut AST) -> (Vec<Ty>, Vec<Diagnostic>) {
        self.fill_ty_table(ast);

        for d in ast.iter() {
            match d {
                Decl::TyDecl(TyDecl::Struct(s)) => self.cxt.insert_global(
                    s.name.lexeme.clone(),
                    Ty {
                        kind: TyKind::Struct(s.clone()),
                        span: s.span.clone(),
                    },
                ),
                Decl::TyDecl(TyDecl::Enum(e)) => self.cxt.insert_global(
                    e.name.lexeme.clone(),
                    Ty {
                        kind: TyKind::Enum(e.clone()),
                        span: e.span.clone(),
                    },
                ),
                Decl::Fn(f) => {
                    let params = f.header.params.iter().map(|p| p.ty.clone()).collect();
                    let name = &f.header.name.lexeme;
                    self.cxt.insert_global(
                        name.clone(),
                        Ty {
                            kind: TyKind::Fn(params, f.header.ret_ty.clone()),
                            span: f.span.clone(),
                        },
                    )
                }
                _ => continue,
            }
        }

        for d in ast.iter_mut() {
            if let Decl::Fn(f) = d {
                self.infer_fn(f).unwrap();
            }
        }
        self.solve_constrains();
        (self.subst.clone(), self.diagnostics.clone())
    }

    fn solve_constrains(&mut self) {
        for con in self.cons.clone() {
            let Constraint::Eq(t1, t2) = con;
            self.unify(&t1, &t2);
        }
    }

    fn gen_ret_cons(&mut self, block: &mut Block, ret_ty: &Ty) -> Result<(), Diagnostic> {
        for stmt in &mut block.stmts {
            match stmt {
                Stmt::Ret(ref mut e, _) => {
                    e.ty = self.new_id(e.span.clone());
                    self.cons.push(Constraint::Eq(e.ty.clone(), ret_ty.clone()));
                }
                Stmt::If {
                    cond: _,
                    ref mut body,
                    ref mut else_branches,
                    ref mut final_branch,
                    span: _,
                } => {
                    self.gen_ret_cons(body, ret_ty)?;
                    for branch in else_branches {
                        self.gen_ret_cons(&mut branch.body, ret_ty)?;
                    }
                    if let Some(ref mut fb) = final_branch {
                        self.gen_ret_cons(&mut fb.body, ret_ty)?;
                    }
                }
                Stmt::While {
                    cond: _,
                    ref mut body,
                    span: _,
                } => {
                    self.gen_ret_cons(body, ret_ty)?;
                }
                Stmt::For {
                    vardef: _,
                    ref mut body,
                    span: _,
                } => {
                    self.gen_ret_cons(body, ret_ty)?;
                }
                _ => continue,
            }
        }
        Ok(())
    }

    fn infer_fn(&mut self, f: &mut FnDecl) -> Result<(), Diagnostic> {
        self.cxt.push_frame();
        self.gen_ret_cons(&mut f.body, &f.header.ret_ty)?;
        for p in f.header.params.iter_mut() {
            match p.ty.kind {
                TyKind::Poly(_) => todo!(),
                _ => {
                    p.ty.infer_internal();
                    self.cxt.insert(p.name.lexeme.clone(), p.ty.clone());
                }
            }
        }
        self.infer_block(&mut f.body)
    }

    fn infer_block(&mut self, block: &mut Block) -> Result<(), Diagnostic> {
        self.cxt.push_scope();
        for stmt in block.stmts.iter_mut() {
            stmt.accept(self)?;
        }
        self.cxt.pop_scope();
        Ok(())
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

    pub fn infer(&mut self, e: &Expr) -> Result<Ty, Diagnostic> {
        match e.node {
            ExprKind::Binary {
                ref lhs,
                op: _,
                ref rhs,
            } => {
                let lhs = self.infer(lhs)?;
                let sp = lhs.span.clone();
                self.cons.push(Constraint::Eq(
                    lhs,
                    Ty {
                        kind: TyKind::Num,
                        span: sp,
                    },
                ));
                let rhs = self.infer(rhs)?;
                let sp = rhs.span.clone();
                self.cons.push(Constraint::Eq(
                    rhs,
                    Ty {
                        kind: TyKind::Num,
                        span: sp,
                    },
                ));
                Ok(Ty {
                    kind: TyKind::Num,
                    span: e.span.clone(),
                })
            }
            ExprKind::Logical {
                ref lhs,
                ref op,
                ref rhs,
            } => {
                let lhs = self.infer(lhs)?;
                let rhs = self.infer(rhs)?;
                match op {
                    CmpOp::And | CmpOp::Or => {
                        self.cons.push(Constraint::Eq(
                            lhs.clone(),
                            Ty {
                                kind: TyKind::Bool,
                                span: lhs.span.clone(),
                            },
                        ));
                        self.cons.push(Constraint::Eq(
                            rhs.clone(),
                            Ty {
                                kind: TyKind::Bool,
                                span: rhs.span.clone(),
                            },
                        ));
                        Ok(Ty {
                            kind: TyKind::Bool,
                            span: e.span.clone(),
                        })
                    }
                    CmpOp::Greater | CmpOp::GreaterEq | CmpOp::Less | CmpOp::LessEq => {
                        self.cons.push(Constraint::Eq(
                            lhs.clone(),
                            Ty {
                                kind: TyKind::Num,
                                span: lhs.span.clone(),
                            },
                        ));
                        self.cons.push(Constraint::Eq(
                            rhs.clone(),
                            Ty {
                                kind: TyKind::Num,
                                span: lhs.span.clone(),
                            },
                        ));
                        Ok(Ty {
                            kind: TyKind::Num,
                            span: e.span.clone(),
                        })
                    }
                    CmpOp::EqEq | CmpOp::NotEq => {
                        self.cons.push(Constraint::Eq(lhs, rhs));
                        Ok(Ty {
                            kind: TyKind::Bool,
                            span: e.span.clone(),
                        })
                    }
                }
            }
            ExprKind::Unary { ref rhs, ref op } => {
                let rhs = self.infer(rhs)?;
                let tk = match op {
                    UnaryOp::Minus => TyKind::Num,
                    UnaryOp::Not => TyKind::Bool,
                };
                let res = Ty {
                    kind: tk,
                    span: e.span.clone(),
                };
                self.cons.push(Constraint::Eq(rhs, res.clone()));
                Ok(res)
            }
            ExprKind::Array(ref arr) => {
                let first_tk = match arr.first() {
                    Some(e) => self.infer(e)?,
                    None => self.new_id(e.span.clone()),
                };
                let elem_ty = Ty {
                    kind: TyKind::Array(box Ty {
                        kind: first_tk.kind.clone(),
                        span: e.span.clone(),
                    }),
                    span: first_tk.span.clone(),
                };
                for elem in arr {
                    let tk = self.infer(elem)?;
                    self.cons.push(Constraint::Eq(tk, first_tk.clone()));
                }
                Ok(elem_ty)
            }
            ExprKind::Tup(ref tup) => {
                let mut t = Vec::new();
                for elem in tup {
                    t.push(self.infer(&elem)?)
                }
                Ok(Ty {
                    kind: TyKind::Tup(t),
                    span: e.span.clone(),
                })
            }
            ExprKind::Path(ref path) => {
                if path.len() != 2 {
                    return Err(self.span_err(ErrKind::Internal("Typenpfade mit mehr als 2 Segmenten um zum Beispiel #benuzte stmts zu ersetzen sind zum aktuellen Zeitpunkt noch nicht unterstuezt!".to_string()), path.span.clone()));
                }
                let ty_name = path.first().unwrap();
                let fn_name = path.segments.get(1).unwrap();
                match self.ty_table.get(&ty_name.lexeme) {
                    Some(t) => {
                        if let Some(fun) = t.get_method(&fn_name.lexeme) {
                            if let Some(p) = fun.header.params.first() {
                                if p.name.lexeme == "selbst" {
                                    return Err(self.span_err(
                                        ErrKind::Type(TypeErr::NonStaticCall {
                                            ty_name: path.first().unwrap().lexeme.clone(),
                                            fn_name: fn_name.lexeme.clone(),
                                        }),
                                        fn_name.span.clone(),
                                    ));
                                } else {
                                    return Ok(Ty {
                                        kind: fun.into(),
                                        span: fn_name.span.clone(),
                                    });
                                }
                            }
                            Ok(Ty {
                                kind: fun.into(),
                                span: fn_name.span.clone(),
                            })
                        } else {
                            Err(self.span_err(
                                ErrKind::Type(TypeErr::StaticFnNotFound {
                                    ty_name: ty_name.lexeme.clone(),
                                    fn_name: fn_name.lexeme.clone(),
                                }),
                                fn_name.span.clone(),
                            ))
                        }
                    }
                    None => Err(self.span_err(
                        ErrKind::Type(TypeErr::TyNotFound(path.first().unwrap().lexeme.clone())),
                        path.first().unwrap().span.clone(),
                    )),
                }
            }
            ExprKind::Struct {
                ref name,
                ref members,
            } => self.infer_struct_lit(name, members),
            ExprKind::Range(ref from, ref to) => {
                let ty = Ty {
                    kind: TyKind::Num,
                    span: from.span.clone().combine(&to.span.clone()),
                };
                Ok(Ty {
                    kind: TyKind::Array(Box::new(ty)),
                    span: e.span.clone(),
                })
            }
            ExprKind::Lit(ref lit) => Ok(Ty {
                kind: Self::infer_lit(lit),
                span: e.span.clone(),
            }),
            ExprKind::Index {
                ref callee,
                ref index,
            } => {
                let index = self.infer(index)?;
                let span = index.span.clone();
                let callee_ty = self.infer(callee)?;
                self.cons.push(Constraint::Eq(
                    index,
                    Ty {
                        kind: TyKind::Num,
                        span,
                    },
                ));
                let arr = Ty {
                    kind: TyKind::Array(box self.new_id(e.span.clone())),
                    span: e.span.clone(),
                };
                self.cons.push(Constraint::Eq(callee_ty, arr.clone()));
                Ok(arr)
            }
            ExprKind::Var(ref var) | ExprKind::This(ref var) => match self.cxt.get(&var.lexeme) {
                Some(t) => Ok(t.clone()),
                None => Err(Diagnostic {
                    kind: ErrKind::Type(TypeErr::VarNotFound(var.lexeme.clone())),
                    span: var.span.clone(),
                    suggestions: Vec::new(),
                }),
            },
            ExprKind::Call {
                ref callee,
                ref args,
            } => {
                let callee_ty = self.infer(callee)?;
                let mut args_buf = Vec::new();
                for arg in args.iter() {
                    args_buf.push(self.infer(arg)?);
                }
                let id = self.new_id(e.span.clone());
                let f_ty = Ty {
                    kind: TyKind::Fn(args_buf, box id.clone()),
                    span: e.span.clone(),
                };
                self.cons.push(Constraint::Eq(f_ty, callee_ty));
                Ok(id)
            }
            // TODO(Simon): Type constrains for intrinsic functions
            ExprKind::Intrinsic { ref kind, args: _ } => match kind {
                Intrinsic::Format | Intrinsic::Read => Ok(Ty {
                    kind: TyKind::Text,
                    span: e.span.clone(),
                }),
                Intrinsic::Print | Intrinsic::Write => Ok(Ty::default_unit_type(e.span.clone())),
            },
            ExprKind::Field(ref callee, ref field) => {
                todo!();
            }
        }
    }

    fn infer_lit(lit: &Lit) -> TyKind {
        match lit {
            Lit::Number(_) => TyKind::Num,
            Lit::String(_) => TyKind::Text,
            Lit::Bool(_) => TyKind::Bool,
        }
    }

    fn infer_struct_lit(&mut self, name: &Ident, members: &Vec<Member>) -> Result<Ty, Diagnostic> {
        let str_name = name.lexeme.clone();

        match self.cxt.get(&str_name).cloned() {
            Some(s) => {
                if let TyKind::Struct(s) = s.kind {
                    // FIXME(Simon): this fails to detect if the user had more than 1 duplicate struct literal field!!!
                    Self::check_duplicates_field(&members)?;
                    self.check_forgotten_fields(&s, &members);

                    for member in members {
                        let member_ty = self.infer(&member.init)?;
                        if let Some(ty) = s.fields.get(&member.name) {
                            self.cons
                                .push(Constraint::Eq(ty.clone(), member_ty.clone()))
                        }
                    }
                    Ok(Ty {
                        kind: TyKind::Struct(s),
                        span: name.span.clone(),
                    })
                } else {
                    let err = ErrKind::Type(TypeErr::TyNotFound(str_name));
                    // TODO(Simon): provide suggestions which type might be meant
                    Err(self.span_err(err, name.span.clone()))
                }
            }

            _ => {
                let err = ErrKind::Type(TypeErr::TyNotFound(str_name));
                // TODO(Simon): provide suggestions which type might be meant
                Err(self.span_err(err, name.span.clone()))
            }
        }
    }

    // FIXME(Simon): Refactor to log errors directly!!
    fn check_duplicates_field(members: &Vec<Member>) -> Result<(), Diagnostic> {
        let mut fields = HashSet::new();
        for member in members {
            if !fields.insert(&member.name.lexeme) {
                return Err(Diagnostic {
                    kind: ErrKind::Type(TypeErr::DuplicateLitField(member.name.lexeme.clone())),
                    span: member.span.clone(),
                    suggestions: vec![
                        "Versuche das doppelte Feld in dem Strukturliteral zu entfernen!"
                            .to_string(),
                    ],
                });
            }
        }
        Ok(())
    }

    fn check_forgotten_fields(&mut self, s: &Struct, members: &Vec<Member>) {
        let mut s = s.clone();
        for member in members {
            let field = &member.name;
            match s.fields.remove(field) {
                None => {
                    self.span_err(
                        ErrKind::Type(TypeErr::InvalidField(
                            s.name.lexeme.clone(),
                            field.lexeme.clone(),
                        )),
                        member.span.clone(),
                    );
                }
                Some(_) => continue,
            }
        }

        for (name, _) in s.fields {
            let err = ErrKind::Type(TypeErr::MissingField(name.lexeme.clone()));
            self.span_err(err, name.span.clone());
        }
    }

    fn infer_struct(s: &mut Struct) {
        for (_, ty) in &mut s.fields {
            ty.infer_internal();
        }
    }
    fn infer_enum(e: &mut Enum) {
        for variant in &mut e.variants {
            if let VariantData::Val(ref mut tup) = variant.data {
                for elem in tup {
                    elem.infer_internal();
                }
            }
        }
    }

    fn link_cons(&mut self, e: &Expr) {
        let tk = self.infer(&e).unwrap();
        let id = self.new_id(e.span.clone());
        self.cons.push(Constraint::Eq(tk, id));
    }

    fn infer_expr(&mut self, e: &mut Expr) {
        e.accept(self);
    }
}

impl Visitor for TyConsGenPass {
    type Result = Result<(), Diagnostic>;
    fn visit_decl(&mut self, _decl: &mut Decl) -> Self::Result {
        // match decl {
        //     Decl::Fn(f) => self.infer_fn(f)?,
        //     Decl::TyDecl(TyDecl::Struct(s)) => Self::infer_struct(s),
        //     Decl::TyDecl(TyDecl::Enum(e)) => Self::infer_enum(e),
        //     _ => {}
        // };
        Ok(())
    }
    fn visit_stmt(&mut self, stmt: &mut Stmt) -> Self::Result {
        match stmt {
            Stmt::VarDef(ref mut vd) => {
                let tk = match vd.ty.kind {
                    TyKind::Infer => self.new_id(vd.pat.span.clone()),
                    _ => {
                        vd.ty.infer_internal();
                        vd.ty.clone()
                    }
                };
                vd.ty = tk.clone();
                self.cxt.insert(vd.pat.lexeme.clone(), tk.clone());
                let init_ty = self.infer_expr(&mut vd.init);
                self.cons
                    .push(Constraint::Eq(vd.init.ty.clone(), tk.clone()))
            }
            Stmt::Assign {
                ref mut target,
                ref mut rhs,
                span: _,
            } => {
                //self.infer_expr(lhs); // TODO
                self.infer_expr(rhs);
                // self.cons
                //     .push(Constraint::Eq(lhs.ty.kind.clone(), rhs.ty.kind.clone()));
            }
            Stmt::Block(ref mut block) => self.infer_block(block)?,
            Stmt::Expr(ref mut e) => self.infer_expr(e),
            Stmt::For {
                ref mut vardef,
                ref mut body,
                span: _,
            } => {
                // TODO(Simon): force array type
                self.cxt.push_scope();
                let loop_var = vardef.pat.lexeme.clone();
                self.infer_expr(&mut vardef.init);
                self.cxt
                    .insert(vardef.pat.lexeme.clone(), vardef.init.ty.clone());
                self.infer_block(body)?;
                self.cxt.pop_scope();
            }
            Stmt::While {
                ref mut cond,
                ref mut body,
                span: _,
            } => {
                self.infer_expr(cond);
                self.cons.push(Constraint::Eq(
                    Ty {
                        kind: TyKind::Bool,
                        span: cond.span.clone(),
                    },
                    cond.ty.clone(),
                ));
                self.infer_block(body)?;
            }
            Stmt::If {
                ref mut cond,
                ref mut body,
                ref mut else_branches,
                ref mut final_branch,
                span: _,
            } => {
                self.infer_expr(cond);
                self.cons.push(Constraint::Eq(
                    cond.ty.clone(),
                    Ty {
                        kind: TyKind::Bool,
                        span: cond.span.clone(),
                    },
                ));
                self.infer_block(body)?;

                for branch in else_branches.iter_mut() {
                    self.infer_expr(&mut branch.cond);
                    self.cons.push(Constraint::Eq(
                        branch.cond.ty.clone(),
                        Ty {
                            kind: TyKind::Bool,
                            span: branch.cond.span.clone(),
                        },
                    ));
                    self.infer_block(&mut branch.body)?;
                }
                if let Some(fb) = final_branch {
                    self.infer_block(&mut fb.body)?;
                }
            }
            Stmt::Ret(..) | Stmt::Break(..) | Stmt::Continue(..) => {}
        };
        Ok(())
    }

    fn visit_expr(&mut self, expr: &mut Expr) -> Self::Result {
        match expr.node {
            ExprKind::Binary {
                ref mut lhs,
                op: _,
                ref mut rhs,
            } => {
                self.infer_expr(lhs);
                self.infer_expr(rhs);
            }
            ExprKind::Logical {
                ref mut lhs,
                op: _,
                ref mut rhs,
            } => {
                self.infer_expr(lhs);
                self.infer_expr(rhs);
            }
            ExprKind::Unary { ref mut rhs, .. } => {
                self.infer_expr(rhs);
            }
            ExprKind::Index {
                ref mut callee,
                ref mut index,
            } => {
                self.infer_expr(callee);
                self.infer_expr(index);
            }
            ExprKind::Array(ref mut elems) => {
                for mut elem in elems {
                    self.infer_expr(&mut elem);
                }
            }
            ExprKind::Range(ref mut lo, ref mut hi) => {
                self.infer_expr(lo);
                self.infer_expr(hi);
            }
            ExprKind::Tup(ref mut elems) => {
                for elem in elems {
                    self.infer_expr(elem);
                }
            }
            ExprKind::Field(ref mut callee, _) => self.infer_expr(callee),
            ExprKind::Call {
                ref mut callee,
                ref mut args,
            } => {
                let callee = self.infer_expr(callee);
                args.iter_mut().for_each(|elem| self.infer_expr(elem));
            }
            ExprKind::Intrinsic {
                kind: _,
                ref mut args,
            } => args.iter_mut().for_each(|elem| self.infer_expr(elem)),
            ExprKind::Struct {
                name: _,
                ref mut members,
            } => {
                for member in members {
                    self.infer_expr(&mut member.init);
                }
            }
            ExprKind::Path(_) | ExprKind::Lit(_) | ExprKind::This(_) | ExprKind::Var(_) => {}
        }

        let tk = self.infer(&expr)?;
        let id = self.new_id(expr.span.clone());
        expr.ty = id.clone();
        self.cons.push(Constraint::Eq(tk, id));
        Ok(())
    }
}

struct TypeSubstitutor {
    substitutions: Vec<Ty>,
}

impl TypeSubstitutor {
    pub fn new(substitutions: Vec<Ty>) -> Self {
        Self { substitutions }
    }

    pub fn apply_subst(&mut self, ast: &mut AST) {
        for decl in ast {
            decl.accept(self);
        }
    }

    pub fn subst(&self, t: &Ty) -> Ty {
        match t.kind {
            TyKind::Id(i) if self.substitutions[i].kind != TyKind::Id(i) => {
                self.subst(&self.substitutions[i].clone())
            }
            TyKind::Tup(ref tup) => {
                let mut subst_tup = Vec::new();
                for elem in tup {
                    subst_tup.push(self.subst(&elem));
                }
                Ty {
                    kind: TyKind::Tup(subst_tup),
                    span: t.span.clone(),
                }
            }
            TyKind::Array(ref elem) => Ty {
                kind: TyKind::Array(box self.subst(elem)),
                span: t.span.clone(),
            },
            _ => t.clone(),
        }
    }

    fn subst_fn(&mut self, f: &mut FnDecl) {
        for param in f.header.params.iter_mut() {
            param.ty = self.subst(&param.ty);
        }
        self.subst_block(&mut f.body);
    }

    fn subst_expr(&mut self, e: &mut Expr) {
        e.accept(self);
    }

    fn subst_block(&mut self, b: &mut Block) {
        for stmt in &mut b.stmts {
            stmt.accept(self);
        }
    }
}

impl Visitor for TypeSubstitutor {
    type Result = ();

    fn visit_decl(&mut self, decl: &mut Decl) -> Self::Result {
        if let Decl::Fn(f) = decl {
            self.subst_fn(f);
        }
    }

    fn visit_stmt(&mut self, stmt: &mut Stmt) -> Self::Result {
        match stmt {
            Stmt::While {
                ref mut cond,
                ref mut body,
                ..
            } => {
                self.subst_expr(cond);
                self.subst_block(body);
            }
            Stmt::VarDef(ref mut vd) => {
                self.subst_expr(&mut vd.init);
                vd.ty = self.subst(&vd.ty);
            }
            Stmt::Expr(ref mut e) => {
                self.subst_expr(e);
            }
            Stmt::For {
                ref mut vardef,
                ref mut body,
                ..
            } => {
                vardef.ty = self.subst(&vardef.ty);
                self.subst_block(body);
                self.subst_expr(&mut vardef.init);
            }
            Stmt::If {
                ref mut cond,
                ref mut body,
                ref mut else_branches,
                ref mut final_branch,
                ..
            } => {
                self.subst_expr(cond);
                self.subst_block(body);

                for branch in else_branches {
                    self.subst_expr(&mut branch.cond);
                    self.subst_block(&mut branch.body);
                }

                if let Some(fb) = final_branch {
                    self.subst_block(&mut fb.body);
                }
            }
            Stmt::Assign {
                ref mut target,
                ref mut rhs,
                ..
            } => {
                //self.subst_expr(lhs);
                self.subst_expr(rhs);
            }
            Stmt::Ret(ref mut val, _) => {
                self.subst_expr(val);
            }
            Stmt::Break(_) | Stmt::Continue(_) => {}
            Stmt::Block(ref mut block) => self.subst_block(block),
        }
    }
    fn visit_expr(&mut self, expr: &mut Expr) -> Self::Result {
        match expr.node {
            ExprKind::Binary {
                ref mut lhs,
                op: _,
                ref mut rhs,
            } => {
                self.subst_expr(lhs);
                self.subst_expr(rhs);
            }
            ExprKind::Logical {
                ref mut lhs,
                op: _,
                ref mut rhs,
            } => {
                self.subst_expr(lhs);
                self.subst_expr(rhs);
            }
            ExprKind::Unary { ref mut rhs, .. } => {
                self.subst_expr(rhs);
            }
            ExprKind::Index {
                ref mut callee,
                ref mut index,
            } => {
                self.subst_expr(callee);
                self.subst_expr(index);
            }
            ExprKind::Array(ref mut elems) => {
                for mut elem in elems {
                    self.subst_expr(&mut elem);
                }
            }
            ExprKind::Range(ref mut lo, ref mut hi) => {
                self.subst_expr(lo);
                self.subst_expr(hi);
            }
            ExprKind::Tup(ref mut elems) => {
                for elem in elems {
                    self.subst_expr(elem);
                }
            }
            ExprKind::Field(ref mut callee, _) => self.subst_expr(callee),
            ExprKind::Call {
                ref mut callee,
                ref mut args,
            } => {
                self.subst_expr(callee);
                args.iter_mut().for_each(|elem| self.subst_expr(elem));
            }
            ExprKind::Intrinsic {
                kind: _,
                ref mut args,
            } => args.iter_mut().for_each(|elem| self.subst_expr(elem)),
            ExprKind::Struct {
                name: _,
                ref mut members,
            } => members
                .iter_mut()
                .for_each(|member| self.subst_expr(&mut member.init)),
            ExprKind::Path(_) | ExprKind::Lit(_) | ExprKind::This(_) | ExprKind::Var(_) => {}
        }
        expr.ty = self.subst(&expr.ty);
    }
}
