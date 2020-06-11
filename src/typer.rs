use crate::cxt::Cxt;
use std::collections::*;
use std::convert::TryFrom;
use std::fmt;

use crate::errors::*;
use crate::lexer::*;

use derivative::*;
use itertools::Itertools;
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

    Fn(FnDecl),

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
            TyKind::Infer => "Infer".to_string(),
            TyKind::Poly(elem) => format!("${}$", elem.lexeme),
            TyKind::Num => "Zahl".to_string(),
            TyKind::Bool => "Bool".to_string(),
            TyKind::Path(p) => format!("{}", p),
            TyKind::Text => "Text".to_string(),
            TyKind::Fn(f) => format!("fun: {}", f.header),
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
        for d in ast.iter() {
            if let Decl::TyDecl(t) = d {
                match t {
                    TyDecl::Struct(s) => self
                        .cxt
                        .insert_global(s.name.lexeme.clone(), TyKind::Struct(s.clone())),
                    TyDecl::Enum(e) => self
                        .cxt
                        .insert_global(e.name.lexeme.clone(), TyKind::Enum(e.clone())),
                }
            }
        }

        for d in ast.iter_mut() {
            if let Decl::Fn(f) = d {
                self.infer_fn(f);
            }
        }
        dbg!(&self.cons);
        dbg!(&self.diagnostics);
    }

    fn infer_fn(&mut self, f: &mut FnDecl) -> Result<(), Diagnostic> {
        self.cxt.make_clean();
        for p in f.header.params.iter() {
            match p.ty.kind {
                TyKind::Poly(_) => todo!(),
                _ => self.cxt.insert(p.name.lexeme.clone(), p.ty.kind.clone()),
            }
        }
        self.infer_block(&mut f.body)
    }

    fn infer_block(&mut self, block: &mut Block) -> Result<(), Diagnostic> {
        self.cxt.make();
        for stmt in block.stmts.iter_mut() {
            stmt.accept(self)?;
        }
        self.cxt.drop();
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
                let first_tk = match arr.first() {
                    Some(e) => self.infer(e)?,
                    None => self.new_id(),
                };
                let elem_ty = TyKind::Array(box Ty {
                    kind: first_tk.clone(),
                    span: e.span,
                });
                for elem in arr {
                    let tk = self.infer(elem)?;
                    self.cons.push(Constraint::Eq(tk, first_tk.clone()));
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
            } => self.infer_struct_lit(name, members),
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
            } => {
                let index = self.infer(index)?;
                let callee_ty = self.infer(callee)?;
                self.cons.push(Constraint::Eq(index, TyKind::Num));
                // let arr = TyKind::Array(box Ty {
                //     kind: TyKind::Infer,
                //     span: callee.span,
                // });
                //self.cons.push(Constraint::Eq(callee_ty, arr.clone()));
                //Ok(arr)
                Ok(TyKind::Num)
            }
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

    fn infer_struct_lit(
        &mut self,
        name: &Ident,
        members: &Vec<Member>,
    ) -> Result<TyKind, Diagnostic> {
        let str_name = name.lexeme.clone();

        match self.cxt.get(&str_name) {
            Some(TyKind::Struct(s)) => {
                // FIXME(Simon): this fails to detect if the user had more than 1 duplicate struct literal field!!!
                Self::check_duplicates_field(&members)?;
                self.check_forgotten_fields(&s, &members);

                let member_table = s
                    .fields
                    .iter()
                    .map(|field| (&field.name.lexeme, field.ty.kind.clone()))
                    .collect::<HashMap<_, _>>();

                for member in members {
                    let member_ty = self.infer(&member.init)?;
                    match member_table.get(&member.name.lexeme) {
                        Some(ty) => self
                            .cons
                            .push(Constraint::Eq(ty.clone(), member_ty.clone())),
                        None => continue,
                    }
                }
                Ok(TyKind::Struct(s.clone()))
            }

            _ => {
                let err = ErrKind::Type(TypeErr::TyNotFound(str_name));
                // TODO(Simon): provide suggestions which type might be meant
                Err(self.span_err(err, name.span))
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
                    span: member.span,
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
        let mut member_table = s
            .fields
            .iter()
            .map(|field| (&field.name.lexeme, field.span))
            .collect::<HashMap<_, _>>();

        for member in members {
            let field = &member.name.lexeme;
            match member_table.remove(field) {
                None => {
                    self.span_err(
                        ErrKind::Type(TypeErr::InvalidField(s.name.lexeme.clone(), field.clone())),
                        member.span,
                    );
                }
                Some(_) => continue,
            }
        }

        for (name, span) in member_table {
            let err = ErrKind::Type(TypeErr::MissingField(name.clone()));
            self.span_err(err, span);
        }
    }
}

impl Visitor for Typer {
    type Result = Result<(), Diagnostic>;
    fn visit_decl(&mut self, decl: &mut Decl) -> Self::Result {
        match decl {
            Decl::Fn(f) => self.infer_fn(f)?,
            _ => {}
        };
        Ok(())
    }
    fn visit_stmt(&mut self, stmt: &mut Stmt) -> Self::Result {
        match stmt {
            Stmt::VarDef(ref mut vd) => {
                let tk = match vd.ty.kind {
                    TyKind::Infer => self.new_id(),
                    _ => vd.ty.kind.clone(),
                };
                vd.ty.kind = tk.clone();
                self.cxt.insert(vd.pat.lexeme.clone(), tk.clone());
                let init_ty = self.infer(&vd.init).unwrap();
                self.cons.push(Constraint::Eq(init_ty, tk.clone()))
            }
            Stmt::Assign {
                ref lhs,
                ref rhs,
                span: _,
            } => {
                let lhs = self.infer(lhs).unwrap();
                let rhs = self.infer(rhs).unwrap();
                self.cons.push(Constraint::Eq(lhs, rhs))
            }
            Stmt::Block(ref mut block) => self.infer_block(block)?,
            Stmt::Expr(ref e) => {
                self.infer(e)?;
            }
            Stmt::For {
                ref vardef,
                ref body,
                span: _,
            } => {
                // TODO(Simon): force array type
                self.cxt.make();
                let loop_var = vardef.pat.lexeme.clone();
                let init_tk = self.infer(&vardef.init)?;
                self.cxt.insert(vardef.pat.lexeme.clone(), init_tk);
                self.cxt.drop();
            }
            Stmt::While {
                ref cond,
                ref mut body,
                span: _,
            } => {
                let cond_ty = self.infer(cond)?;
                self.cons.push(Constraint::Eq(TyKind::Bool, cond_ty));
                self.infer_block(body)?;
            }
            Stmt::If {
                ref cond,
                ref mut body,
                ref mut else_branches,
                ref mut final_branch,
                span: _,
            } => {
                let cond = self.infer(cond)?;
                self.cons.push(Constraint::Eq(cond, TyKind::Bool));
                self.infer_block(body)?;

                for branch in else_branches.iter_mut() {
                    let cond = self.infer(&branch.cond)?;
                    self.cons.push(Constraint::Eq(cond, TyKind::Bool));
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
        self.infer(&expr)?;
        Ok(())
    }
}
