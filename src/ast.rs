use super::lexer::*;
use crate::errors::*;
use std::convert::TryFrom;

pub trait ASTNode {
    fn accept<V: Visitor>(&mut self, visitor: &mut V) -> V::Result;
}

pub trait Visitor {
    type Result;

    fn visit_stmt(&mut self, stmt: &mut Stmt) -> Self::Result;
    fn visit_expr(&mut self, expr: &mut Expr) -> Self::Result;
}

#[derive(PartialEq, Debug, Clone)]
pub enum ExprKind {
    /// normal binary expression, only used for numeric expressions
    /// example: a      +     42
    ///          ^-rhs  ^-op  ^-lhs
    Binary {
        lhs: Box<Expr>,
        rhs: Box<Expr>,
        op: BinaryOp,
    },

    /// just like a normal binary expression but only used for logical expressions
    /// example: a      &&    b
    ///          ^-rhs  ^-op  ^-lhs
    Logical {
        lhs: Box<Expr>,
        rhs: Box<Expr>,
        op: CmpOp,
    },

    /// one sided expression
    /// example: -    3
    ///          ^-op ^-rhs
    Unary { rhs: Box<Expr>, op: UnaryOp },

    /// struct literals are used to initialize objects with values
    /// example: Person {name: "Torben"}
    ///          ^-pat  ^^^^^^^^^^^^^^- member with name and init expr
    Struct { path: Path, members: Vec<Member> },

    /// a tuple expression is just a collection of other expressions
    /// example: (20,    20)
    ///           ^-expr ^-expr
    Tup(Vec<Expr>),
    /// variable reference, possibly containing `::` to refer to types in other moduels
    /// example: foo::bar
    ///          ^^^-segment
    Path(Path),

    /// used to represent all sorts of index expressions
    /// example: foo[     expr     ]
    ///          ^-callee ^index
    Index { callee: Box<Expr>, index: Box<Expr> },

    /// assignment expressions can be used to change the value of an already define variable
    /// NOTE: it's type is fixed and must be equal on both sides of the expression
    /// example: a.b    = 20
    ///          ^-callee ^value
    Assign { target: Box<Expr>, value: Box<Expr> },

    /// array literals are used to initialize arrays with values
    /// example: [1, 2, 3, 4, 5]
    ///           ^-create new array with values from 1 to including 5
    Array(Vec<Expr>),

    /// a range pattern
    /// example: 0   ..   10
    ///           ^-start ^-end
    Range(Box<Expr>, Box<Expr>),

    /// a raw literal is the smallest possible expression
    /// example: 42
    ///          ^-num literal
    /// example: "foo"
    ///          ^-string/text literal
    Lit(Lit, Span),

    /// access of a named struct field like a.b
    /// example: a  .    b
    ///          ^-callee ^ field
    Field(Box<Expr>, Ident),

    /// refers to a object instance and can be used to refer to that instance and it's member fields e.g. (selbst.foo)
    /// if a function contains self as an argument in it's signature it automatically becomes an associated 'Method' with that datatype
    /// NOTE: there are a few restrictions while using self in a function
    /// 1. self can only be used inside impl blocks
    /// 2. if a function contains self in it's signature self has to be the first parameter
    /// 3. the self parameter does not need to have any addition type information
    /// example: selbst    .     foo
    ///          ^-instance ptr  ^-member field
    This,

    /// function call e.g. foo(-42, 1, 1)
    /// example: foo    (-42,     10)
    ///          ^-callee ^-arg0  ^-arg1
    Call { callee: Box<Expr>, args: Vec<Expr> },
}

#[derive(Debug, PartialEq, Clone)]
pub struct Member {
    pub name: Ident,
    pub init: Expr,
    pub span: Span,
}

impl Member {
    pub fn new(name: Ident, expr: Expr, span: Span) -> Self {
        Self {
            name,
            init: expr,
            span,
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum Stmt {
    Expr(Expr),

    VarDef {
        pat: Ident, // TODO(Simon): this should really be a pattern to allow for destructoring
        init: Expr,
        ty: Ty,
        span: Span,
    },

    Block(Block),

    If {
        cond: Expr,
        body: Block,
        else_branches: Vec<ElseBranch>,
        final_branch: Option<FinalBranch>,
        span: Span,
    },

    While {
        cond: Expr,
        body: Block,
        span: Span,
    },

    For {
        it: Expr,
        var: Ident,
        body: Block,
        span: Span,
    },

    Break(Span),

    Continue(Span),

    Ret(Expr, Span),

    FnDecl(FnDecl),
    StructDecl(StructDecl),
    ImplBlock {
        target: Path,
        fn_decls: Vec<FnDecl>,
        span: Span,
    },
    EnumDecl {
        name: Ident,
        variants: Vec<Variant>,
        span: Span,
    },
}

#[derive(Debug, PartialEq)]
pub struct ElseBranch {
    pub cond: Expr,
    pub body: Block,
    pub span: Span,
}

#[derive(Debug, PartialEq)]
pub struct FinalBranch {
    pub body: Block,
    pub span: Span,
}

impl ASTNode for Stmt {
    fn accept<V: Visitor>(&mut self, visitor: &mut V) -> V::Result {
        visitor.visit_stmt(self)
    }
}

#[derive(Debug, PartialEq)]
pub struct EnumDecl {
    pub ident: Ident,
    pub variants: Vec<Variant>,
    pub span: Span,
}

#[derive(Debug, PartialEq)]
pub struct Variant {
    pub span: Span,
    pub ident: Ident,
    pub data: VariantData,
}

#[derive(Debug, PartialEq)]
pub enum VariantData {
    Val(Vec<Ty>),
    Unit,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Path {
    pub segments: Vec<Ident>,
    pub span: Span,
}

impl Path {
    pub fn new(segments: Vec<Ident>, span: Span) -> Self {
        Path { segments, span }
    }

    pub fn len(&self) -> usize {
        self.segments.len()
    }
}

#[derive(Debug, PartialEq)]
pub struct Param {
    pub name: Ident,
    pub ty: Ty,
    pub span: Span,
}

impl Param {
    pub fn new(name: Ident, ty: Ty, span: Span) -> Self {
        Self { name, ty, span }
    }
}

#[derive(Debug, PartialEq)]
pub struct StructDecl {
    pub name: Ident,
    pub fields: Vec<Field>,
    pub span: Span,
}

#[derive(Debug, PartialEq)]
pub struct Field {
    pub name: Ident,
    pub ty: Ty,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Ident {
    pub name: String,
    pub span: Span,
}

impl TryFrom<Token> for Ident {
    // TODO(Simon): this does not seem right, we should clean this up to use some internal error type for fatal compiler errors
    type Error = Diagnostic;
    fn try_from(t: Token) -> Result<Ident, Self::Error> {
        match t.kind {
            TokenKind::Ident(name) => Ok(Ident::new(name.to_owned(), t.span)),
            _ => Err(Diagnostic::new(
                "Interner Fehler",
                format!("Invalide Umwandlung von `{:#?}` zu `Ident`", t).as_str(),
                Vec::new(),
                Severity::CodeRed,
                t.span,
            )),
        }
    }
}

impl Ident {
    pub fn new(name: String, span: Span) -> Self {
        Ident { name, span }
    }
}

impl Field {
    pub fn new(name: Ident, ty: Ty, span: Span) -> Self {
        Field { name, ty, span }
    }
}

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

#[derive(Debug, PartialEq)]
pub struct FnSig {
    pub name: Ident,
    pub params: Vec<Param>,
    pub ret_ty: Ty,
}

impl FnSig {
    pub fn new(name: Ident, params: Vec<Param>, ret_ty: Ty) -> Self {
        FnSig {
            name,
            params,
            ret_ty,
        }
    }
}

#[derive(Debug, PartialEq)]
pub struct FnDecl {
    pub head: FnSig,
    pub body: Block,
}

impl FnDecl {
    pub fn new(head: FnSig, body: Block) -> Self {
        FnDecl { head, body }
    }
}

#[derive(Debug, PartialEq)]
pub struct Block {
    pub stmts: Vec<Stmt>,
    pub span: Span,
}

impl Block {
    pub fn new(stmts: Vec<Stmt>, span: Span) -> Self {
        Block { stmts, span }
    }
}

impl Default for ExprKind {
    fn default() -> Self {
        ExprKind::Tup(Vec::new())
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct Expr {
    pub node: ExprKind,
    pub ty: Ty,
    pub span: Span,
}

impl ASTNode for Expr {
    fn accept<V: Visitor>(&mut self, visitor: &mut V) -> V::Result {
        visitor.visit_expr(self)
    }
}

impl Expr {
    pub fn new(node: ExprKind, span: Span) -> Self {
        Self {
            node,
            span,
            ty: Ty::default_infer_type(span.clone()),
        }
    }

    pub fn empty(span: Span) -> Self {
        Self {
            node: ExprKind::Tup(Vec::new()),
            span,
            ty: Ty::default_infer_type(span.clone()),
        }
    }
}

#[derive(Debug, PartialEq, Clone, Copy)]
pub enum BinaryOp {
    Plus,
    Minus,
    Multiply,
    Divide,
}

impl TryFrom<Token> for BinaryOp {
    type Error = Diagnostic;

    fn try_from(t: Token) -> Result<Self, Self::Error> {
        match t.kind {
            TokenKind::Operator(Operator::Plus) => Ok(Self::Plus),
            TokenKind::Operator(Operator::Minus) => Ok(Self::Minus),
            TokenKind::Operator(Operator::Star) => Ok(Self::Multiply),
            TokenKind::Operator(Operator::Slash) => Ok(Self::Divide),
            _ => Err(Diagnostic::new(
                "Interner Fehler",
                format!("Invalide Umwandlung von `{:#?} zu BinaryOp`", t).as_str(),
                Vec::new(),
                Severity::CodeRed,
                t.span,
            )),
        }
    }
}

#[derive(Debug, PartialEq, Clone, Copy)]
pub enum CmpOp {
    EqEq,
    NotEq,
    Greater,
    GreaterEq,
    Less,
    LessEq,
}

impl TryFrom<Token> for CmpOp {
    type Error = Diagnostic;

    fn try_from(value: Token) -> Result<Self, Self::Error> {
        match value.kind {
            TokenKind::Operator(Operator::EqEq) => Ok(CmpOp::EqEq),
            TokenKind::Operator(Operator::NotEq) => Ok(CmpOp::NotEq),
            TokenKind::Operator(Operator::Greater) => Ok(CmpOp::Greater),
            TokenKind::Operator(Operator::GreaterEq) => Ok(CmpOp::GreaterEq),
            TokenKind::Operator(Operator::Less) => Ok(CmpOp::Less),
            TokenKind::Operator(Operator::LessEq) => Ok(CmpOp::LessEq),
            _ => Err(Diagnostic::new(
                "Interner Fehler",
                format!("Invalide Umwandlung von `{:#?}` zu CmpOp", value).as_str(),
                Vec::new(),
                Severity::CodeRed,
                value.span,
            )),
        }
    }
}

// NOTE(Simon): I don't know how the parser is going to handle +10 with the current grammar rules
// NOTE(Simon): maybe we need to include plus
#[derive(Debug, PartialEq, Clone, Copy)]
pub enum UnaryOp {
    Minus,
    Not,
}

impl TryFrom<Token> for UnaryOp {
    type Error = Diagnostic;

    fn try_from(t: Token) -> Result<Self, Self::Error> {
        match t.kind {
            TokenKind::Operator(Operator::Not) => Ok(UnaryOp::Not),
            TokenKind::Operator(Operator::Minus) => Ok(UnaryOp::Minus),
            _ => Err(Diagnostic::new(
                "Interner Fehler",
                format!("Invalide Umwandlung von `{:#?}` zu UnaryOp", t).as_str(),
                Vec::new(),
                Severity::CodeRed,
                t.span,
            )),
        }
    }
}

#[derive(Debug, PartialEq)]
pub struct Call {
    pub callee: Box<Expr>,
    pub args: Vec<Expr>,
}

#[derive(Debug, Copy, Clone)]
pub struct Span {
    pub lo: usize,
    pub hi: usize,
}

impl PartialEq for Span {
    // NOTE(Simon): this seems a bit sketchy to me but we are doing it for now to use partialEq while unit testing the parser.
    // NOTE(Simon): This makes it extemly easy because we can just use assert_eq.
    // NOTE(Simon): We might have to find a better solution or just annotate the expected ast with the right spans.
    fn eq(&self, _: &Self) -> bool {
        true
    }
}

impl Default for Span {
    fn default() -> Self {
        Self { lo: 0, hi: 0 }
    }
}

impl Span {
    pub fn new(lo: usize, hi: usize) -> Self {
        Span { lo, hi }
    }

    pub fn combine(&self, rhs: &Span) -> Self {
        Span {
            lo: std::cmp::min(self.lo.clone(), rhs.lo.clone()),
            hi: std::cmp::max(self.hi.clone(), rhs.hi.clone()),
        }
    }
}

#[macro_use]
#[cfg(test)]
pub mod dsl {
    use super::*;

    macro_rules! ident {
        ($name:ident) => {
            Ident::new(stringify!($name).to_string(), Span::default())
        };
    }

    pub fn fn_decl(name: Ident, params: Vec<Param>, ret_ty: Ty, body: Block) -> FnDecl {
        FnDecl {
            head: FnSig {
                name,
                params,
                ret_ty,
            },
            body,
        }
    }

    pub fn ret(e: Expr) -> Stmt {
        Stmt::Ret(e, Span::default())
    }

    pub fn param(name: Ident, ty: Ty) -> Param {
        Param {
            name,
            ty,
            span: Span::default(),
        }
    }

    pub fn bin(lhs: Expr, rhs: Expr, op: BinaryOp) -> Expr {
        Expr {
            node: ExprKind::Binary {
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
                op,
            },
            ty: infer_ty(),
            span: Span::default(),
        }
    }

    pub fn cmp(lhs: Expr, rhs: Expr, op: CmpOp) -> Expr {
        Expr {
            node: ExprKind::Logical {
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
                op,
            },
            ty: infer_ty(),
            span: Span::default(),
        }
    }

    pub fn span() -> Span {
        Span::default()
    }

    pub fn range(lo: Expr, hi: Expr) -> Expr {
        Expr {
            node: ExprKind::Range(Box::new(lo), Box::new(hi)),
            ty: infer_ty(),
            span: Span::default(),
        }
    }

    // funny name to avoid conclusion with rust's builtin bool type
    pub fn bol(x: bool) -> Expr {
        Expr {
            node: ExprKind::Lit(Lit::Bool(x), Span::default()),
            ty: infer_ty(),
            span: Span::default(),
        }
    }

    pub fn num(x: usize) -> Expr {
        Expr {
            node: ExprKind::Lit(Lit::Number(x as f64), Span::default()),
            ty: infer_ty(),
            span: Span::default(),
        }
    }

    pub fn num_f(x: f64) -> Expr {
        Expr {
            node: ExprKind::Lit(Lit::Number(x), Span::default()),
            ty: infer_ty(),
            span: Span::default(),
        }
    }

    pub fn txt(x: &str) -> Expr {
        Expr {
            node: ExprKind::Lit(Lit::String(x.to_string()), Span::default()),
            ty: infer_ty(),
            span: Span::default(),
        }
    }

    pub fn variant(ident: Ident, data: VariantData) -> Variant {
        Variant {
            ident,
            data,
            span: span(),
        }
    }

    pub fn member(name: Ident, init: Expr) -> Member {
        Member {
            name,
            init,
            span: Span::default(),
        }
    }

    pub fn this() -> Expr {
        Expr {
            node: ExprKind::This,
            ty: infer_ty(),
            span: Span::default(),
        }
    }

    pub fn unary(rhs: Expr, op: UnaryOp) -> Expr {
        Expr {
            node: ExprKind::Unary {
                rhs: Box::new(rhs),
                op,
            },
            ty: infer_ty(),
            span: Span::default(),
        }
    }

    pub fn path_expr(p: Path) -> Expr {
        Expr {
            node: ExprKind::Path(p),
            ty: infer_ty(),
            span: Span::default(),
        }
    }

    pub fn struct_lit(path: Path, members: Vec<Member>) -> Expr {
        Expr {
            node: ExprKind::Struct { path, members },
            ty: infer_ty(),
            span: Span::default(),
        }
    }

    pub fn call(callee: Expr, args: Vec<Expr>) -> Expr {
        Expr {
            node: ExprKind::Call {
                callee: Box::new(callee),
                args,
            },
            ty: infer_ty(),
            span: Span::default(),
        }
    }

    pub fn index(callee: Expr, index: Expr) -> Expr {
        Expr {
            node: ExprKind::Index {
                callee: Box::new(callee),
                index: Box::new(index),
            },
            ty: infer_ty(),
            span: Span::default(),
        }
    }

    pub fn field(callee: Expr, name: Ident) -> Expr {
        Expr {
            node: ExprKind::Field(Box::new(callee), name),
            ty: infer_ty(),
            span: Span::default(),
        }
    }

    pub fn ty(kind: TyKind) -> Ty {
        Ty {
            kind,
            span: Span::default(),
        }
    }

    pub fn array_ty(elem: Ty) -> Ty {
        Ty {
            kind: TyKind::Array(Box::new(elem)),
            span: Span::default(),
        }
    }

    pub fn path_ty(p: Path) -> Ty {
        Ty {
            kind: TyKind::Path(p),
            span: Span::default(),
        }
    }

    pub fn unit_ty() -> Ty {
        Ty::default_unit_type(Span::default())
    }

    pub fn infer_ty() -> Ty {
        Ty::default_infer_type(Span::default())
    }

    pub fn assign(target: Expr, value: Expr) -> Expr {
        Expr {
            node: ExprKind::Assign {
                target: Box::new(target),
                value: Box::new(value),
            },
            ty: infer_ty(),
            span: Span::default(),
        }
    }

    macro_rules! path (
        ($p:path) => ( {
            let str = stringify!($p).to_string();
            let segments = str.split("::")
                .map(|s| s.to_string())
                .map(|s| Ident::new(s, Span::default()))
                .collect::<Vec<_>>();
            Path::new(segments, Span::default())
		}
        );
    );

    pub fn block(stmts: Vec<Stmt>) -> Block {
        Block::new(stmts, Span::default())
    }

    pub fn while_stmt(cond: Expr, body: Block) -> Stmt {
        Stmt::While {
            cond,
            body,
            span: span(),
        }
    }
    pub fn if_stmt(
        cond: Expr,
        body: Block,
        else_branches: Vec<ElseBranch>,
        final_branch: Option<FinalBranch>,
    ) -> Stmt {
        Stmt::If {
            cond,
            body,
            else_branches,
            final_branch,
            span: span(),
        }
    }

    pub fn else_branch(cond: Expr, body: Block) -> ElseBranch {
        ElseBranch {
            cond,
            body,
            span: span(),
        }
    }

    pub fn final_branch(body: Block) -> FinalBranch {
        FinalBranch { body, span: span() }
    }

    macro_rules! tup {
		( $($x:expr),* ) => (
			expr!( {
				let mut tmp_vec: Vec<Expr> = Vec::new();
				$(
					tmp_vec.push($x);
				)*
				ExprKind::Tup(tmp_vec)
			}
			)
		)
	}

    pub fn tup_ty(elems: Vec<Ty>) -> Ty {
        Ty {
            kind: TyKind::Tup(elems),
            span: Span::default(),
        }
    }

    macro_rules! expr {
        ($x:expr) => {
            Expr {
                node: $x,
                span: Span::default(),
                ty: infer_ty(),
            }
        };
    }

    macro_rules! array {
		( $($x:expr),* ) => (
			expr!( {
				let mut tmp_vec: Vec<Expr> = Vec::new();
				$(
					tmp_vec.push($x);
				)*
				ExprKind::Array(tmp_vec)
			}
			)
		)
	}
}
