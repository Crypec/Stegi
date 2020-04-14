use super::lexer::*;
use std::convert::TryFrom;

pub trait ASTNode {
    fn accept<V: Visitor>(&mut self, visitor: &mut V) -> V::Result;
}

pub trait Visitor {
    type Result;

    fn visit_stmt(&mut self, stmt: &mut Stmt) -> Self::Result;
    fn visit_expr(&mut self, expr: &mut Expr) -> Self::Result;
}

#[derive(Derivative)]
#[derivative(Debug)]
#[derive(PartialEq)]
pub enum ExprKind {
    #[derivative(Debug = "transparent")]
    Binary(Binary),

    #[derivative(Debug = "transparent")]
    Unary(Unary),

    #[derivative(Debug = "transparent")]
    Logical(Logical),

    Struct(Struct),

    Tup(Vec<Expr>),

    #[derivative(Debug = "transparent")]
    Path(Path),

    #[derivative(Debug = "transparent")]
    Index(Index),

    Assign(Box<Expr>, Box<Expr>),

    Array(Vec<Expr>),

    Range(Box<Expr>, Box<Expr>),

    Literal(Literal, Span),

    #[derivative(Debug = "transparent")]
    Variable(Variable),

    Field(Box<Expr>, Ident),

    This(Variable, Span),

    #[derivative(Debug = "transparent")]
    Call(Call),
}

#[derive(Debug, PartialEq)]
pub struct Index {
    pub callee: Box<Expr>,
    pub index: Box<Expr>,
}

#[derive(Debug, PartialEq)]
pub struct Member {
    pub ident: Ident,
    pub expr: Box<Expr>,
    pub span: Span,
}

impl Member {
    pub fn new(ident: Ident, expr: Expr, span: Span) -> Self {
        Self {
            ident,
            expr: Box::new(expr),
            span,
        }
    }
}

#[derive(Debug, PartialEq)]
pub struct Struct {
    pub pat: Path,
    pub members: Vec<Member>,
}

#[derive(Derivative)]
#[derivative(Debug)]
#[derive(PartialEq)]
pub enum Stmt {
    #[derivative(Debug = "transparent")]
    Expr(Expr),

    #[derivative(Debug = "transparent")]
    Local(Box<Local>),

    #[derivative(Debug = "transparent")]
    EnumDecl(EnumDecl),

    #[derivative(Debug = "transparent")]
    Block(Block),

    If(Expr, Block, Option<Box<Stmt>>),
    While(Expr, Block),

    For(ForLoop),

    Break,

    Ret(Expr, Span),

    #[derivative(Debug = "transparent")]
    FnDecl(FnDecl),

    ImplBlock {
        target: Path,
        fn_decls: Vec<FnDecl>,
        span: Span,
    },

    #[derivative(Debug = "transparent")]
    StructDecl(StructDecl),
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

impl EnumDecl {
    pub fn new(ident: Ident, variants: Vec<Variant>, span: Span) -> Self {
        EnumDecl {
            ident,
            variants,
            span,
        }
    }
}

#[derive(Debug, PartialEq)]
pub struct Variant {
    pub span: Span,
    pub ident: Ident,
    pub data: VariantData,
}

#[derive(Debug, PartialEq)]
pub enum VariantData {
    Tuple(Vec<Ty>),
    Unit,
}

#[derive(Debug, PartialEq)]
pub struct Local {
    pub ident: Ident, // TODO(Simon): this should really be a pattern
    pub init: Expr,
    pub ty: Ty,
    pub span: Span,
}

impl Local {
    pub fn new(init: Expr, ident: Ident, ty: Ty, span: Span) -> Self {
        Local {
            init,
            ident,
            ty,
            span,
        }
    }
}

#[derive(Debug, PartialEq)]
pub struct ForLoop {
    pub it: Expr,
    pub var: Ident,
    pub body: Block,
    pub span: Span,
}

impl ForLoop {
    pub fn new(it: Expr, var: Ident, body: Block, span: Span) -> Self {
        ForLoop {
            it,
            var,
            body,
            span,
        }
    }
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
    pub ty: TyKind,
    pub span: Span,
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
    type Error = String;
    fn try_from(t: Token) -> Result<Ident, Self::Error> {
        match t.kind {
            TokenKind::Ident(name) => Ok(Ident::new(name.to_owned(), t.span)),
            _ => Err(format!(
                "token konnte nicht in ident umgewandelt werden: {:#?}",
                t
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
    Array(Box<TyKind>),

    Struct(Path),

    Enum(Path),

    #[derivative(Debug = "transparent")]
    Tup(Vec<TyKind>),

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

    pub fn new_unit(kind: TyKind, span: Span) -> Self {
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
    pub params: Vec<(Ident, Ty)>,
    pub ret_ty: Ty,
}

impl FnSig {
    pub fn new(name: Ident, params: Vec<(Ident, Ty)>, ret_ty: Ty) -> Self {
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

impl ExprKind {
    pub fn binary(lhs: Expr, rhs: Expr, op: BinOp) -> Self {
        ExprKind::Binary(Binary {
            lhs: Box::new(lhs),
            rhs: Box::new(rhs),
            op,
        })
    }
    pub fn logical(lhs: Expr, rhs: Expr, op: CmpOp) -> Self {
        ExprKind::Logical(Logical {
            lhs: Box::new(lhs),
            rhs: Box::new(rhs),
            op,
        })
    }

    pub fn unary(rhs: Expr, op: UnaryOp) -> Self {
        ExprKind::Unary(Unary {
            rhs: Box::new(rhs),
            op,
        })
    }

    pub fn field(lhs: Expr, ident: Ident) -> Self {
        ExprKind::Field(Box::new(lhs), ident)
    }

    pub fn call(callee: Expr, args: Vec<Expr>) -> Self {
        ExprKind::Call(Call {
            callee: Box::new(callee),
            args,
        })
    }
    pub fn index(callee: Expr, index: Expr) -> Self {
        ExprKind::Index(Index {
            callee: Box::new(callee),
            index: Box::new(index),
        })
    }

    pub fn struct_lit(pat: Path, members: Vec<Member>) -> Self {
        ExprKind::Struct(Struct { pat, members })
    }
}

impl Default for ExprKind {
    fn default() -> Self {
        ExprKind::Tup(Vec::new())
    }
}

#[derive(Debug, PartialEq)]
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

#[derive(Debug, PartialEq)]
pub struct Binary {
    pub lhs: Box<Expr>,
    pub rhs: Box<Expr>,
    pub op: BinOp,
}

#[derive(Debug, PartialEq)]
pub enum BinOp {
    Plus,
    Minus,
    Multiply,
    Divide,
}

impl TryFrom<TokenKind> for BinOp {
    type Error = String;

    fn try_from(value: TokenKind) -> Result<Self, Self::Error> {
        match value {
            TokenKind::Operator(Operator::Plus) => Ok(BinOp::Plus),
            TokenKind::Operator(Operator::Minus) => Ok(BinOp::Minus),
            TokenKind::Operator(Operator::Star) => Ok(BinOp::Multiply),
            TokenKind::Operator(Operator::Slash) => Ok(BinOp::Divide),
            _ => Err(format!(
                "nicht erlaubte umwandlung in bin op token {}",
                value
            )),
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum CmpOp {
    EqEq,
    NotEq,
    Greater,
    GreaterEq,
    Less,
    LessEq,
}

impl TryFrom<TokenKind> for CmpOp {
    type Error = String;

    fn try_from(value: TokenKind) -> Result<Self, Self::Error> {
        match value {
            TokenKind::Operator(Operator::EqEq) => Ok(CmpOp::EqEq),
            TokenKind::Operator(Operator::NotEq) => Ok(CmpOp::NotEq),
            TokenKind::Operator(Operator::Greater) => Ok(CmpOp::Greater),
            TokenKind::Operator(Operator::GreaterEq) => Ok(CmpOp::GreaterEq),
            TokenKind::Operator(Operator::Less) => Ok(CmpOp::LessEq),
            TokenKind::Operator(Operator::LessEq) => Ok(CmpOp::LessEq),
            _ => Err(format!(
                "nicht erlaubte umwandlung in cmp op token {}",
                value
            )),
        }
    }
}

#[derive(Debug, PartialEq)]
pub struct Unary {
    pub rhs: Box<Expr>,
    pub op: UnaryOp,
}

// NOTE(Simon): I don't know how the parser is going to handle +10 with the current grammar rules
// NOTE(Simon): maybe we need to include plus
#[derive(Debug, PartialEq)]
pub enum UnaryOp {
    Minus,
    Not,
}

impl TryFrom<TokenKind> for UnaryOp {
    type Error = String;

    fn try_from(value: TokenKind) -> Result<Self, Self::Error> {
        match value {
            TokenKind::Operator(Operator::Not) => Ok(UnaryOp::Not),
            TokenKind::Operator(Operator::Minus) => Ok(UnaryOp::Minus),
            _ => Err(format!(
                "nicht erlaubte umwandlung in cmp op token {}",
                value
            )),
        }
    }
}

#[derive(Debug, PartialEq)]
pub struct Logical {
    pub lhs: Box<Expr>,
    pub rhs: Box<Expr>,
    pub op: CmpOp,
}

#[derive(Debug, PartialEq)]
pub struct Call {
    pub callee: Box<Expr>,
    pub args: Vec<Expr>,
}

#[derive(Debug, PartialEq)]
pub struct Variable {
    pub name: String,
    pub depth: Option<usize>,
    pub function_depth: usize,
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
            lo: std::cmp::min(self.lo, rhs.lo),
            hi: std::cmp::max(self.hi, rhs.hi),
        }
    }
}

impl Variable {
    pub fn new_local(name: &str) -> Self {
        Variable {
            name: name.to_owned(),
            depth: Some(0),
            function_depth: 0,
        }
    }
    pub fn new_global(name: &str) -> Self {
        Variable {
            name: name.to_owned(),
            depth: None,
            function_depth: 0,
        }
    }
}
