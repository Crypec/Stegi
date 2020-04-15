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

#[derive(PartialEq, Debug)]
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
    Struct { pat: Path, members: Vec<Member> },

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
    This(Ident),

    /// function call e.g. foo(-42, 1, 1)
    /// example: foo    (-42,     10)
    ///          ^-callee ^-arg0  ^-arg1
    Call { callee: Box<Expr>, args: Vec<Expr> },
}

#[derive(Debug, PartialEq)]
pub struct Member {
    pub name: Ident,
    pub init: Box<Expr>,
    pub span: Span,
}

impl Member {
    pub fn new(name: Ident, expr: Expr, span: Span) -> Self {
        Self {
            name,
            init: Box::new(expr),
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

    EnumDecl(EnumDecl),

    Block(Block),

    If(Branch),

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
}

#[derive(Debug, PartialEq)]
pub enum Branch {
    Primary { cond: Expr, body: Block },
    Secondary { cond: Expr, body: Block },
    Final { body: Block },
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
pub enum BinaryOp {
    Plus,
    Minus,
    Multiply,
    Divide,
}

impl TryFrom<TokenKind> for BinaryOp {
    type Error = String;

    fn try_from(value: TokenKind) -> Result<Self, Self::Error> {
        match value {
            TokenKind::Operator(Operator::Plus) => Ok(Self::Plus),
            TokenKind::Operator(Operator::Minus) => Ok(Self::Minus),
            TokenKind::Operator(Operator::Star) => Ok(Self::Multiply),
            TokenKind::Operator(Operator::Slash) => Ok(Self::Divide),
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
            TokenKind::Operator(Operator::Less) => Ok(CmpOp::Less),
            TokenKind::Operator(Operator::LessEq) => Ok(CmpOp::LessEq),
            _ => Err(format!(
                "nicht erlaubte umwandlung in cmp op token {}",
                value
            )),
        }
    }
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
