use super::lexer::*;

#[derive(Derivative)]
#[derivative(Debug)]
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

#[derive(Debug)]
pub struct Index {
    pub callee: Box<Expr>,
    pub index: Box<Expr>,
}

#[derive(Debug)]
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

#[derive(Debug)]
pub struct Struct {
    pub pat: Path,
    pub members: Vec<Member>,
}

#[derive(Derivative)]
#[derivative(Debug)]
pub enum Stmt {
    #[derivative(Debug = "transparent")]
    Expr(Expr),

    #[derivative(Debug = "transparent")]
    Local(Box<Local>),

    Var(Variable, Expr),

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

    #[derivative(Debug = "transparent")]
    StructDecl(StructDecl),
}

#[derive(Debug)]
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

#[derive(Debug)]
pub struct Variant {
    pub span: Span,
    pub ident: Ident,
    pub data: VariantData,
}

#[derive(Debug)]
pub enum VariantData {
    Tuple(Vec<Ty>),
    Unit,
}

#[derive(Debug)]
pub struct Local {
    pub init: Expr,
    pub pat: Path, // TODO(Simon): this should be a pattern to assign to
    pub ty: Option<Ty>,
    pub span: Span,
}

impl Local {
    pub fn new(init: Expr, pat: Path, ty: Option<Ty>, span: Span) -> Self {
        Local {
            init,
            pat,
            ty,
            span,
        }
    }
}

#[derive(Debug)]
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

#[derive(Debug, Clone)]
pub struct Path {
    pub segments: Vec<Ident>,
    pub span: Span,
}

impl Path {
    pub fn new(segments: Vec<Ident>, span: Span) -> Self {
        Path { segments, span }
    }
}

#[derive(Debug)]
pub struct Param {
    pub name: Ident,
    pub ty: TyKind,
    pub span: Span,
}

#[derive(Debug)]
pub struct StructDecl {
    pub name: Ident,
    pub fields: Vec<Field>,
    pub span: Span,
}

#[derive(Debug)]
pub struct Field {
    pub name: Ident,
    pub ty: Ty,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct Ident {
    pub name: String,
    pub span: Span,
}

impl From<Token> for Ident {
    fn from(item: Token) -> Self {
        Ident {
            name: item.lexeme,
            span: item.span,
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
pub enum TyKind {
    #[derivative(Debug = "transparent")]
    Array(Box<TyKind>),

    #[derivative(Debug = "transparent")]
    Tup(Vec<TyKind>),

    #[derivative(Debug = "transparent")]
	Infer(usize),

	#[derivative(Debug = "transparent")]
    Path(Path),
}

#[derive(Debug)]
pub struct Ty {
    pub kind: TyKind,
    pub span: Span,
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

	pub fn new(kind: TyKind, span: Span) -> Self {
		Self {
			kind,
			span,
		}
	}
}

#[derive(Debug)]
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

#[derive(Debug)]
pub struct FnDecl {
    pub head: FnSig,
    pub body: Block,
}

impl FnDecl {
    pub fn new(head: FnSig, body: Block) -> Self {
        FnDecl { head, body }
    }
}

#[derive(Debug)]
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
    pub fn binary(lhs: Expr, rhs: Expr, op: TokenKind) -> Self {
        ExprKind::Binary(Binary {
            lhs: Box::new(lhs),
            rhs: Box::new(rhs),
            op,
        })
    }
    pub fn logical(lhs: Expr, rhs: Expr, op: TokenKind) -> Self {
        ExprKind::Logical(Logical {
            lhs: Box::new(lhs),
            rhs: Box::new(rhs),
            op,
        })
    }

    pub fn unary(rhs: Expr, op: TokenKind) -> Self {
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

#[derive(Debug)]
pub struct Expr {
    pub node: ExprKind,
	pub ty: Ty,
	pub span: Span,
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

#[derive(Debug)]
pub struct Binary {
    pub lhs: Box<Expr>,
    pub rhs: Box<Expr>,
    pub op: TokenKind,
}

#[derive(Debug)]
pub struct Unary {
    pub rhs: Box<Expr>,
    pub op: TokenKind,
}

#[derive(Debug)]
pub struct Logical {
    pub lhs: Box<Expr>,
    pub rhs: Box<Expr>,
    pub op: TokenKind,
}

#[derive(Debug)]
pub struct Call {
    pub callee: Box<Expr>,
    pub args: Vec<Expr>,
}

#[derive(Debug)]
pub struct Variable {
    pub name: String,
    pub depth: Option<usize>,
    pub function_depth: usize,
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
