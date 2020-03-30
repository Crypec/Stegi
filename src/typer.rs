use std::collections::HashMap;

use crate::ast::*;
use crate::errors::*;
use crate::lexer::*;

type Env = HashMap<String, Ty>;

type TypeResult = Result<Ty, TypeError>;

// this is a bit ugly, but we have to do it because rust does not allow impls on type external types
// an aliased type does not create a new type, therefore this workaround is needed
struct Subst(HashMap<usize, Ty>);

impl Subst {
    fn apply(&self, t: Ty) -> Ty {
        match t.kind {
            TyKind::Path(_) => t,
            TyKind::Infer(id) => self.get(&id).unwrap_or(t),
            _ => todo!(),
        }
    }

    fn get(&self, id: &usize) -> Option<Ty> {
        self.0.get(id).cloned()
    }
}

pub struct Typer {
    ctx: Context,
}

impl Visitor for Typer {
    type Result = Result<Ty, TypeError>;

    fn visit_stmt(&mut self, stmt: &Stmt) -> Self::Result {
        todo!()
    }
    fn visit_expr(&mut self, e: &Expr) -> Self::Result {
        infer(&self.ctx.env, &e);
        Err(TypeError::InvalidType)
    }
}

impl Typer {
    pub fn new() -> Self {
        Self {
            ctx: Context::new(),
        }
    }
}

struct Context {
    next: usize,
    env: Env,
}

impl Context {
    pub fn new() -> Self {
        Self {
            next: 0,
            env: Env::new(),
        }
    }
}

pub fn infer(env: &Env, e: &Expr) -> TypeResult {
    match e.node {
        ExprKind::Literal(Literal::Number(_), s) => Ok(Ty::new_unit(TyKind::Num, s)),
        ExprKind::Variable(ref var) => env
            .get(&var.name)
            .cloned()
            .ok_or(TypeError::VarNameNotFound),
        _ => panic!("invalid type!! {:#?}", e.node),
    }
}
