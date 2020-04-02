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
    type Result = ();

    fn visit_stmt(&mut self, stmt: &Stmt) -> Self::Result {}
    fn visit_expr(&mut self, e: &Expr) -> Self::Result {
        infer(&self.ctx.env, &e);
    }
}

impl Typer {
    pub fn new() -> Self {
        Self {
            ctx: Context::new(),
        }
    }

    pub fn infer(&mut self, ast: &mut Vec<Stmt>) {
        ast.into_iter().for_each(|stmt| {
            stmt.accept(self);
        })
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
    fn add(&self, name: String, t: Ty) -> Self {
        let mut new_env = self.env.clone();
        new_env.insert(name, t);
        Self {
            next: self.next,
            env: new_env,
        }
    }

    fn new_id(&mut self) -> Ty {
        let new_id = self.next;
        self.next += 1;
        Ty {
            kind: TyKind::Infer(new_id),
            span: Span::new(0, 0),
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
