use crate::ast::*;
use crate::errors::*;
use crate::typer::*;
use std::collections::*;

pub struct ImplReoderPass {
    impls: HashMap<String, Vec<FnDecl>>,
    err: Vec<Diagnostic>,
}

impl<'a> ImplReoderPass {
    pub fn new() -> Self {
        Self {
            impls: HashMap::new(),
            err: Vec::new(),
        }
    }

    pub fn reorder(&mut self, ast: &mut AST) -> Vec<Diagnostic> {
        for stmt in ast.iter() {
            if let Decl::Impl {
                ref target,
                ref fn_decls,
                span: _,
            } = stmt
            {
                // NOTE(Simon): This can never fail, because if an impl block does not have a name the parser will not accept it.
                // FIXME(Simon): The current system does not allow users to define impls on external types, i.e. types outside their own src module!
                // FIXME(Simon): To allow this we need to look at the whole path of the impl name, not just the first elem!
                let name = target.first().unwrap().lexeme.clone();
                let fns = fn_decls.clone();
                self.impls.insert(name, fns);
            }
        }
        for stmt in ast.iter_mut() {
            if let Decl::TyDecl(t) = stmt {
                if let Some(methods) = self.impls.remove(&t.name().lexeme) {
                    let methods = methods
                        .into_iter()
                        .map(|f| (f.header.name.lexeme.clone(), f.clone()))
                        .collect();
                    t.add_methods(methods);
                }
            }
        }
        self.err.clone()
    }

    fn span_err(&mut self, kind: ErrKind, span: Span) {
        self.err.push(Diagnostic {
            kind,
            span,
            suggestions: Vec::new(),
        });
    }
}

pub struct TyLoweringPass {
    ty_table: HashSet<String>,
    err: Vec<Diagnostic>,
}

impl TyLoweringPass {
    pub fn new() -> Self {
        Self {
            ty_table: HashSet::new(),
            err: Vec::new(),
        }
    }
    pub fn apply(&mut self, ast: &mut AST) -> Vec<Diagnostic> {
        for node in ast {
            node.accept(self);
        }
        self.err.clone()
    }

    fn span_err(&mut self, kind: ErrKind, span: Span) -> &mut Diagnostic {
        self.err.push(Diagnostic {
            kind,
            span,
            suggestions: Vec::new(),
        });
        self.err.last_mut().unwrap()
    }

    // pub fn get_lowered_ty(&mut self, t: &Ty) -> Ty {
    //     match &t.kind {
    //         TyKind::Path(ref p) => {
    //             if p.len() != 0 {
    //                 self.span_err(
    //                     ErrKind::Internal(
    //                         "Typenpfade mit mehr als 1 Elementen werden noch nicht unterstuezt!"
    //                             .to_string(),
    //                     ),
    //                     p.span.clone(),
    //                 );
    //             }
    //             let ty = self.ty_table.get(&p.first().unwrap().lexeme);
    //             match ty {
    //                 Some(t) => t.clone(),
    //                 None => {
    //                     self.span_err(
    //                         ErrKind::Type(TypeErr::TyNotFound(p.first().unwrap().lexeme.clone())),
    //                         p.first().unwrap().span.clone(),
    //                     );
    //                     Ty::default_unit_type(p.span.clone())
    //                 }
    //             }
    //         }
    //         TyKind::Array(ref elem) => Ty {
    //             kind: TyKind::Array(box self.get_lowered_ty(elem)),
    //             span: t.span.clone(),
    //         },
    //         TyKind::Tup(ref elems) => {
    //             let mut tup = Vec::new();
    //             for elem in elems {
    //                 tup.push(self.get_lowered_ty(elem));
    //             }
    //             Ty {
    //                 kind: TyKind::Tup(tup),
    //                 span: t.span.clone(),
    //             }
    //         }
    //         TyKind::Fn(params, ret) => {
    //             let params = params.iter().map(|p| self.get_lowered_ty(p)).collect();
    //             let ret = self.get_lowered_ty(&ret);
    //             Ty {
    //                 kind: TyKind::Fn(params, box ret),
    //                 span: t.span.clone(),
    //             }
    //         }
    //         TyKind::Infer
    //         | TyKind::Id(_)
    //         | TyKind::Num
    //         | TyKind::Bool
    //         | TyKind::Text
    //         | TyKind::Poly(_) => t.clone(),
    //     }
    // }

    fn lower_ty(&mut self, expr: &mut Expr) {
        expr.accept(self);
    }
    fn lower_block(&mut self, block: &mut Block) {
        for stmt in block.stmts.iter_mut() {
            stmt.accept(self);
        }
    }
    fn lower_fn(&mut self, f: &mut FnDecl) {
        for param in f.header.params.iter_mut() {
            param.ty.infer_internal()
        }
        self.lower_block(&mut f.body);
        f.header.ret_ty.infer_internal();
    }
}

impl Visitor for TyLoweringPass {
    type Result = ();

    fn visit_decl(&mut self, decl: &mut Decl) -> Self::Result {
        match decl {
            Decl::TyDecl(t) => match t {
                TyDecl::Enum(e) => {
                    for (_, method) in e.methods.iter_mut() {
                        self.lower_fn(method);
                    }
                }
                TyDecl::Struct(s) => {
                    for (_, ty) in s.fields.iter_mut() {
                        // TODO(Simon): check availability of types
                        ty.infer_internal();
                    }
                    for (_, method) in s.methods.iter_mut() {
                        self.lower_fn(method);
                    }
                }
            },
            Decl::Fn(f) => {
                self.lower_fn(f);
            }
            _ => {}
        }
    }

    fn visit_stmt(&mut self, stmt: &mut Stmt) -> Self::Result {
        match stmt {
            Stmt::While {
                ref mut cond,
                ref mut body,
                ..
            } => {
                self.lower_ty(cond);
                self.lower_block(body);
            }
            Stmt::VarDef(ref mut vd) => {
                self.lower_ty(&mut vd.init);
                vd.ty.infer_internal();
            }
            Stmt::Expr(ref mut e) => {
                self.lower_ty(e);
            }
            Stmt::For {
                ref mut vardef,
                ref mut body,
                ..
            } => {
                vardef.ty.infer_internal();
                self.lower_block(body);
                self.lower_ty(&mut vardef.init);
            }
            Stmt::If {
                ref mut cond,
                ref mut body,
                ref mut else_branches,
                ref mut final_branch,
                ..
            } => {
                self.lower_ty(cond);
                self.lower_block(body);

                for branch in else_branches {
                    self.lower_ty(&mut branch.cond);
                    self.lower_block(&mut branch.body);
                }

                if let Some(fb) = final_branch {
                    self.lower_block(&mut fb.body);
                }
            }
            Stmt::Assign {
                ref mut target,
                ref mut rhs,
                ..
            } => {
                //self.subst_expr(lhs);
                self.lower_ty(rhs);
            }
            Stmt::Ret(ref mut val, _) => {
                self.lower_ty(val);
            }
            Stmt::Break(_) | Stmt::Continue(_) => {}
            Stmt::Block(ref mut block) => self.lower_block(block),
        }
    }
    fn visit_expr(&mut self, expr: &mut Expr) -> Self::Result {
        match expr.node {
            ExprKind::Binary {
                ref mut lhs,
                op: _,
                ref mut rhs,
            } => {
                self.lower_ty(lhs);
                self.lower_ty(rhs);
            }
            ExprKind::Logical {
                ref mut lhs,
                op: _,
                ref mut rhs,
            } => {
                self.lower_ty(lhs);
                self.lower_ty(rhs);
            }
            ExprKind::Unary { ref mut rhs, .. } => {
                self.lower_ty(rhs);
            }
            ExprKind::Index {
                ref mut callee,
                ref mut index,
            } => {
                self.lower_ty(callee);
                self.lower_ty(index);
            }
            ExprKind::Array(ref mut elems) => {
                for mut elem in elems {
                    self.lower_ty(&mut elem);
                }
            }
            ExprKind::Range(ref mut lo, ref mut hi) => {
                self.lower_ty(lo);
                self.lower_ty(hi);
            }
            ExprKind::Tup(ref mut elems) => {
                for elem in elems {
                    self.lower_ty(elem);
                }
            }
            ExprKind::Field(ref mut callee, _) => self.lower_ty(callee),
            ExprKind::Call {
                ref mut callee,
                ref mut args,
            } => {
                self.lower_ty(callee);
                args.iter_mut().for_each(|elem| self.lower_ty(elem));
            }
            ExprKind::Intrinsic {
                kind: _,
                ref mut args,
            } => args.iter_mut().for_each(|elem| self.lower_ty(elem)),
            ExprKind::Struct {
                name: _,
                ref mut members,
            } => members
                .iter_mut()
                .for_each(|member| self.lower_ty(&mut member.init)),
            ExprKind::Path(_) | ExprKind::Lit(_) | ExprKind::This(_) | ExprKind::Var(_) => {}
        }
        expr.ty.infer_internal();
    }
}
