use crate::ast::*;
use crate::errors::*;
use std::collections::HashMap;

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

// pub struct MethodReorderingPass {
//     ty_table: HashMap<String, TyDecl>,
//     err: Vec<Diagnostic>,
// }

// impl MethodReorderingPass {
//     fn new() -> Self {
//         Self {
//             ty_table: HashMap::new(),
//             err: Vec::new(),
//         }
//     }

//     pub fn reorder(&mut self, ast: &mut AST) -> Vec<Diagnostic> {
//         todo!();
//     }

//     pub fn fill_ty_table(&mut self, ast: &AST) {
//         for node in ast {
//             if let Decl::TyDecl(t) = node {
//                 self.ty_table.insert(t.name().lexeme, t.clone());
//             }
//         }
//     }
// }
