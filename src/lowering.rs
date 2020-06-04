use crate::ast::*;
use crate::errors::*;
use std::collections::HashMap;

pub struct ImplReoderPass {
    //ty_table: HashMap<&'a String, &'a Stmt>,
    err: Vec<Diagnostic>,
}

impl<'a> ImplReoderPass {
    pub fn new() -> Self {
        Self {
            //       ty_table: HashMap::new(),
            err: Vec::new(),
        }
    }

    fn span_err(&mut self, kind: ErrKind, span: Span) {
        self.err.push(Diagnostic {
            kind,
            span,
            suggestions: Vec::new(),
        });
    }
}

pub fn reorder(ast: &mut AST) {
    let mut impls = HashMap::new();
    {
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
                impls.insert(name, fns);
            }
        }
        for stmt in ast.iter_mut() {
            if let Decl::TyDecl(t) = stmt {
                if let Some(methods) = impls.remove(&t.name().lexeme) {
                    t.add_methods(methods);
                }
            }
        }
        if !impls.is_empty() {
            panic!("TODO(Simon): report error for invalid impls on unknown types");
        }
    }
}
