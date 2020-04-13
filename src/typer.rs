use colored::*;
use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use ngrammatic::{CorpusBuilder, Pad};

use crate::ast::*;
use crate::errors::Diagnostic;
use crate::lexer::*;
use crate::session::*;

// NOTE(Simon): we might need to adjust this threshold to avoid too many false positives
const WORD_CMP_TRESHOLD: f32 = 0.2;

pub struct Typer {
    stack: Vec<HashMap<String, Ty>>,
    fn_table: HashMap<String, FnDecl>,
    ty_table: HashMap<String, StructDecl>,
    sess: Rc<RefCell<Session>>,
}

impl Typer {
    pub fn new(sess: Rc<RefCell<Session>>) -> Self {
        Self {
            stack: Vec::new(),
            fn_table: HashMap::new(),
            ty_table: HashMap::new(),
            sess,
        }
    }

    pub fn infer(&mut self, ast: &mut Vec<Stmt>) {
        self.stack.push(HashMap::new());
        ast.iter_mut().for_each(|stmt| stmt.accept(self));
    }

    fn infer_block(&mut self, b: &mut Block) {
        self.make_cxt();
        b.stmts.iter_mut().for_each(|stmt| stmt.accept(self));
        self.drop_cxt();
    }
    fn infer_local(&mut self, local: &mut Local) {
        local.init.accept(self);
        self.insert_cxt(&local.ident.name, local.ty.clone());

        // if the user has not provided a type, we set it to the inferred expr type
        // but if the user has specified a type, we will use the specified type because it is
        // more likely it is correct, we are  going to emit in an error during the
        // type checking phase if the types are not compatible
        if let TyKind::Infer(_) = local.ty.kind {
            local.ty = local.init.ty.clone();
        }
    }

    fn infer_var(&mut self, p: &Path) -> Ty {
        // can never fail because we only got there because len of p is 1, otherwiese we have to infer an enum
        let var = p.segments.first().unwrap();
        match self.lookup_cxt(&var.name) {
            Some(ty) => ty,
            None => {
                let mut err = self.span_err(
                    "Typenfehler",
                    format!(
                        "Wir haben die Variable `{}` nicht gefunden!",
                        var.name.bold()
                    )
                    // I don't get why we need the conversion here, String implements Into String
                    .as_str(),
                    &var.span,
                );
                self.find_similar_var_names(&var.name)
                    .iter()
                    .for_each(|sug| {
                        let sim = format!("{:.2}", sug.1 * 100.0);
                        err.suggest(format!(
                            "Meintest du vielleicht `{}`? [Uebereinstimmung: {}%]",
                            sug.0.bold(),
                            sim
                        ))
                    });
                self.sess_register(err);
                Ty::default()
            }
        }
    }

    fn infer_enum_arm(&self) {
        todo!()
    }

    fn make_cxt(&mut self) {
        self.stack.push(self.stack.last().unwrap().clone());
    }

    fn insert_cxt(&mut self, name: &String, ty: Ty) {
        self.stack.last_mut().unwrap().insert(name.to_string(), ty);
    }

    fn lookup_cxt(&self, name: &String) -> Option<Ty> {
        self.stack.last().unwrap().get(name).cloned()
    }

    fn drop_cxt(&mut self) {
        self.stack.pop();
    }

    fn find_similar_var_names(&mut self, needle: &String) -> Vec<(String, f32)> {
        let mut corpus = CorpusBuilder::new().arity(2).pad_full(Pad::Auto).finish();
        self.stack
            .last()
            .unwrap()
            .iter()
            .for_each(|(k, _)| corpus.add_text(k));
        corpus
            .search(needle, WORD_CMP_TRESHOLD)
            .into_iter()
            .map(|res| (res.text, res.similarity))
            .collect()
    }

    fn span_err<S: Into<String>>(&mut self, desc: S, msg: S, span: &Span) -> Diagnostic {
        self.sess.borrow_mut().span_err(desc, msg, span)
    }

    fn sess_register(&mut self, d: Diagnostic) {
        self.sess.borrow_mut().sess_register(d);
    }
}

impl Visitor for Typer {
    type Result = ();

    fn visit_stmt(&mut self, s: &mut Stmt) -> Self::Result {
        match s {
            Stmt::Block(ref mut b) => self.infer_block(b),
            Stmt::Local(l) => self.infer_local(l),
            // TODO(Simon): typecheck branches
            Stmt::If(cond, body, _branches) => {
                cond.accept(self);
                self.infer_block(body);
            }
            Stmt::FnDecl(ref mut fn_decl) => self.infer_block(&mut fn_decl.body),
            _ => panic!("{:#?}", s),
        }
    }

    fn visit_expr(&mut self, e: &mut Expr) -> Self::Result {
        match e.node {
            ExprKind::Binary(ref mut bin) => {
                bin.lhs.accept(self);
                bin.rhs.accept(self);
            }
            ExprKind::Logical(ref mut cmp) => {
                cmp.lhs.accept(self);
                cmp.rhs.accept(self);
            }
            ExprKind::Literal(ref lit, _) => {
                e.ty.kind = match lit {
                    Literal::String(_) => TyKind::Text,
                    Literal::Bool(_) => TyKind::Text,
                    Literal::Number(_) => TyKind::Num,
                };
            }
            ExprKind::Path(ref p) => {
                if p.segments.len() == 1 {
                    // unwrap can never fail
                    self.infer_var(p);
                } else {
                    self.infer_enum_arm();
                }
            }

            _ => unimplemented!(),
        }
    }
}
