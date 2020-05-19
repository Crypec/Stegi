use crate::ast::*;

use std::convert::From;

use crate::errors::*;
use crate::lexer::Lit;
use std::collections::HashMap;

use crate::ast::*;
use crate::cxt::Cxt;

#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    Num(f64),
    Text(String),
    Bool(bool),
    Object(HashMap<String, Value>),
    Array(Vec<Value>),
}

pub struct Interp {
    cxt: Cxt<String, Expr>,
}

//macro_rules! bin_op {
// 	($lhs:ident, $op:tt, $rhs:ident, $ty:pat) => {
// 		let lhs = self.eval($lhs)?;
// 		let rhs = self.eval($rhs)?;
// 		match (lhs, rhs) {
// 			($ty(a), $ty(b)) => $ty(a $op b),
// 			_ => todo!(),
// 		}
// 	}
// }

impl From<Lit> for Value {
    fn from(l: Lit) -> Self {
        match l {
            Lit::Number(n) => Value::Num(n),
            Lit::String(t) => Value::Text(t),
            Lit::Bool(b) => Value::Bool(b),
        }
    }
}

impl Interp {
    pub fn new() -> Self {
        Self { cxt: Cxt::new() }
    }

    pub fn eval(&mut self, e: &Expr) -> Result<Value, Diagnostic> {
        match e.node {
            ExprKind::Binary {
                ref lhs,
                ref op,
                ref rhs,
            } => {
                let lhs = self.eval(lhs)?;
                let rhs = self.eval(rhs)?;
                match (lhs, rhs) {
                    // TODO(Simon): check for overflows etc...
                    (Value::Num(a), Value::Num(b)) => match op {
                        BinaryOp::Plus => Ok(Value::Num(a + b)),
                        BinaryOp::Minus => Ok(Value::Num(a - b)),
                        BinaryOp::Multiply => Ok(Value::Num(a * b)),
                        BinaryOp::Divide => Ok(Value::Num(a / b)),
                    },
                    _ => panic!("error in typechecker: Invalid type for binary op!"),
                }
            }
            ExprKind::Logical {
                ref lhs,
                ref op,
                ref rhs,
            } => {
                let lhs = self.eval(lhs)?;
                let rhs = self.eval(rhs)?;
                match op {
                    CmpOp::EqEq => Ok(Value::Bool(lhs == rhs)),
                    CmpOp::NotEq => Ok(Value::Bool(lhs != rhs)),
                    CmpOp::Greater => match (lhs, rhs) {
                        (Value::Num(a), Value::Num(b)) => Ok(Value::Bool(a > b)),
                        _ => panic!("error in typechecker: Invalid type for cmpop: >"),
                    },
                    CmpOp::GreaterEq => match (lhs, rhs) {
                        (Value::Num(a), Value::Num(b)) => Ok(Value::Bool(a >= b)),
                        _ => panic!("error in typechecker: Invalid type for cmpop: >="),
                    },
                    CmpOp::Less => match (lhs, rhs) {
                        (Value::Num(a), Value::Num(b)) => Ok(Value::Bool(a < b)),
                        _ => panic!("error in typechecker: Invalid type for cmpop: <"),
                    },
                    CmpOp::LessEq => match (lhs, rhs) {
                        (Value::Num(a), Value::Num(b)) => Ok(Value::Bool(a <= b)),
                        _ => panic!("error in typechecker: Invalid type for cmpop: <="),
                    },
                    CmpOp::And => match (lhs, rhs) {
                        (Value::Bool(a), Value::Bool(b)) => Ok(Value::Bool(a && b)),
                        _ => panic!("error in typechecker: Invalid type for cmpop: and"),
                    },
                    CmpOp::Or => match (lhs, rhs) {
                        (Value::Bool(a), Value::Bool(b)) => Ok(Value::Bool(a || b)),
                        _ => panic!("error in typechecker: Invalid type for cmpop: or"),
                    },
                }
            }
            ExprKind::Unary { ref rhs, ref op } => match op {
                UnaryOp::Minus => {
                    if let Value::Num(n) = self.eval(rhs)? {
                        return Ok(Value::Num(-1.0 * n));
                    } else {
                        panic!("error in typechecker: Invalid type for unary: -");
                    }
                }
                UnaryOp::Not => {
                    if let Value::Bool(b) = self.eval(rhs)? {
                        return Ok(Value::Bool(!b));
                    } else {
                        panic!("error in typechecker: Invalid type for unary: !");
                    }
                }
            },
            // NOTE(Simon): this clone may be unecessary if we decide to mutate the ast on the fly
            ExprKind::Lit(ref l) => Ok(l.clone().into()),
            _ => todo!(),
        }
    }

    pub fn interp(&mut self, ast: &mut Vec<Stmt>) {
        for n in ast {
            n.accept(self).unwrap();
        }
    }
}

impl Visitor for Interp {
    type Result = Result<Value, Diagnostic>;

    fn visit_expr(&mut self, e: &mut Expr) -> Self::Result {
        match e.node {
            _ => todo!(),
        }
    }

    fn visit_stmt(&mut self, s: &mut Stmt) -> Self::Result {
        match s {
            Stmt::VarDef(ref v) => {
                println!("{:#?}", self.eval(&v.init));
                todo!();
            }
            Stmt::FnDecl(ref mut fd) => {
                for stmt in fd.body.stmts.iter_mut() {
                    stmt.accept(self)?;
                }
                todo!();
            }
            _ => todo!(),
        }
    }
}
