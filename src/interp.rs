use crate::ast::*;

use std::convert::From;
use std::fmt;

use crate::errors::*;
use crate::lexer::Lit;
use std::collections::HashMap;

use crate::ast::*;
use crate::cxt::Cxt;

macro_rules! cast(
    ($val:expr, $p:path) => {
        match $val {
            $p(x) => x,
            _ => {
                let pat = stringify!($pat);
                let val = stringify!($val);
                panic!("Invalide Umwandlung, {:#?} entspricht nicht folgendem Muster: {:#?} dies ist wahrscheinlich ein Fehler im Typenchecker!", val, pat);
            }
        }
    }
);

#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    Num(f64),
    Text(String),
    Bool(bool),
    Object(Path, HashMap<String, Value>),
    Tup(Vec<Value>),
    Array(Vec<Value>),
    Fn(FnDecl),
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Num(n) => write!(f, "{}", n),
            Value::Text(t) => write!(f, "{}", t),
            Value::Bool(b) => {
                let str_bool = match b {
                    true => "wahr",
                    false => "falsch",
                };
                write!(f, "{}", str_bool)
            }
            Value::Array(arr) => {
                let values = arr
                    .iter()
                    .map(|v| format!("{}", v))
                    .collect::<Vec<String>>()
                    .join(", ");
                write!(f, "[{}]", values)
            }
            Value::Tup(tup) => {
                let values = tup
                    .iter()
                    .map(|v| format!("{}", v))
                    .collect::<Vec<String>>()
                    .join(", ");
                write!(f, "({})", values)
            }
            Value::Object(path, obj) => write!(f, "{}: {:#?}", path, obj),
            Value::Fn(fun) => write!(f, "{:#?}", fun),
        }
    }
}

impl Value {
    fn is_num(&self) -> bool {
        match self {
            Value::Num(_) => true,
            _ => false,
        }
    }

    fn truthy(&self) -> bool {
        match self {
			Value::Bool(b) => *b,
			_ => panic!("Tried to check if value other than bool is truthy, this should not happen and is most definitely a bug in our typechecker!"),
		}
    }
}

pub struct Interp {
    // TODO(Simon): maybe we can refactor these into an "execution environment"?
    cxt: Cxt<String, Value>,
    ty_table: HashMap<String, TyDecl>,
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
            Lit::String(t) => {
                // FIXME(Simon): This is quite expensive as we have to do a memalloc and a memcopy for every string in the programm!
                let t = &t[1..t.len() - 1];
                Value::Text(t.to_string())
            }
            Lit::Bool(b) => Value::Bool(b),
        }
    }
}

impl Interp {
    pub fn new() -> Self {
        Self {
            cxt: Cxt::new(),
            ty_table: HashMap::new(),
        }
    }

    fn run_block(&mut self, block: &mut Block) -> Result<Option<Value>, Diagnostic> {
        self.cxt.make();
        for stmt in block.stmts.iter_mut() {
            let ret = stmt.accept(self)?;
            if let Some(_) = ret {
                self.cxt.drop();
                return Ok(ret);
            }
        }
        self.cxt.drop();
        Ok(None)
    }

    fn call_fn(&mut self, callee: &Expr, args: &Vec<Expr>) -> Result<Value, Diagnostic> {
        let callee = self.eval(callee)?;

        let mut args_eval = Vec::new();
        for arg in args {
            args_eval.push(self.eval(arg)?);
        }
        let mut fun = cast!(callee, Value::Fn);
        let params = fun.header.params;
        debug_assert_eq!(args_eval.len(), params.len());

        // FIXME(Simon): this needs to be a call to make_clean()!!!
        self.cxt.make();

        for (p, a) in params.iter().zip(args_eval.into_iter()) {
            let name = p.name.lexeme.clone();
            self.cxt.insert(name, a);
        }
        let ret = self.run_block(&mut fun.body)?;
        self.cxt.drop();
        match ret {
            Some(val) => Ok(val),
            None => Ok(Value::Tup(Vec::new())),
        }
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
            ExprKind::Path(ref p) => {
                if p.len() > 1 {
                    // TODO(Simon): lookup method in typdecl in ty_table
                    todo!()
                } else {
                    let name = &p.first().unwrap().lexeme;
                    debug_assert!(
                        self.cxt.get(&name).is_some(),
                        "Fehlende Variablen sollten eigentlich vom Typchecker erkannt werden!"
                    );
                    // FIXME(Simon): as always: we don't really need this clone
                    Ok(self.cxt.get(&name).unwrap().clone())
                }
            }
            ExprKind::Struct {
                ref path,
                ref members,
            } => {
                let mut obj = HashMap::new();
                for field in members.iter() {
                    let name = field.name.lexeme.clone();
                    let val = self.eval(&field.init.clone())?;
                    obj.insert(name, val);
                }
                Ok(Value::Object(path.clone(), obj))
            }
            ExprKind::Tup(ref elems) => {
                // TODO(Simon): refactor this to use a nice iterator
                let mut t = Vec::new();
                for e in elems {
                    t.push(self.eval(&e)?);
                }
                Ok(Value::Tup(t))
            }
            ExprKind::Array(ref arr) => {
                // TODO(Simon): refactor this to use a nice iterator
                let mut a = Vec::new();
                for e in arr {
                    a.push(self.eval(&e)?);
                }
                Ok(Value::Array(a))
            }
            ExprKind::Range(ref start, ref end) => {
                let (start, end) = match (self.eval(start)?, self.eval(end)?) {
					(Value::Num(start), Value::Num(end)) => (start, end),
					_ => panic!("Start und Endwert einer Reihe muessen immer den Typ Zahl haben. Es scheint als haetten wir einen Fehler im Typchecker!")
				};
                // FIXME(Simon): this is unsound because a f64::MAX can be bigger than i64::MAX
                let (start, end) = (start as i64, end as i64);
                let range = (start..end).map(|i| Value::Num(i as f64)).collect();
                Ok(Value::Array(range))
            }
            ExprKind::Index {
                ref callee,
                ref index,
            } => match (self.eval(callee)?, self.eval(index)?) {
                (Value::Array(arr), Value::Num(i)) => {
                    let i = i.trunc() as usize;
                    match arr.get(i) {
                        Some(v) => Ok(v.clone()),
                        None => panic!("index out of bounds!"),
                    }
                }
                _ => panic!(
                    "Fehler im Typchecker. Index must be of type callee: array and index: num!"
                ),
            },
            ExprKind::Field(ref _callee, ref _field) => {
                todo!();
            }
            ExprKind::This => todo!(),
            ExprKind::Call {
                ref callee,
                ref args,
            } => self.call_fn(&callee, &args),
            ExprKind::Val(ref v) => Ok(v.clone()),
            ExprKind::Intrinsic { ref kind, ref args } => match kind {
                Intrinsic::Print => {
                    //let fmt = cast!(self.eval(args.get(0).unwrap())?, Value::Text);
                    let mut args_eval = Vec::new();
                    for arg in args {
                        args_eval.push(self.eval(arg)?);
                    }
                    println!("{}", args_eval[0]);
                    Ok(Value::Num(0.0))
                }
                _ => todo!(),
            },
        }
    }

    fn fill_fn_table(&mut self, ast: &mut AST) {
        for decl in ast {
            if let Decl::Fn(f) = decl {
                let name = f.header.name.lexeme.clone();
                self.cxt.insert(name, Value::Fn(f.clone()));
            }
        }
    }

    fn fill_ty_table(&mut self, ast: &mut AST) {
        for decl in ast {
            if let Decl::TyDecl(t) = decl {
                let name = t.name().lexeme.clone();
                self.ty_table.insert(name, t.clone());
            }
        }
    }

    pub fn interp(&mut self, ast: &mut AST) {
        self.fill_fn_table(ast);
        self.fill_ty_table(ast);

        for d in ast.iter_mut() {
            if let Decl::Fn(f) = d {
                // TODO(Simon): we could clean this up a bit
                // let found_main = false;
                if f.header.name.lexeme == "Start" {
                    self.run_block(&mut f.body);
                }
                // if !found_main {
                //     self.span
                // }
            }
        }
    }
}

impl Visitor for Interp {
    type Result = Result<Option<Value>, Diagnostic>;

    fn visit_decl(&mut self, d: &mut Decl) -> Self::Result {
        todo!()
    }

    fn visit_expr(&mut self, e: &mut Expr) -> Self::Result {
        Ok(Some(self.eval(e)?))
    }

    fn visit_stmt(&mut self, s: &mut Stmt) -> Self::Result {
        match s {
            Stmt::VarDef(ref v) => {
                let val = self.eval(&v.init)?;
                let name = &v.pat.lexeme;
                self.cxt.insert(name.clone(), val);
                Ok(None)
            }
            Stmt::If {
                ref cond,
                ref mut body,
                ref mut else_branches,
                ref mut final_branch,
                ref span,
            } => {
                if self.eval(cond)?.truthy() {
                    let ret = self.run_block(body)?;
                    if let Some(_) = ret {
                        return Ok(ret);
                    }
                } else {
                    for branch in else_branches.iter_mut() {
                        if self.eval(&branch.cond)?.truthy() {
                            self.run_block(&mut branch.body)?;
                            return Ok(None);
                        }
                    }
                    if let Some(fb) = final_branch {
                        let ret = self.run_block(&mut fb.body)?;
                        if let Some(_) = ret {
                            return Ok(ret);
                        }
                    }
                }
                Ok(None)
            }
            Stmt::For {
                ref vardef,
                ref mut body,
                ref span,
            } => {
                self.cxt.make();
                let val = self.eval(&vardef.init)?;
                let loop_var = vardef.pat.lexeme.clone();
                let arr = match val {
					Value::Array(a) => a,
					_ => panic!("We can only iterate through arrays! If you are starring at this message trying to understand what happend, don't worry, this is most likely a bug in the typechecker!"),
				};
                for elem in arr {
                    self.cxt.insert(loop_var.clone(), elem);
                    let ret = self.run_block(body)?;
                    if let Some(_) = ret {
                        self.cxt.drop();
                        return Ok(ret);
                    }
                }
                self.cxt.drop();
                Ok(None)
            }
            Stmt::Expr(ref e) => {
                self.eval(e)?;
                Ok(None)
            }
            Stmt::While {
                ref cond,
                ref mut body,
                ref span,
            } => {
                while self.eval(cond)?.truthy() {
                    let ret = self.run_block(body)?;
                    if let Some(_) = ret {
                        return Ok(ret);
                    }
                }
                Ok(None)
            }
            Stmt::Assign {
                ref lhs,
                ref rhs,
                ref span,
            } => {
                println!("bevor eval");
                dbg!(lhs);
                dbg!(rhs);
                let lhs = self.eval(lhs)?;
                let rhs = self.eval(rhs)?;

                println!("after eval");
                dbg!(lhs);
                dbg!(rhs);
                todo!();
            }
            Stmt::Block(ref mut block) => Ok(self.run_block(block)?),
            Stmt::Break(_) | Stmt::Continue(_) => todo!(),
            Stmt::Ret(ref e, _) => Ok(Some(self.eval(e)?)),
        }
    }
}
