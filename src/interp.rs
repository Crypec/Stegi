use crate::ast::*;

use std::cell::RefCell;
use std::convert::From;
use std::fmt;

use dyn_fmt::*;

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
                let pat = stringify!($p);
                panic!("Invalide Umwandlung, {:?} entspricht nicht folgendem Muster: {:#?} dies ist wahrscheinlich ein Fehler im Typenchecker!", $val, pat);
            }
        }
    }
);

type Object = (Ident, HashMap<String, Value>);

#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    Num(f64),
    Text(String),
    Bool(bool),
    Object(Object),
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
            Value::Object((path, obj)) => write!(f, "{}:{:#?}", path, obj),
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
        self.cxt.push_scope();
        for stmt in block.stmts.iter_mut() {
            let ret = stmt.accept(self)?;
            if let Some(_) = ret {
                self.cxt.pop_scope();
                return Ok(ret);
            }
        }
        self.cxt.pop_scope();
        Ok(None)
    }

    fn call_fn(&mut self, callee: &mut Expr, args: &Vec<Expr>) -> Result<Value, Diagnostic> {
        let mut args = args.clone();
        if let ExprKind::Field(..) = callee.node {
            args.push(callee.clone());
        }

        let callee = self.eval(callee)?;
        let mut fun = cast!(callee, Value::Fn);
        let mut params = fun.header.params;
        debug_assert_eq!(args.len(), params.len());

        // FIXME(Simon): this needs to be a call to make_clean()!!!
        self.cxt.push_scope();

        for (p, a) in params.iter_mut().zip(args.iter()) {
            let name = p.name.lexeme.clone();
            let arg = self.eval(&a)?;
            self.cxt.insert(name, arg);
        }
        let ret = self.run_block(&mut fun.body)?;
        self.cxt.pop_scope();
        match ret {
            Some(val) => Ok(val),
            None => Ok(Value::Tup(Vec::new())),
        }
    }

    fn fill_fn_table(&mut self, ast: &mut AST) {
        for decl in ast {
            if let Decl::Fn(f) = decl {
                let name = f.header.name.lexeme.clone();
                self.cxt.insert_global(name, Value::Fn(f.clone()));
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
                    self.run_block(&mut f.body).unwrap();
                }
                // if !found_main {
                //     self.span
                // }
            }
        }
    }

    fn assign(&mut self, target: &AssingKind, to: Value) -> Result<(), Diagnostic> {
        let from = self
            .cxt
            .get(&target.base_var().lexeme)
            .expect("Variable nicht definiert! Das ist vermutlich ein Fehler im Typenchecker!");
        let ptr = self.assign_match(target)?;
        *ptr = to;
        Ok(())
    }

    fn assign_match(&mut self, target: &AssingKind) -> Result<&mut Value, Diagnostic> {
        match target {
            AssingKind::Var(var) => Ok(self.cxt.get_mut(&var.lexeme).expect(
                "Variable nicht gefunden! Vermutlich ein Fehler waehrend der Typenanalyse!",
            )),
            AssingKind::Field { callee, name } => {
                if let Value::Object((_, obj)) = self.assign_match(callee)? {
                    Ok(obj.get_mut(&name.lexeme).expect(
                        "Feld in Objekt nicht gefunden! Vermutlich ein Fehler in der Typenanalyse!",
                    ))
                } else {
                    Err(Diagnostic {
						kind: ErrKind::Internal("Feld in Object nicht gefunden! Dieser Fehler haette eigentlich waehrend der Typenanalyse erkannt werden sollen!".to_string()),
						span: name.span,
						suggestions: Vec::new(),
					})
                }
            }
            AssingKind::Index { callee, index } => {
                let idx = cast!(self.eval(&index)?, Value::Num) as isize;
                if let Value::Array(arr) = self.assign_match(callee)? {
                    let err = Diagnostic {
                        kind: ErrKind::Runtime(RuntimeError::OutOfBounds {
                            index: idx,
                            len: arr.len(),
                        }),
                        span: index.span,
                        suggestions: Vec::new(),
                    };
                    arr.get_mut(idx as usize).ok_or(err)
                } else {
                    Err(Diagnostic {
						kind: ErrKind::Internal("Objekt ist kein Array. Dieser Fehler sollte eigentlich waehrend der Typenanalyse erkannt werden!".to_string()),
						span: index.span,
						suggestions: Vec::new(),
					})
                }
            }
        }
    }

    fn eval(&mut self, e: &Expr) -> Result<Value, Diagnostic> {
        match e.node {
            ExprKind::Binary {
                ref lhs,
                ref op,
                ref rhs,
            } => {
                let lhs = cast!(self.eval(lhs)?, Value::Num);
                let rhs = cast!(self.eval(rhs)?, Value::Num);
                let res = match op {
                    BinaryOp::Plus => lhs + rhs,
                    BinaryOp::Minus => lhs - rhs,
                    BinaryOp::Multiply => lhs * rhs,
                    BinaryOp::Divide => lhs / rhs, // TODO(Simon): propper error reporting
                };
                Ok(Value::Num(res))
            }
            ExprKind::Logical {
                ref lhs,
                ref op,
                ref rhs,
            } => {
                if *op == CmpOp::EqEq {
                    return Ok(Value::Bool(self.eval(lhs)? == self.eval(rhs)?));
                } else if *op == CmpOp::NotEq {
                    return Ok(Value::Bool(self.eval(lhs)? != self.eval(rhs)?));
                };
                let lhs = cast!(self.eval(lhs)?, Value::Bool);
                let rhs = cast!(self.eval(rhs)?, Value::Bool);
                let res = match op {
                    CmpOp::And => lhs && rhs,
                    CmpOp::Or => lhs || rhs,
                    CmpOp::GreaterEq => lhs >= rhs,
                    CmpOp::Greater => lhs > rhs,
                    CmpOp::Less => lhs < rhs,
                    CmpOp::LessEq => lhs <= rhs,
                    _ => unreachable!("Covered by the if beforehand!"),
                };
                Ok(Value::Bool(res))
            }
            ExprKind::Unary { ref rhs, ref op } => match op {
                UnaryOp::Minus => {
                    let rhs = cast!(self.eval(&rhs)?, Value::Num);
                    Ok(Value::Num(-rhs))
                }
                UnaryOp::Not => {
                    let rhs = cast!(self.eval(&rhs)?, Value::Bool);
                    Ok(Value::Bool(!rhs))
                }
            },
            ExprKind::Range(ref from, ref to) => {
                let from = cast!(self.eval(from)?, Value::Num) as isize;
                let to = cast!(self.eval(to)?, Value::Num) as isize;
                let arr = (from..to).map(|e| Value::Num(e as f64)).collect();
                Ok(Value::Array(arr))
            }
            ExprKind::Tup(ref elems) => {
                let mut t = Vec::new();
                for elem in elems {
                    t.push(self.eval(&elem)?);
                }
                Ok(Value::Tup(t))
            }
            ExprKind::Index {
                ref callee,
                ref index,
            } => {
                let arr = cast!(self.eval(callee)?, Value::Array);
                let idx = cast!(self.eval(index)?, Value::Num) as isize;
                match arr.get(idx as usize) {
                    Some(val) => Ok(val.clone()),
                    None => {
                        let kind = ErrKind::Runtime(RuntimeError::OutOfBounds {
                            len: arr.len(),
                            index: idx,
                        });
                        return Err(Diagnostic{
							kind,
							span: e.span,
							suggestions: vec!["Du kannst versuchen mit einer extra Abfrage den Wert des index zu ueberpruefen!".to_string()],
						});
                    }
                }
            }
            ExprKind::Lit(ref lit) => match lit {
                Lit::Bool(b) => Ok(Value::Bool(*b)),
                Lit::Number(n) => Ok(Value::Num(*n)),
                Lit::String(t) => Ok(Value::Text(t.clone())),
            },
            ExprKind::Struct {
                ref name,
                ref members,
            } => {
                let mut obj = HashMap::new();
                for m in members {
                    obj.insert(m.name.lexeme.clone(), self.eval(&m.init)?);
                }
                Ok(Value::Object((name.clone(), obj)))
            }
            ExprKind::Field(ref callee, ref name) => {
                let (_, obj) = cast!(self.eval(&callee)?, Value::Object);
                Ok(obj.get(&name.lexeme).expect("Field not found!").clone())
            }
            ExprKind::Path(ref p) => Ok(self.cxt.get(&p.first().unwrap().lexeme).unwrap().clone()),
            ExprKind::Array(ref elems) => {
                let mut array = Vec::new();
                for e in elems {
                    array.push(self.eval(&e)?);
                }
                Ok(Value::Array(array))
            }
            ExprKind::Call {
                ref callee,
                ref args,
            } => {
                let mut fun = cast!(self.eval(callee)?, Value::Fn);
                let mut args_eval = Vec::new();
                for arg in args {
                    args_eval.push(self.eval(&arg)?);
                }
                debug_assert_eq!(fun.header.params.len(), args_eval.len());
                self.cxt.push_frame();
                for (p, arg) in fun.header.params.iter().zip(args_eval.iter()) {
                    self.cxt.insert(p.name.lexeme.clone(), arg.clone())
                }
                let ret = match self.run_block(&mut fun.body)? {
                    Some(ret_val) => Ok(ret_val),
                    None => Ok(Value::Tup(Vec::new())),
                };
                self.cxt.pop_frame();
                ret
            }
            ExprKind::Intrinsic { ref kind, ref args } => match kind {
                Intrinsic::Print => {
                    let mut args_eval = Vec::new();
                    let fmt_spec = cast!(self.eval(&args.first().unwrap())?, Value::Text);
                    for arg in args.iter().skip(1) {
                        args_eval.push(self.eval(arg)?);
                    }
                    println!("{}", Arguments::new(&fmt_spec, args_eval.iter()));
                    Ok(Value::Tup(Vec::new()))
                }
                Intrinsic::Format => {
                    let mut args_eval = Vec::new();
                    let fmt_spec = cast!(self.eval(&args.first().unwrap())?, Value::Text);
                    for arg in args.iter().skip(1) {
                        args_eval.push(self.eval(arg)?);
                    }
                    Ok(Value::Text(format!(
                        "{}",
                        Arguments::new(&fmt_spec, args_eval.iter())
                    )))
                }
                _ => todo!(),
            },
            ExprKind::Var(ref var) | ExprKind::This(ref var) => {
                Ok(self.cxt.get(&var.lexeme).unwrap().clone())
            }
        }
    }
}

impl<'a> Visitor for Interp {
    type Result = Result<Option<Value>, Diagnostic>;

    fn visit_decl(&mut self, d: &mut Decl) -> Self::Result {
        todo!()
    }

    fn visit_expr(&mut self, e: &mut Expr) -> Self::Result {
        todo!()
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
                self.cxt.push_scope();
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
                        self.cxt.pop_scope();
                        return Ok(ret);
                    }
                }
                self.cxt.pop_scope();
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
                ref target,
                ref rhs,
                ref span,
            } => {
                let rhs = self.eval(rhs)?;
                self.assign(&target.kind, rhs)?;
                Ok(None)
            }
            Stmt::Block(ref mut block) => Ok(self.run_block(block)?),
            Stmt::Break(_) | Stmt::Continue(_) => todo!(),
            Stmt::Ret(ref e, _) => Ok(Some(self.eval(e)?)),
        }
    }
}
