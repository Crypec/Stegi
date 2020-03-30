use std::collections::HashMap;

use crate::ast::*;


type VarId = usize;

type Scheme = HashMap<String, Ty>;

pub fn infer(e: Expr) -> Ty {
	todo!()
}
