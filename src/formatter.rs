use crate::ast::*;
use crate::lexer::Lit;
use crate::typer::{Ty, TyKind};

use std::fmt;

impl fmt::Display for Stmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Stmt::Assign { lhs, rhs, span: _ } => writeln!(f, "{} = {}", lhs, rhs),
            Stmt::Block(b) => writeln!(f, "{}", b),
            Stmt::Break(_) => writeln!(f, "stop;"),
            Stmt::Continue(_) => writeln!(f, "weiter;"),
            Stmt::Expr(e) => writeln!(f, "{};", e),
            // Stmt::FnDecl(fn_decl) => {
            //     let params = fn_decl
            //         .head
            //         .params
            //         .iter()
            //         .map(|p| format!("{}: {}", p.name, p.ty))
            //         .collect::<Vec<_>>()
            //         .join(",");
            //     let ret_ty = if !fn_decl.head.ret_ty.is_unit() {
            //         format!("-> {}", fn_decl.head.ret_ty)
            //     } else {
            //         String::new()
            //     };
            //     writeln!(
            //         f,
            //         "{} ({}) {} {}",
            //         fn_decl.head.name, params, ret_ty, fn_decl.body
            //     )
            // }
            Stmt::For {
                vardef,
                body,
                span: _,
            } => {
                writeln!(f, "{}", vardef)?;
                writeln!(f, "{}", body)
            }
            Stmt::While {
                cond,
                body,
                span: _,
            } => {
                writeln!(f, "wenn {} ", cond)?;
                writeln!(f, "{}", body)
            }
            Stmt::Ret(e, _) => writeln!(f, "{}", e),
            Stmt::VarDef(v) => writeln!(f, "{}", v),
            _ => todo!(),
        }
    }
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.node {
            ExprKind::Binary { lhs, rhs, op } => write!(f, "{} {} {}", lhs, op, rhs),
            ExprKind::Logical { lhs, rhs, op } => write!(f, "{} {} {}", lhs, op, rhs),
            ExprKind::Unary { op, rhs } => write!(f, "{}{}", op, rhs),
            ExprKind::Lit(l) => write!(f, "{}", l),
            e => write!(f, "{:#?}", e),
        }
    }
}

impl fmt::Display for BinaryOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BinaryOp::Plus => write!(f, "+"),
            BinaryOp::Minus => write!(f, "-"),
            BinaryOp::Multiply => write!(f, "*"),
            BinaryOp::Divide => write!(f, "/"),
        }
    }
}

impl fmt::Display for CmpOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CmpOp::EqEq => write!(f, "gleich"),
            CmpOp::NotEq => write!(f, "ungleich"),
            CmpOp::Greater => write!(f, ">"),
            CmpOp::GreaterEq => write!(f, ">="),
            CmpOp::Less => write!(f, ">"),
            CmpOp::LessEq => write!(f, "<="),
            CmpOp::And => write!(f, "und"),
            CmpOp::Or => write!(f, "oder"),
        }
    }
}

impl fmt::Display for UnaryOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            UnaryOp::Minus => write!(f, "-"),
            UnaryOp::Not => write!(f, "nicht"),
        }
    }
}

impl fmt::Display for Lit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Lit::Number(n) => write!(f, "{}", n),
            Lit::Bool(v) => write!(f, "{}", v),
            Lit::String(s) => write!(f, "{}", s),
        }
    }
}

impl fmt::Display for Block {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(
            f,
            "{}",
            self.stmts
                .iter()
                .map(|s| format!("{}", s))
                .collect::<Vec<_>>()
                .join("\n")
        )
    }
}

impl fmt::Display for Ident {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "{}", self.lexeme)
    }
}

impl fmt::Display for Ty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "{:#?}", self.kind)
    }
}

impl fmt::Display for VarDef {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // NOTE(Simon): we could do this a bit cleaner if we impl display for tykind or ty
        let ty = match self.ty.kind {
            TyKind::Infer => String::new(),
            _ => format!("{}", self.ty),
        };
        write!(f, "{} :{}= {}", self.pat, ty, self.init)
    }
}

impl fmt::Display for Path {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let p = self
            .segments
            .iter()
            .map(|s| s.lexeme.clone())
            .collect::<Vec<String>>()
            .join("::");
        writeln!(f, "{}", p)
    }
}
