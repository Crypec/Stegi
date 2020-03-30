#![allow(dead_code)]

use std::fs;

mod ast;
mod errors;
mod lexer;
mod parser;

#[macro_use]
extern crate failure;

#[macro_use]
extern crate derivative;

use self::ast::*;
use self::errors::*;
use self::lexer::*;
use self::parser::*;

fn main() {
    let prog = fs::read_to_string("./examples/test.st").expect("failed to read file");

    println!("Hello from the new stegi compiler");
    let res = Lexer::new(&prog).collect::<Result<Vec<Token>, SyntaxError>>();

    let tokens = match res {
        Err(e) => {
            println!("Fehler beim Kompilieren");
            eprintln!("{}", e);
            std::process::exit(1);
        }
        Ok(t) => t,
    };

    let asd = Parser::new(tokens).collect::<Result<Vec<Stmt>, SyntaxError>>();
    println!("{:#?}", asd);
}
