#![warn(clippy::pendantic)]
use std::path::PathBuf;

#[macro_use]
mod ast;

mod errors;
mod lexer;
mod parser;
mod session;
mod typer;

#[macro_use]
extern crate failure;

use self::session::*;

fn main() {
    println!("Hello from the new stegi compiler");
    //let mut path = std::env::current_dir().expect("failed to get working dir");
    //path.push("examples/test.st");
    let path = PathBuf::from("examples/test.st");
    let mut d = Driver::new(vec![path]);
    d.compile();
}
