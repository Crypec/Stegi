#![allow(dead_code)]

use std::path::PathBuf;

mod ast;
mod errors;
mod lexer;
mod parser;
mod session;
mod typer;

#[macro_use]
extern crate failure;

#[macro_use]
extern crate derivative;

use self::session::*;

fn main() {
    println!("Hello from the new stegi compiler");
    //let mut path = std::env::current_dir().expect("failed to get working dir");
    //path.push("examples/test.st");
    let path = PathBuf::from("examples/test.st");
    let mut d = Driver::new(vec![path]);
    d.compile();
}
