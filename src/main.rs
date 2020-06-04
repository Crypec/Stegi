#![feature(box_syntax, box_patterns)]
#![warn(clippy::pendantic)]
#![allow(unused_imports)]
#![allow(unused_variables)]
#![allow(dead_code)]
use std::path::PathBuf;

#[macro_use]
mod ast;

mod cxt;
mod errors;
mod formatter;
mod interp;
mod lexer;
mod lowering;
mod parser;
mod session;
mod typer;

#[macro_use]
extern crate failure;

use self::session::*;

const STEGI_ASCII: &str = r#"
 _________________________________________
/ Fehler im Code zu suchen ist doppelt so \
| schwer, wie ihn zu schreiben. Wenn sie  |
| Code so raffiniert wie moeglich         |
| schreiben, sind Sie also per defintion  |
| nicht intelligent genug, um ihn zu      |
\ debuggen. - Brian W. Kernighan          /
 -----------------------------------------
\                             .       .
 \                           / `.   .' "
  \                  .---.  <    > <    >  .---.
   \                 |    \  \ - ~ ~ - /  /    |
         _____          ..-~             ~-..-~
        |     |   \~~~\.'                    `./~~~/
       ---------   \__/                        \__/
      .'  O    \     /               /       \  "
     (_____,    `._.'               |         }  \/~~~/
      `----.          /       }     |        /    \__/
            `-.      |       /      |       /      `. ,~~|
                ~-.__|      /_ - ~ ^|      /- _      `..-'
                     |     /        |     /     ~-.     `-. _  _  _
                     |_____|        |_____|         ~ - . _ _ _ _
"#;

fn main() {
    println!("################################ Stegi ################################ ");
    //println!("{}", STEGI_ASCII);

    //let mut path = std::env::current_dir().expect("failed to get working dir");
    //path.push("examples/test.st");
    let path = PathBuf::from("examples/test.st");
    let mut d = Driver::new(vec![path]);
    d.compile();
}
