#![feature(box_syntax, box_patterns)]
#![warn(clippy::pendantic)]
#![allow(unused_imports)]
#![allow(unused_variables)]
#![allow(dead_code)]
use std::path::PathBuf;

#[macro_use]
mod ast;

mod cli;
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

use clap::*;

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

    // let matches = App::new("Stegi Kompiler")
    //     .version("0.1")
    //     .author("Torben Groetzinger, Simon Kunz, Leonie Zumsteg")
    //     .about("Hier koennte ihre Werbung stehen")
    //     .arg(
    //         Arg::new("neu")
    //             .short('n')
    //             .long("neue")
    //             .value_name("NAME")
    //             .about("Erstellt ein neues Stegi Projekt")
    //             .takes_value(true),
    //     )
    //     .arg(
    //         Arg::new("start")
    //             .short('s')
    //             .long("starte")
    //             .about("Startet das aktuelle Stegi Projekt"),
    //     )
    //     .get_matches();
    let path = PathBuf::from("examples/test.st");
    let mut d = Driver::new(vec![path]);
    d.compile();
}
