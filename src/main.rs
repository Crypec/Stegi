#![feature(box_syntax, box_patterns)]
#![warn(clippy::pendantic)]
use glob::glob;
use std::path::*;

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

extern crate structopt;

use structopt::StructOpt;

use git2::Repository;

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

#[derive(StructOpt)]
#[structopt(
    name = "stegi",
    about = "Hallo ich bin Stegi und ich will dir helfen programmieren zu lernen!"
)]
enum Stegi {
    #[structopt(name = "start")]
    Start,
    #[structopt(name = "neu")]
    New {
        #[structopt(long = "name")]
        name: String,
    },
}

fn main() {
    println!("################################ Stegi ################################ ");
    match Stegi::from_args() {
        Stegi::Start => {
            if !Path::new("./Quellen").exists() {
                println!("Quellenordner existiert nicht!");
                panic!();
            }
            let mut files = Vec::new();
            for entry in glob("/Quellen/**/*.st")
                .expect("Ordner mit Quelltextdatein konnte nicht eingelesen werden")
            {
                match entry {
                    Ok(path) => files.push(path),
                    Err(e) => eprintln!("{}", e),
                }
            }

            let mut d = Driver::new(files);
            d.start();
        }
        Stegi::New { name } => {
            let dir = format!("./{}", name);
            if let Err(e) = Repository::init(&dir) {
                panic!("failed to init: {}", e);
            };
            let start_file = include_str!("../resources/start.st");

            std::fs::create_dir(format!("./{}/Quellen", dir))
                .expect("Quellenordner konnte nicht angelegt werden!");

            std::fs::write(format!("{}/Quellen/start.st", dir), start_file)
                .expect("Schreiben der 'start' Datei fehlgeschlagen!");
            println!("Neues Projekt {} angelegt!", name);
            println!("{}", STEGI_ASCII);
        }
    }
}
