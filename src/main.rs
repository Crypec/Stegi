#![feature(box_syntax, box_patterns)]
#![allow(
    unused_imports,
    dead_code,
    unused_variables,
    unreachable_code,
    unused_must_use
)]
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

use crate::ast::Span;
use crate::errors::*;
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
                eprintln!(
                    "{}",
                    Diagnostic {
                        kind: ErrKind::Internal(
                            "Wir konnten kein Quellenverzeichnis finden!".to_string()
                        ),
                        span: Span {
                            hi: 0,
                            lo: 0,
                            file: Path::new("./Quellen").to_path_buf(),
                        },
                        suggestions: vec![
                            "Bist du in einem Stegi Projekt".to_string(),
                            "Hast du die noetigen Berechtigungen um die Projektdateien zu lesen!"
                                .to_string(),
                        ]
                    }
                );
                std::process::exit(1)
            }
            let mut files = Vec::new();

            // FIXME(Simon): This does not recursively for subfolders containing .st files
            for entry in glob("./Quellen/*.st")
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
                eprintln!(
                    "{}",
                    Diagnostic {
                        kind: ErrKind::Internal(
                            "Git Repository konnte nicht erstellt werden".to_string()
                        ),
                        span: Span {
                            hi: 0,
                            lo: 0,
                            file: Path::new(&dir).to_path_buf(),
                        },
                        suggestions: vec!["Hast du git instaliert?".to_string(),]
                    }
                );
                std::process::exit(1)
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
