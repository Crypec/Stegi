use std::path::PathBuf;

use crate::typer::*;

use crate::ast::*;
use crate::errors::*;
use crate::interp::*;
use crate::lexer::*;
use crate::lowering::*;
use crate::parser::*;

#[derive(Debug, Clone)]
pub struct SourceMap {
    pub path: PathBuf,
    pub buf: String,
}

pub struct Driver {
    pub files: Vec<SourceMap>,
    pub diagnostics: Vec<Diagnostic>,
    // Stores the index of the current file
    // FIXME(Simon): this seriously hinders us paralellizing the compiler
    // FIXME(Simon): this needs to be cleaned up later, but I don't know how I will be approaching this
}

impl Driver {
    pub fn new(files: Vec<PathBuf>) -> Self {
        Self {
            files: files.into_iter().map(|f| SourceMap::new(f)).collect(),
            diagnostics: Vec::new(),
        }
    }

    pub fn start(&mut self) {
        let mut ast: Vec<Decl> = AST::new();
        dbg!(&self.files);
        for file in &self.files {
            let lex_result = Lexer::new(&file.buf, file.path.clone())
                .collect::<Result<Vec<Token>, Diagnostic>>();
            let t_stream = match lex_result {
                Ok(t_stream) => t_stream,
                Err(e) => {
                    self.diagnostics.push(e);
                    Vec::new()
                }
            };
            let t_stream = infer_semis(t_stream);

            let parse_result =
                Parser::new(t_stream, &file.path).collect::<Vec<Result<Decl, Diagnostic>>>();
            let (nodes, errors): (Vec<_>, Vec<_>) =
                parse_result.into_iter().partition(Result::is_ok);
            let file_ast: Vec<_> = nodes.into_iter().map(Result::unwrap).collect();
            ast.extend(file_ast);

            self.diagnostics.extend(
                errors
                    .into_iter()
                    .map(Result::unwrap_err)
                    .collect::<Vec<Diagnostic>>(),
            );
            dbg!(&self.diagnostics);
        }
        dbg!(&ast);
        ImplReoderPass::new().reorder(&mut ast);
        self.diagnostics.extend(Typer::new().infer(&mut ast));
        if self.had_err() {
            eprintln!("Fehler beim Kompilieren gefunden. Programm wird nicht ausgefuehrt! :c\n");
            for err in &self.diagnostics {
                eprintln!("{}", err);
            }
            std::process::exit(1);
        }
        Interp::new().interp(&mut ast);
    }

    pub fn had_err(&self) -> bool {
        self.diagnostics.iter().any(|d| match d.kind {
            ErrKind::Runtime(_) | ErrKind::Syntax(_) | ErrKind::Type(_) | ErrKind::Internal(_) => {
                true
            }
            ErrKind::Warning { .. } => false,
        })
    }
}

impl SourceMap {
    pub fn new(path: PathBuf) -> Self {
        let buf = std::fs::read_to_string(&path).expect("Datei konnte nicht gelesen werden");
        Self { path, buf }
    }
}
