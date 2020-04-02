use std::fs;
use std::io;
use std::path::PathBuf;

use crate::ast::*;
use crate::errors::*;
use crate::lexer::*;
use crate::parser::*;
use crate::typer::*;

use colored::*;

#[derive(Debug)]
pub struct SourceMap {
    pub path: PathBuf,
}

pub struct Driver {
    pub sess: Session,
}

impl Driver {
    pub fn new(files: Vec<PathBuf>) -> Self {
        Self {
            sess: Session::new(files),
        }
    }

    pub fn compile(&mut self) {
        let file_str = self
            .sess
            .files
            .get(0)
            .unwrap()
            .read_from_fs()
            .expect("failed to read file");

        let t_stream = Lexer::new(file_str)
            .collect::<Result<Vec<Token>, SyntaxError>>()
            .expect("failed to tokenize file");
        let mut ast = Parser::new(t_stream, &mut self.sess)
            .collect::<Vec<Result<Stmt, SyntaxError>>>()
            .into_iter()
            .map(|stmt| stmt.unwrap())
            .collect::<Vec<Stmt>>();
        let tyc = Typer::new().infer(&mut ast);
    }
}

impl SourceMap {
    pub fn new(path: PathBuf) -> Self {
        Self { path }
    }
    pub fn read_from_fs(&self) -> io::Result<String> {
        fs::read_to_string(&self.path)
    }

    pub fn read_span_snippet(&self, s: &Span) -> Result<String, std::io::Error> {
        Ok(fs::read_to_string(&self.path)?[s.lo..s.hi].to_string())
    }
}

pub struct Session {
    pub files: Vec<SourceMap>,
    pub had_err: bool,
    // Stores the index of the current file
    // FIXME(Simon): this seriously hinders us paralellizing the compiler
    // FIXME(Simon): this needs to be cleaned up later, but I don't know how I will be approaching this
    pub current: usize,
}
impl Session {
    pub fn new(files: Vec<PathBuf>) -> Self {
        Self {
            files: files.into_iter().map(|p| SourceMap::new(p)).collect(),
            had_err: false,
            current: 0,
        }
    }

    pub fn span_err(&mut self, desc: &'static str, msg: &'static str, span: &Span) -> Error {
        self.had_err = true;
        Error {
            desc,
            msg,
            suggestions: Vec::new(),
            span: *span,
            severity: Severity::Fatal,
            src: self
                .files
                .get(self.current)
                .expect("invalid index for src map"),
        }
    }
}
