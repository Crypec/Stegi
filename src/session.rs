use std::fs;
use std::path::PathBuf;
use std::time::Instant;

use crate::typer::*;

use crate::ast::*;
use crate::errors::*;
use crate::lexer::*;
use crate::parser::*;

#[derive(Debug, Clone)]
pub struct SourceMap {
    pub path: PathBuf,
    pub buf: String,
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
        let current_src_map = self.sess.files.get(self.sess.current).unwrap();
        let now = Instant::now();
        let buf = &self.sess.files.first().unwrap().buf;
        let t_stream = Lexer::new(&buf)
            .collect::<Result<Vec<Token>, SyntaxError>>()
            .expect("failed to tokenize file");
        let t_stream = infer_semis(t_stream);
        let ast = Parser::new(t_stream).collect::<Vec<Result<Stmt, Diagnostic>>>();
        println!("{:#?}", now.elapsed());
        let (ast, errors): (Vec<_>, Vec<_>) = ast.into_iter().partition(Result::is_ok);
        let mut ast: Vec<_> = ast.into_iter().map(Result::unwrap).collect();
        // FIXME(Simon): these should be converted into UserDiagnostics
        errors
            .into_iter()
            .map(Result::unwrap_err)
            .map(|diag| UserDiagnostic::new(diag, current_src_map.clone()))
            .for_each(|diag| println!("{}", diag));
        TypeInferencePass::new().infer(&mut ast);
        dbg!(&ast);
        let had_err = self.sess.diagnostics.iter().any(|d| match d.severity {
            Severity::Fatal | Severity::CodeRed => true,
            Severity::Warning => false,
        });
        if had_err {
            eprintln!("Fehler beim Kompilieren gefunden. Programm wird nicht ausgefuehrt! :c\n");
        }

        //     self.sess
        //         .borrow()
        //         .diagnostics
        //         .iter()
        //         .for_each(|d| eprintln!("{}", d))
        // }
    }
}

impl SourceMap {
    pub fn new(path: PathBuf) -> Self {
        let buf = std::fs::read_to_string(&path).expect("failed to read file");
        Self { path, buf }
    }

    pub fn read_span_snippet(&self, s: &Span) -> Result<String, std::io::Error> {
        Ok(fs::read_to_string(&self.path)?[s.lo..s.hi].to_string())
    }

    pub fn get_line_num(&self, sp: &Span) -> usize {
        self.buf
            .char_indices()
            .filter(|(_, c)| *c == '\n')
            .position(|(i, _)| i >= sp.lo)
            .expect("failed to compute line number of err")
            + 1
    }
}

pub struct Session {
    pub files: Vec<SourceMap>,
    pub diagnostics: Vec<Diagnostic>,
    // Stores the index of the current file
    // FIXME(Simon): this seriously hinders us paralellizing the compiler
    // FIXME(Simon): this needs to be cleaned up later, but I don't know how I will be approaching this
    pub current: usize,
}
impl Session {
    pub fn new(files: Vec<PathBuf>) -> Self {
        Self {
            files: files.into_iter().map(SourceMap::new).collect(),
            current: 0,
            diagnostics: Vec::new(),
        }
    }

    // pub fn span_err<S: Into<String>>(&self, desc: S, msg: S, span: &Span) -> Diagnostic {
    //     Diagnostic {
    //         desc: desc.into(),
    //         msg: msg.into(),
    //         suggestions: Vec::new(),
    //         span: span.clone(),
    //         severity: Severity::Fatal,
    //         src_map: self.clone(),
    //     }
    // }

    pub fn sess_register(&mut self, diag: Diagnostic) {
        self.diagnostics.push(diag);
    }

    // pub fn span_warn<S: Into<String>>(&self, desc: S, msg: S, span: &Span) -> Diagnostic {
    //     Diagnostic {
    //         desc: desc.into(),
    //         msg: msg.into(),
    //         suggestions: Vec::new(),
    //         span: span.clone(),
    //         severity: Severity::Warning,
    //         src_map: self.src_map.clone(),
    //     }
    // }
}
