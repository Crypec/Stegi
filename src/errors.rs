use std::fmt;
use std::fs;

use crate::ast::Span;
use crate::lexer::*;
use crate::session::*;

use colored::*;

#[derive(Debug, Fail)]
pub enum SyntaxError {
    #[fail(
        display = "Syntaxfehler: Unerwarteter Buchstabe '{}' in Zeile: {}",
        _0, _1
    )]
    UnexpectedChar(char, usize),

    #[fail(display = "Syntaxfehler: Textliteral nicht geschlosssen '{}'", _0)]
    UnterminatedString(usize),

    #[fail(display = "SyntaxFehler: Unerwartetes Dateiende")]
    UnexpectedEOF,

    #[fail(
        display = "SyntaxFehler: Nach {} haben wir eigentlich {} erwartet",
        _0, _1
    )]
    Missing(String, &'static str),

    #[fail(
        display = "SyntaxFehler: Du scheinst den 'Stop' Befehl ausserhalb einer Schleife benutzt zu haben"
    )]
    BreakOutsideLoop,
}

pub enum TypeError {
    InvalidType,
    VarNameNotFound,
}

pub enum Severity {
    Warning,
    Fatal,
}

pub struct Error<'a> {
    pub msg: &'static str,
    pub desc: &'static str,
    pub suggestions: Vec<String>,
    pub severity: Severity,
    pub span: Span,
    pub src: &'a SourceMap,
}

impl Error<'_> {
    fn line_number(&self) -> usize {
        // FIXME(Simon): I haven't tested this, but it seems like this is going to work only on linux with the current solution
        // FIXME(Simon): because windows uses not only a '\n' as a newline char but combines it with a '\r'
        fs::read_to_string(&self.src.path)
            .expect("failed to read file")
            .chars()
            .take(self.span.lo)
            .filter(|c| *c == '\n')
            .count()
    }

    fn line_span(&self) -> Span {
        let src = fs::read_to_string(&self.src.path).unwrap();
        let (lo, _) = src
            .char_indices()
            .filter(|(_, c)| *c == '\n')
            .nth(self.line_number() - 1)
            .unwrap();
        let (hi, _) = src
            .char_indices()
            .skip(lo + 1)
            .find(|(_, c)| *c == '\n')
            .unwrap();
        let res = Span::new(lo, hi);
        res
    }

    fn fmt_src_line(&self) -> String {
        format!(
            "|{} {}\n|   {}",
            self.line_number(),
            self.get_src_line(),
            self.underline()
        )
    }

    fn underline(&self) -> String {
        let line_span = self.line_span();
        let file = fs::read_to_string(&self.src.path).unwrap();
        let buf_len = self.span.lo - line_span.lo - 1;
        let buf = (0..buf_len).map(|_| " ").collect::<String>();
        let under = (0..self.span.hi - self.span.lo + 1)
            .map(|_| "^".red().bold().to_string())
            .collect::<String>();
        format!("{}{}", buf, under)
    }

    fn get_src_line(&self) -> String {
        let line = self.line_span();
        fs::read_to_string(&self.src.path).unwrap()[line.lo..line.hi]
            .trim_start_matches("\n")
            .to_owned()
    }

    pub fn suggest(&mut self, sug: &str) {
        self.suggestions.push(sug.to_owned());
    }
}

impl fmt::Display for Error<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let header = format!(
            "-- {} --------------------------------------- [{}:{}:{}]",
            self.desc.red().bold(),
            self.src.path.to_str().unwrap(),
            self.line_number(),
            self.span.lo,
        );
        writeln!(f, "{}", header.bright_blue());
        writeln!(f, "");
        writeln!(f, "{}", self.msg);
        writeln!(f, "");
        writeln!(f, "|");
        writeln!(f, "{}", self.fmt_src_line());
        writeln!(f, "|");
        if !self.suggestions.is_empty() {
            write!(f, "{}", "Hilfe:".yellow().bold().underline());
            for sug in self.suggestions.iter() {
                write!(f, " = {}", sug);
            }
        }
        writeln!(f)
    }
}
