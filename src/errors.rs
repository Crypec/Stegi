use std::fmt;

use crate::ast::Span;
use crate::session::SourceMap;

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

#[derive(Debug)]
pub enum Severity {
    Warning,
    Fatal,
    CodeRed, // Reserved for only the highest severity alarms, this means we fucked something up :D
}

#[derive(Debug)]
pub struct Diagnostic {
    pub desc: String,
    pub msg: String,
    pub suggestions: Vec<String>,
    pub severity: Severity,
    pub span: Span,
}

impl Diagnostic {
    pub fn new<S: Into<String>>(
        desc: S,
        msg: S,
        suggestions: Vec<S>,
        severity: Severity,
        span: Span,
    ) -> Self {
        Self {
            desc: desc.into(),
            msg: msg.into(),
            suggestions: suggestions
                .into_iter()
                .map(|s| s.into())
                .collect::<Vec<String>>(),
            span,
            severity,
        }
    }
    pub fn suggest<S: Into<String>>(self, sug: S) -> Self {
        let mut diag = self;
        diag.suggestions.push(sug.into());
        diag
    }

    pub fn add_suggestion<S: Into<String>>(&mut self, sug: S) {
        self.suggestions.push(sug.into());
    }
}

pub struct UserDiagnostic {
    pub src_map: SourceMap,
    pub desc: String,
    pub msg: String,
    pub suggestions: Vec<String>,
    pub severity: Severity,
    pub span: Span,
}

impl UserDiagnostic {
    pub fn new(diag: Diagnostic, src_map: SourceMap) -> Self {
        // TODO(Simon): there may be a better way to copy the data from Diagnostic into UserDiagnostic
        Self {
            src_map,
            desc: diag.desc,
            msg: diag.msg,
            suggestions: diag.suggestions,
            severity: diag.severity,
            span: diag.span,
        }
    }

    fn underline(&self) -> String {
        let buf_len = self.span.hi - self.span.lo;
        (0..=buf_len).map(|_| "^").collect::<String>()
    }

    fn span_snippet(&self) -> String {
        let s = self.line_span();
        let buf = &self.src_map.buf;
        buf[s.lo..s.hi].trim_start().to_string().clone()
    }

    fn line_span(&self) -> Span {
        // FIXME(Simon): I haven't tested this, but it seems like this is going to work only on linux with the current solution
        // FIXME(Simon): because windows uses not only a '\n' as a newline char but combines it with a '\r'
        let mut line_offsets = vec![0];
        line_offsets.extend(
            self.src_map
                .buf
                .char_indices()
                .filter(|(_, c)| *c == '\n')
                .map(|(i, _)| i)
                .collect::<Vec<usize>>(),
        );
        assert!(
            self.span.hi <= *line_offsets.last().unwrap(),
            "`hi` marker of span is outside of file"
        );

        let mut it = line_offsets.into_iter().peekable();
        let mut lo = 0;
        while let Some(offset) = it.next() {
            if offset == self.span.lo || *it.peek().unwrap() >= self.span.lo {
                lo = offset;
                break;
            }
        }
        let hi = it.next().unwrap();
        let (lo, _) = self
            .src_map
            .buf
            .char_indices()
            .skip(lo)
            .find(|(_, c)| !c.is_whitespace())
            .unwrap();
        Span::new(lo, hi)
    }

    fn line_num(&self) -> usize {
        self.src_map
            .buf
            .char_indices()
            .filter(|(_, c)| *c == '\n')
            .position(|(i, _)| i >= self.span.lo)
            .expect("failed to compute line number of err")
            + 1
    }

    fn write_code_snippet(&self, f: &mut fmt::Formatter, c: Color) -> fmt::Result {
        let line_str = format!(" {} |", self.line_num());

        let align = line_str.len();
        let u_line = self.underline();

        writeln!(f, "{:>a$}", "|", a = align)?;
        writeln!(f, "{} {}", line_str, self.span_snippet())?;
        writeln!(
            f,
            "{:>a$} {:>u$}",
            "|",
            u_line.color(c).bold(),
            a = align,
            u = self.span.lo - self.line_span().lo + u_line.len()
        )?;
        writeln!(
            f,
            "{:>a$} {}: {}",
            "|",
            "Hilfe".bold().underline(),
            self.msg,
            a = align
        )
    }
}

impl fmt::Display for UserDiagnostic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let color = match self.severity {
            Severity::Warning => Color::BrightYellow,
            Severity::Fatal => Color::Red,
            Severity::CodeRed => Color::BrightMagenta,
        };
        writeln!(
            f,
            "{} {} {}[{}]",
            "--".bold(),
            self.desc.color(color).bold(),
            "------------------------------------------".bold(),
            self.src_map.path.to_str().unwrap().blue()
        )?;
        writeln!(f)?;
        self.write_code_snippet(f, color)?;
        writeln!(f, "")?;
        for sug in &self.suggestions {
            writeln!(f, " • {}", sug)?;
        }
        write!(f, "")
    }
}
