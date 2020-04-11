use std::fmt;
use std::rc::Weak;

use crate::ast::Span;
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
    CodeRed, // Reserved for only the highest severity alarms, this means we fucked something up :D
}

// TODO(Simon): do some better error handling with the weak ref to parent session
pub struct Diagnostic {
    pub desc: String,
    pub msg: String,
    pub suggestions: Vec<String>,
    pub severity: Severity,
    pub span: Span,
    pub src: Weak<SourceMap>,
}

impl Diagnostic {
    pub fn new<S: Into<String>>(
        desc: S,
        msg: S,
        suggestions: Vec<S>,
        severity: Severity,
        span: Span,
        src: Weak<SourceMap>,
    ) -> Self {
        Self {
            desc: desc.into(),
            msg: msg.into(),
            suggestions: suggestions
                .into_iter()
                .map(|s| s.into())
                .collect::<Vec<String>>(),
            severity,
            span: span.clone(),
            src,
        }
    }

    pub fn emit(&self) {
        println!("{}", self);
    }

    fn line_num(&self) -> usize {
        self.src
            .upgrade()
            .unwrap()
            .buf
            .chars()
            .filter(|c| *c == '\n')
            .count()
    }

    fn underline(&self) -> String {
        let line_span = self.line_span();
        let buf_len = line_span.hi - self.span.lo;
        (1..buf_len).map(|_| "^").collect::<String>()
    }

    fn span_snippet(&self) -> String {
        let s = self.line_span();
        self.src.upgrade().unwrap().buf[s.lo..s.hi]
            .trim_start()
            .to_string()
    }

    fn line_span(&self) -> Span {
        // FIXME(Simon): I haven't tested this, but it seems like this is going to work only on linux with the current solution
        // FIXME(Simon): because windows uses not only a '\n' as a newline char but combines it with a '\r'
        let mut line_offsets = vec![0];
        line_offsets.extend(
            &self
                .src
                .upgrade()
                .unwrap()
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
        // we add 1 to the low marker of the line span to skip the `\n = newline` char
        Span::new(lo + 1, hi)
    }
}

impl fmt::Display for Diagnostic {
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
            self.src.upgrade().unwrap().path.to_str().unwrap().blue()
        )?;
        writeln!(f)?;
        let line = self.line_num().to_string();
        let front_pad = line.chars().count() + 2;
        let bar = "|".bold();
        writeln!(f, "{:>pad$}", bar, pad = front_pad)?;
        writeln!(
            f,
            "{:^pad$}{} {}",
            line.bold(),
            bar,
            self.span_snippet(),
            pad = front_pad - 1
        )?;
        let highlight = format!(
            "{:pad$}{}",
            " ",
            self.underline().color(color).bold(),
            pad = self.span.lo - self.line_span().lo,
        );
        writeln!(f, "{:>pad$}{}", bar, highlight, pad = front_pad)?;
        writeln!(
            f,
            "{:>pad$} {} {}",
            bar,
            "Hilfe:".underline().bold(),
            self.msg,
            pad = front_pad
        )?;
        write!(f, "")
    }
}
