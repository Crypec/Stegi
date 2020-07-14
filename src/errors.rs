use std::fmt;
use std::io;

use crate::ast::Span;
use crate::lexer::TokenKind;
use crate::typer::{Ty, TyKind};

use colored::*;

#[derive(Debug, Clone)]
pub enum ErrKind {
    Syntax(SyntaxErr),
    Type(TypeErr),
    Runtime(RuntimeError),
    Warning { desc: String, msg: String },
    Internal(String), // CodeRed this means we fucked something up, should never happen :D
}

impl fmt::Display for ErrKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ErrKind::Syntax(s_err) => write!(f, "{}", s_err),
            ErrKind::Type(t_err) => write!(f, "{}", t_err),
            ErrKind::Runtime(r_err) => write!(f, "{}", r_err),
            ErrKind::Warning { desc, msg } => write!(f, "{} \n{}", desc, msg),
            ErrKind::Internal(i_err) => write!(f, "{}", i_err),
        }
    }
}

#[derive(Debug, Clone)]
pub enum SyntaxErr {
    // lexer
    UnexpectedChar(char),
    UnterminatedString,

    SelfOutsideImpl,

    // parser
    MissingToken {
        expected: Vec<TokenKind>,
        actual: TokenKind,
    },

    ExpectedTy,

    ExpectedExpr,

    InvalidAssignmentTarget,
    InvalidVarDefTarget,

    UnbalancedParen,
    BreakOutsideLoop,
    UnexpectedEOF,
}

impl fmt::Display for SyntaxErr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SyntaxErr::UnexpectedChar(c) => write!(f, "Wir denken das Zeichen : ´{}´ gehört dort nicht hin.", c),
            SyntaxErr::UnterminatedString => write!(f, "Wir denken du hast vergessen einen Text zu schließen."),
            SyntaxErr::SelfOutsideImpl => write!(f, "Du hast vergessen die Methode in einen Implementierungsblock zu schreiben. Versuche die Funktion in einen Implementierungsblock zu schreiben."),
            SyntaxErr::MissingToken{expected, actual} => write!(f, "Wir haben hier eher ´{}´ erwartet, als {}. Versuche doch {} durch {} zu ersetzen.", fmt_tk_vec(expected), actual, actual, fmt_tk_vec(expected)),
            SyntaxErr::ExpectedTy => write!(f, "An dieser Stelle haben wir einen Datentypen erwartet!"),
            SyntaxErr::ExpectedExpr => write!(f, "An dieser Stelle haben wir einen mathematischen Ausdurck erwartet!"),
            SyntaxErr::InvalidAssignmentTarget => write!(f, "Der folgende Ausdruck ist nicht als Zuweisungsziel erlaubt."),
            SyntaxErr::InvalidVarDefTarget => write!(f, "Wir denken du hast hier ein falsches Zuweisungsziel ausgewählt. Der Zuweisungsoperator ´:=´ erlaubt dir Variablen zu definieren um in diesen einen Wert zu speichern."),
            SyntaxErr::UnbalancedParen => write!(f,"Schau bitte ob du irgendwo Klammern vergessen oder zu viel gesetzt hast. Wir aben hier eine Ungleicheit zwischen offenen und geschlossenen Klammern festgestellt."),
            SyntaxErr::BreakOutsideLoop => write!(f, "Wir denken wir haben ein `break` aushalb einer schleife entdeckt. Schau bitte, dass break nur in einer Schleife vorkommt."),
            SyntaxErr::UnexpectedEOF => write!(f, "Wir haben unerwartet das Ende der Datei erreicht! Schau bitte, dass du dein Code vollständig schreibst und richtig abschließt!")
        } //Torben
    }
}

fn fmt_tk_vec(tks: &Vec<TokenKind>) -> String {
    let arr = tks
        .iter()
        .map(|t| format!("{}", t))
        .collect::<Vec<String>>()
        .join(",");
    format!("[{}]", arr)
}

#[derive(Debug, Clone)]
pub enum TypeErr {
    VarNotFound(String),
    TyNotFound(String),
    InvalidType { expected: TyKind, actual: Ty },
    // TODO(Simon): this should really be a ty instead of just a tykind, we need the span to do proper error reporting
    InfRec(Ty, Ty),
    DuplicateLitField(String),
    MissingField(String),
    InvalidField(String, String),
    FieldNotFound { ty: TyKind, field: String },
    GenericsMismatch(Ty, Ty),
    NonStaticCall { ty_name: String, fn_name: String },
    StaticFnNotFound { ty_name: String, fn_name: String },
    Parity { expected: usize, actual: usize },
}

impl fmt::Display for TypeErr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self{
            TypeErr:: VarNotFound(varname) => write!(f, "Diese Variable `{}` haben wir nicht gefunden. Bitte Definiere und Initialisiere sie, bevor du sie benutzt.", varname),
            TypeErr::InvalidType{expected, actual}=> write!(f, "Unerwarteter Typ '{}' gefunden erwartet haben wir '{}'!", actual.kind, expected),
            TypeErr::InfRec(a, b) => write!(f, "Unendlich rekursiver Typ entdeckt! Typ: {}, kommt in {} vor!!!", a, b),
            TypeErr::FieldNotFound{ty, field} => write!(f, "Der Datentyp {} hat kein Feld mit dem Namen '{}'!", ty, field),
			TypeErr::TyNotFound(t) => write!(f, "Keine Defintion fuer den Datentyp {} gefunden", t),
			TypeErr::DuplicateLitField(field) => write!(f, "Jedes Feld eines Objektes kann nur einmal vorkommen, '{}' kommt dabei allerdings mehr als einmal vor!", field),
			TypeErr::MissingField(field) => write!(f, "Du hast vergessen dem Feld {} einen Wert zu geben!", field),
			TypeErr::InvalidField(ty, field) => write!(f, "Der Datentyp: {} hat kein Feld mit dem Namen: '{}'!", ty, field),
			TypeErr::GenericsMismatch(lhs, rhs) => write!(f, "An dieser Stelle haben wir {} erwartet, aber {} gefunden!", lhs, rhs),
			TypeErr::NonStaticCall{ty_name, fn_name} => write!(f, "Die Funktion: {} des Datentypen {}, ist nicht statisch! Der 'selbst' Paramter ist fuer statische Funktionen nicht erlaubt!", fn_name, ty_name),
			TypeErr::StaticFnNotFound{ty_name, fn_name} => write!(f, "Der Datentyp {} hat keine statische Funktion mit dem Namen {}!", ty_name, fn_name),
			TypeErr::Parity{expected, actual} => write!(f, "Die Anzahl der Argumente im Aufruf der Funktion stimmt nicht mit der in der Definition angegebenden ueberein. Erwartet: {} => Gefunden: {}", expected, actual),

        } //torben
    }
}

#[derive(Debug, Clone)]
pub enum RuntimeError {
    OutOfBounds { index: isize, len: usize },
    FileNotFound(String),
    CantWriteFile(String),
}
impl fmt::Display for RuntimeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self{
            Self::OutOfBounds{index, len} => write!(f, "Du hast versucht auf einen Index außerhalb des Feldes zuzugreifen, die Länge des Feldes beträgt {}. Du hast versucht auf die Postition {} zuzugreifen!", len, index),
				Self::FileNotFound(path) => write!(f, "Die Datei an der Stelle: {}, konnten wir nicht von der lesen!", path),
			Self::CantWriteFile(path) => write!(f, "Die Datei an der Stelle: {}, konnten wir nicht auf schreiben!", path),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Diagnostic {
    pub kind: ErrKind,
    pub suggestions: Vec<String>,
    pub span: Span,
}

impl Diagnostic {
    pub fn new(kind: ErrKind, suggestions: Vec<String>, span: Span) -> Self {
        Self {
            kind,
            suggestions: suggestions
                .into_iter()
                .map(|s| s.into())
                .collect::<Vec<String>>(),
            span,
        }
    }
    pub fn suggest<S: Into<String>>(&mut self, sug: S) -> &mut Self {
        self.suggestions.push(sug.into());
        self
    }

    #[allow(dead_code)]
    pub fn add_suggestion<S: Into<String>>(&mut self, sug: S) {
        self.suggestions.push(sug.into());
    }

    fn underline(&self) -> String {
        let buf_len = self.span.hi - self.span.lo;
        (0..=buf_len).map(|_| "^").collect::<String>()
    }

    fn get_src_file(&self) -> io::Result<String> {
        std::fs::read_to_string(&self.span.file)
    }

    fn span_snippet(&self) -> io::Result<String> {
        let s = self.line_span()?;
        Ok(self.get_src_file()?[s.lo..s.hi].trim_start().to_string())
    }

    fn line_span(&self) -> io::Result<Span> {
        // FIXME(Simon): I haven't tested this, but it seems like this is going to work only on linux with the current solution
        // FIXME(Simon): because windows uses not only a '\n' as a newline char but combines it with a '\r'
        let mut line_offsets = vec![0];
        line_offsets.extend(
            self.get_src_file()?
                .char_indices()
                .filter(|(_, c)| *c == '\n')
                .map(|(i, _)| i)
                .collect::<Vec<usize>>(),
        );
        /*
        assert!(
            self.span.hi <= *line_offsets.last().unwrap(),
            "`hi` marker of span is outside of file"
        );
        */
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
            .get_src_file()?
            .char_indices()
            .skip(lo)
            .find(|(_, c)| !c.is_whitespace())
            .unwrap();
        Ok(Span::new(lo, hi, self.span.file.clone()))
    }

    fn line_num(&self) -> io::Result<usize> {
        Ok(self
            .get_src_file()?
            .char_indices()
            .filter(|(_, c)| *c == '\n')
            .position(|(i, _)| i >= self.span.lo)
            .expect("failed to compute line number of err")
            + 1)
    }

    fn get_color(&self) -> Color {
        match self.kind {
            ErrKind::Warning { .. } => Color::Yellow,
            ErrKind::Internal(_) => Color::BrightMagenta,
            _ => Color::Red,
        }
    }

    fn get_kind(&self) -> &str {
        match self.kind {
            ErrKind::Warning { .. } => "Warnung",
            ErrKind::Internal(_) => "interner Fehler",
            ErrKind::Runtime(..) => "Laufzeitfehler",
            ErrKind::Syntax(..) => "Syntaxfehler",
            ErrKind::Type(..) => "Typenfehler",
        }
    }

    fn write_code_snippet(&self, f: &mut fmt::Formatter, c: Color) -> fmt::Result {
        let line_str = format!(" {} {}", self.line_num().unwrap(), "|".bold());
        let align = line_str.len() - 8;
        let u_line = self.underline();

        writeln!(f, "{:>a$}", "|".bold(), a = align)?;
        writeln!(f, "{} {}", line_str, self.span_snippet().unwrap())?;
        writeln!(
            f,
            "{:>a$} {:>u$}",
            "|".bold(),
            u_line.color(c).bold(),
            a = align,
            u = self.span.lo - self.line_span().unwrap().lo + u_line.len()
        )?;

        let msg = format!("{}", self.kind).color(c).bold();
        writeln!(f, "{:>a$} {}", "|".bold(), msg, a = align)
    }

    // fn write_code_snippet(&self, f: &mut fmt::Formatter, c: Color) -> fmt::Result {
    //     dbg!(self.span);
    // }
}

impl fmt::Display for Diagnostic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let color = self.get_color();
        writeln!(
            f,
            "{} {} {}[{}]",
            "--".bold(),
            self.get_kind().bold().color(color),
            "-----------------------------------------------------------".bold(),
            self.span.file.to_str().unwrap().blue()
        )?;
        //write!(f, "\n{} {}", "->".bold(), msg);

        let line_str = format!(" {} |", self.line_num().unwrap());

        let align = line_str.len();
        let u_line = self.underline();

        writeln!(f)?;
        self.write_code_snippet(f, color);
        // writeln!(f, "{:>a$}", "|", a = align)?;

        // writeln!(f, "{} {}", line_str, self.span_snippet().unwrap())?;

        // writeln!(
        //     f,
        //     "{:>a$} {:>u$}",
        //     "|",
        //     u_line.color(color).bold(),
        //     a = align,
        //     u = self.span.lo - self.line_span().unwrap().lo + u_line.len()
        // )?;
        // writeln!(
        //     f,
        //     "{:>a$} {}: {}",
        //     "|",
        //     "Hilfe".bold().underline(),
        //     self.kind,
        //     a = align
        // )?;
        if self.suggestions.len() != 0 {
            writeln!(f)?;
            writeln!(f, "{}", "Hilfe:".bold().underline())?;
            for sug in &self.suggestions {
                writeln!(f, " • {}", sug)?;
            }
        }
        writeln!(f, "")
    }
}
