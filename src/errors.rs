use std::fmt;

use crate::ast::Span;
use crate::lexer::TokenKind;
use crate::session::SourceMap;
use crate::typer::Ty;

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
            SyntaxErr::MissingToken{expected, actual} => write!(f, "Wir haben hier eher ´{:?}´ erwartet, als {}. Versuche doch {:?} durch {} zu ersetzen.", expected, actual, expected, actual),
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

#[derive(Debug, Clone)]
pub enum TypeErr {
    VarNotFound(String),
    TyNotFound(String),
    InvalidType(Ty, Ty),
    // TODO(Simon): this should really be a ty instead of just a tykind, we need the span to do proper error reporting
    InfRec(Ty, Ty),
    DuplicateLitField(String),
    MissingField(String),
    InvalidField(String, String),
    FieldNotFound { ty: Ty, field: String },
    GenericsMismatch(Ty, Ty),
    NonStaticCall { ty_name: String, fn_name: String },
    StaticFnNotFound { ty_name: String, fn_name: String },
}

impl fmt::Display for TypeErr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self{
            TypeErr:: VarNotFound(varname) => write!(f, "Diese Variable `{}` haben wir nicht gefunden. Bitte Definiere und Initialisiere sie, bevor du sie benutzt.", varname),
            TypeErr::InvalidType(expected, actual)=> write!(f, "Du hast hier einen Typ benutzt der entweder gar nicht existiert oder hier nicht funktioniert. Bitte schau da nochmal drüber. Erwartet: {} => Gefunden: {}", expected, actual),
            TypeErr::InfRec(a, b) => write!(f, "Unendlich rekursiver Typ entdeckt! Typ: {}, kommt in {} vor!!!", a, b),
            TypeErr::FieldNotFound{ty, field} => write!(f, "Der Datentyp {} hat kein Feld mit dem Namen {}!", ty, field),
			TypeErr::TyNotFound(t) => write!(f, "Keine Defintion fuer den Datentyp {} gefunden", t),
			TypeErr::DuplicateLitField(field) => write!(f, "Jedes Feld eines Objektes kann nur einmal vorkommen, '{}' kommt dabei allerdings mehr als einmal vor!", field),
			TypeErr::MissingField(field) => write!(f, "Du hast vergessen dem Feld {} einen Wert zu geben!", field),
			TypeErr::InvalidField(ty, field) => write!(f, "Der Datentyp: {} hat kein Feld mit dem Namen: {}!", ty, field),
			TypeErr::GenericsMismatch(lhs, rhs) => write!(f, "An dieser Stelle haben wir {} erwartet, aber {} gefunden!", lhs, rhs),
			TypeErr::NonStaticCall{ty_name, fn_name} => write!(f, "Die Funktion: {} des Datentypen {}, ist nicht statisch! Der 'selbst' Paramter ist fuer statische Funktionen nicht erlaubt!", fn_name, ty_name),
			TypeErr::StaticFnNotFound{ty_name, fn_name} => write!(f, "Der Datentyp {} hat keine statische Funktion mit dem Namen {}!", ty_name, fn_name),

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
    pub fn suggest<S: Into<String>>(self, sug: S) -> Self {
        let mut diag = self;
        diag.suggestions.push(sug.into());
        diag
    }

    #[allow(dead_code)]
    pub fn add_suggestion<S: Into<String>>(&mut self, sug: S) {
        self.suggestions.push(sug.into());
    }
}

#[derive(Debug)]
pub struct UserDiagnostic {
    pub src_map: SourceMap,
    pub kind: ErrKind,
    pub suggestions: Vec<String>,
    pub span: Span,
}

impl UserDiagnostic {
    pub fn new(diag: Diagnostic, src_map: SourceMap) -> Self {
        // TODO(Simon): there may be a better way to copy the data from Diagnostic into UserDiagnostic
        Self {
            src_map,
            kind: diag.kind,
            suggestions: diag.suggestions,
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
        buf[s.lo..s.hi].trim_start().to_string()
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
            self.kind,
            a = align
        )
    }
}

impl fmt::Display for UserDiagnostic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let color = match self.kind {
            ErrKind::Warning { .. } => Color::Yellow,
            ErrKind::Internal(_) => Color::BrightMagenta,
            _ => Color::Red,
        };
        let msg = format!("{}", self.kind).color(color).bold();
        writeln!(
            f,
            "{} {} {}[{}]",
            "--".bold(),
            msg,
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
