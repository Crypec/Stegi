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
