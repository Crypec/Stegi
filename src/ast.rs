pub enum TokenKind {
	Ident,

	Keyword(Keyword),

	// Values for internally supported types
	Literal(Literal),

	PathSep,

	
	// Delimiters
	CurlyOpen,
	CurlyClosed,
	LParen,
	RParen,
	LBracket,
	RBracket,

	Colon,
	Dot,
	Comma,


	Eq,


	// Comparison operators
	EqEq,
	NotEq,
	Greater,
	GreaterEq,
	Less,
	LessEq,


	// other punktuation tokens
	Semi,
	Underscore,
	ColonEq,
	ThinArrow,


	EOF,
}

impl TokenKind {
	fn match_kind(src: &str) -> Self {
		match src {
			"funktion" | "fun" | "fn" => TokenKind::Keyword(Keyword::Fun),
			"Typ:" => TokenKind::Keyword(Keyword::Struct),
			"implementiere" | "impl" => TokenKind::Keyword(Keyword::Impl),
			"selbst" => TokenKind::Keyword(Keyword::This),
			"solange" => TokenKind::Keyword(Keyword::While),
			"rueckgabe" => TokenKind::Keyword(Keyword::Return),
			"fuer" => TokenKind::Keyword(Keyword::For),
			".." | "bis" => TokenKind::Keyword(Keyword::Range),
			"wenn" => TokenKind::Keyword(Keyword::If),
			"dann" => TokenKind::Keyword(Keyword::Then),
			"sonst" => TokenKind::Keyword(Keyword::Else),
			"stop" => TokenKind::Keyword(Keyword::Break),

			"::" => TokenKind::PathSep,

			"{" => TokenKind::CurlyOpen,
			"}" => TokenKind::CurlyClosed,

			"(" => TokenKind::LParen,
			")" => TokenKind::RParen,

			"[" => TokenKind::RBracket,
			"]" => TokenKind::RBracket,

			":" => TokenKind::Colon,
			"." => TokenKind::Dot,
			"," => TokenKind::Comma,

			"=" => TokenKind::Eq,

			"==" => TokenKind::EqEq,
			"!=" => TokenKind::NotEq,
			"<" => TokenKind::Greater,
			">" => TokenKind::Less,
			"<=" => TokenKind::GreaterEq,
			"=>" => TokenKind::LessEq,
			";" => TokenKind::Semi,
			"_" => TokenKind::Underscore,
			":=" => TokenKind::ColonEq,
			"->" => TokenKind::ThinArrow,
			_ => TokenKind::Ident,
		}
	}
}

pub enum Literal {
	String(String),
	Number(f64),
	Bool(bool),
}

pub enum Keyword {
	// keywords used internall by the language
	Fun,
	Struct,
	Impl,
	This,
	While,
	Return,
	For,
	Break,
	Range,
	If,
	Then,
	Else,
}


struct Position {
	start: u64,
	end: u64,
	line: u64,
}

pub struct Token {
	kind: TokenKind,
	pos: Position,
	literal: String,
}
