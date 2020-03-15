struct Lexer {
	data: String,
	index: u64,
	line: u64,
	errors: Vec<Report>,
}
