pub struct LintPass {
    diag: Vec<Diagnostic>,
}

impl LintPass {
    pub fn new() -> Self {}
    pub fn lint(&mut self, ast: &mut AST) {}

    fn check_for_start(&self, ast: &AST) {
        let start_fns = ast
            .iter()
            .filter(|decl| match decl {
                Decl::FnDecl(f) => true,
                _ => false,
            })
            .filter(|f| f.name.lexeme == "Start")
            .collect();
		match start_fns.count() {
			1 => {},
			0 => 
		}
    }

	fn span_err() -> Diagnostic {
		
	}

}
