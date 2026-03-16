use tower_lsp::lsp_types::*;

use dylang::{ast, derive, lexer, parser, typechecker};

use crate::line_index::LineIndex;

pub struct CheckResult {
    pub diagnostics: Vec<Diagnostic>,
    pub checker: typechecker::Checker,
    pub program: Option<ast::Program>,
    pub line_index: LineIndex,
    pub source: String,
}

fn make_diagnostic(line_index: &LineIndex, message: String, offset: usize) -> Diagnostic {
    let (line, col) = line_index.offset_to_line_col(offset);
    Diagnostic {
        range: Range {
            start: Position::new(line as u32, col as u32),
            end: Position::new(line as u32, col as u32 + 1),
        },
        severity: Some(DiagnosticSeverity::ERROR),
        message,
        ..Default::default()
    }
}

pub fn check(checker: typechecker::Checker, text: &str) -> CheckResult {
    let line_index = LineIndex::new(text);
    let source = text.to_string();
    let mut checker = checker;

    let tokens = match lexer::Lexer::new(text).lex() {
        Ok(tokens) => tokens,
        Err(e) => {
            return CheckResult {
                diagnostics: vec![make_diagnostic(&line_index, e.message, e.pos)],
                checker,
                program: None,
                line_index,
                source,
            };
        }
    };

    let mut program = match parser::Parser::new(tokens).parse_program() {
        Ok(program) => program,
        Err(e) => {
            return CheckResult {
                diagnostics: vec![make_diagnostic(&line_index, e.message, e.span.start)],
                checker,
                program: None,
                line_index,
                source,
            };
        }
    };

    derive::expand_derives(&mut program);

    let diagnostics = match checker.check_program(&program) {
        Ok(()) => vec![],
        Err(errors) => errors
            .into_iter()
            .map(|e| {
                let start_offset = e.span.map(|s| s.start).unwrap_or(0);
                let end_offset = e.span.map(|s| s.end).unwrap_or(1);
                let (start_line, start_col) = line_index.offset_to_line_col(start_offset);
                let (end_line, end_col) = line_index.offset_to_line_col(end_offset);
                Diagnostic {
                    range: Range {
                        start: Position::new(start_line as u32, start_col as u32),
                        end: Position::new(end_line as u32, end_col as u32),
                    },
                    severity: Some(DiagnosticSeverity::ERROR),
                    message: e.message,
                    ..Default::default()
                }
            })
            .collect(),
    };

    CheckResult {
        diagnostics,
        checker,
        program: Some(program),
        line_index,
        source,
    }
}
