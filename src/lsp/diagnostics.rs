use tower_lsp::lsp_types::*;

use dylang::{derive, lexer, parser, typechecker};

use crate::line_index::LineIndex;

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

pub fn check(checker: &mut typechecker::Checker, text: &str) -> Vec<Diagnostic> {
    let line_index = LineIndex::new(text);

    let tokens = match lexer::Lexer::new(text).lex() {
        Ok(tokens) => tokens,
        Err(e) => return vec![make_diagnostic(&line_index, e.message, e.pos)],
    };

    let mut program = match parser::Parser::new(tokens).parse_program() {
        Ok(program) => program,
        Err(e) => return vec![make_diagnostic(&line_index, e.message, e.span.start)],
    };

    derive::expand_derives(&mut program);

    match checker.check_program(&program) {
        Ok(()) => vec![],
        Err(e) => {
            let start_offset = e.span.map(|s| s.start).unwrap_or(0);
            let end_offset = e.span.map(|s| s.end).unwrap_or(1);
            let (start_line, start_col) = line_index.offset_to_line_col(start_offset);
            let (end_line, end_col) = line_index.offset_to_line_col(end_offset);
            vec![Diagnostic {
                range: Range {
                    start: Position::new(start_line as u32, start_col as u32),
                    end: Position::new(end_line as u32, end_col as u32),
                },
                severity: Some(DiagnosticSeverity::ERROR),
                message: e.message,
                ..Default::default()
            }]
        }
    }
}
