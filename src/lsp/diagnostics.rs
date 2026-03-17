use tower_lsp::lsp_types::*;

use dylang::{ast, derive, lexer, parser, typechecker};

use crate::line_index::LineIndex;

pub struct CheckSnapshot {
    pub diagnostics: Vec<Diagnostic>,
    pub tc_result: typechecker::CheckResult,
    pub program: Option<ast::Program>,
    pub line_index: LineIndex,
    pub source: String,
}

fn tc_to_lsp_diagnostic(line_index: &LineIndex, d: &typechecker::Diagnostic) -> Diagnostic {
    let start_offset = d.span.map(|s| s.start).unwrap_or(0);
    let end_offset = d.span.map(|s| s.end).unwrap_or(1);
    let (start_line, start_col) = line_index.offset_to_line_col(start_offset);
    let (end_line, end_col) = line_index.offset_to_line_col(end_offset);
    let severity = match d.severity {
        typechecker::Severity::Error => DiagnosticSeverity::ERROR,
        typechecker::Severity::Warning => DiagnosticSeverity::WARNING,
    };
    Diagnostic {
        range: Range {
            start: Position::new(start_line as u32, start_col as u32),
            end: Position::new(end_line as u32, end_col as u32),
        },
        severity: Some(severity),
        message: d.message.clone(),
        ..Default::default()
    }
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

pub fn check(checker: typechecker::Checker, text: &str) -> CheckSnapshot {
    let line_index = LineIndex::new(text);
    let source = text.to_string();
    let mut checker = checker;

    let tokens = match lexer::Lexer::new(text).lex() {
        Ok(tokens) => tokens,
        Err(e) => {
            return CheckSnapshot {
                diagnostics: vec![make_diagnostic(&line_index, e.message, e.pos)],
                tc_result: checker.to_result(),
                program: None,
                line_index,
                source,
            };
        }
    };

    let mut program = match parser::Parser::new(tokens).parse_program() {
        Ok(program) => program,
        Err(e) => {
            return CheckSnapshot {
                diagnostics: vec![make_diagnostic(&line_index, e.message, e.span.start)],
                tc_result: checker.to_result(),
                program: None,
                line_index,
                source,
            };
        }
    };

    derive::expand_derives(&mut program);

    // check_program returns Err for errors, but warnings are only in collected_diagnostics.
    // Collect errors from the return value, then grab everything from to_result().
    let mut diagnostics: Vec<Diagnostic> = Vec::new();
    if let Err(errors) = checker.check_program(&program) {
        for e in &errors {
            diagnostics.push(tc_to_lsp_diagnostic(&line_index, e));
        }
    }

    let tc_result = checker.to_result();
    for d in &tc_result.diagnostics {
        diagnostics.push(tc_to_lsp_diagnostic(&line_index, d));
    }

    CheckSnapshot {
        diagnostics,
        tc_result,
        program: Some(program),
        line_index,
        source,
    }
}
