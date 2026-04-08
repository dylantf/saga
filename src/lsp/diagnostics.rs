use tower_lsp::lsp_types::*;

use dylang::{ast, derive, desugar, lexer, parser, typechecker};

use crate::line_index::LineIndex;

pub struct CheckSnapshot {
    pub diagnostics: Vec<Diagnostic>,
    pub tc_result: typechecker::CheckResult,
    pub program: Option<ast::Program>,
    pub line_index: LineIndex,
    pub source: String,
}

fn tc_to_lsp_diagnostic(
    line_index: &LineIndex,
    source: &str,
    d: &typechecker::Diagnostic,
) -> Diagnostic {
    let start_offset = d.span.map(|s| s.start).unwrap_or(0);
    let end_offset = d.span.map(|s| s.end).unwrap_or(1);
    let (start_line, start_col) = line_index.offset_to_line_col(start_offset, source);
    let (end_line, end_col) = line_index.offset_to_line_col(end_offset, source);
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

fn make_diagnostic(
    line_index: &LineIndex,
    source: &str,
    message: String,
    offset: usize,
) -> Diagnostic {
    let (line, col) = line_index.offset_to_line_col(offset, source);
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
                diagnostics: vec![make_diagnostic(&line_index, &source, e.message, e.pos)],
                tc_result: checker.to_result(),
                program: None,
                line_index,
                source,
            };
        }
    };

    let mut parser = parser::Parser::new(tokens);
    parser.test_mode = text.contains("import Std.Test");
    let mut program = match parser.parse_program() {
        Ok(program) => program,
        Err(e) => {
            return CheckSnapshot {
                diagnostics: vec![make_diagnostic(
                    &line_index,
                    &source,
                    e.message,
                    e.span.start,
                )],
                tc_result: checker.to_result(),
                program: None,
                line_index,
                source,
            };
        }
    };

    let derive_errors = derive::expand_derives(&mut program);
    desugar::desugar_program(&mut program);

    // If this file declares a builtin stdlib module, evict its cached state
    // from the checker to avoid false "duplicate impl" errors. The prelude
    // already loaded this module, but we need to re-check it cleanly.
    for decl in program.iter() {
        if let ast::Decl::ModuleDecl { path, .. } = decl {
            let module_name = path.join(".");
            if typechecker::BUILTIN_MODULES
                .iter()
                .any(|(name, _)| *name == module_name)
            {
                checker.evict_module(&module_name);
            }
            break;
        }
    }

    let tc_result = checker.check_program(&mut program);
    let mut diagnostics: Vec<Diagnostic> = derive_errors
        .iter()
        .map(|d| tc_to_lsp_diagnostic(&line_index, &source, d))
        .collect();
    diagnostics.extend(
        tc_result
            .diagnostics
            .iter()
            .map(|d| tc_to_lsp_diagnostic(&line_index, &source, d)),
    );

    CheckSnapshot {
        diagnostics,
        tc_result,
        program: Some(program),
        line_index,
        source,
    }
}
