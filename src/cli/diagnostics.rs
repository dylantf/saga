use dylang::token;
use dylang::typechecker;

use super::color;

pub fn byte_offset_to_line_col(source: &str, offset: usize) -> (usize, usize) {
    let mut line = 1;
    let mut col = 1;
    for (i, ch) in source.char_indices() {
        if i >= offset {
            break;
        }
        if ch == '\n' {
            line += 1;
            col = 1;
        } else {
            col += 1;
        }
    }
    (line, col)
}

/// Get the source line at a 1-based line number.
fn get_source_line(source: &str, line_num: usize) -> Option<&str> {
    source.lines().nth(line_num - 1)
}

/// Print a diagnostic (error or warning) with source context and underline.
pub fn print_diagnostic(
    source: &str,
    source_path: &str,
    label: &str,
    span: Option<token::Span>,
    message: &str,
) {
    let (start_line, start_col) = if let Some(span) = span {
        byte_offset_to_line_col(source, span.start)
    } else {
        (1, 1)
    };
    let end_col = if let Some(span) = span {
        byte_offset_to_line_col(source, span.end).1
    } else {
        start_col + 1
    };

    eprintln!(
        "{} at {}:{}:{}: {}",
        label, source_path, start_line, start_col, message
    );
    if let Some(line_text) = get_source_line(source, start_line) {
        let line_num_width = start_line.to_string().len();
        eprintln!("  {} | {}", start_line, line_text);
        let underline_len = if end_col > start_col {
            end_col - start_col
        } else {
            1
        };
        eprintln!(
            "  {} | {}{}",
            " ".repeat(line_num_width),
            " ".repeat(start_col - 1),
            "^".repeat(underline_len)
        );
    }
}

pub fn print_tc_diagnostic(source: &str, source_path: &str, d: &typechecker::Diagnostic) {
    let label = match d.severity {
        typechecker::Severity::Error => &color::red("Type error"),
        typechecker::Severity::Warning => &color::yellow("Warning"),
    };
    print_diagnostic(source, source_path, label, d.span, &d.message);
}
