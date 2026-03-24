mod doc;
mod format;

pub use doc::{Doc, pretty};
pub use format::format_program;

use crate::ast::Program;

/// Format a parsed program to a string with the given line width.
pub fn format(program: &Program, width: usize) -> String {
    let doc = format_program(program);
    pretty(width, &doc)
}
