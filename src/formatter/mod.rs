mod decl;
mod doc;
mod expr;
mod helpers;
mod pat;
mod program;
mod type_expr;

pub use doc::{Doc, pretty};
pub use program::format_program;

/// Default line width for the formatter.
pub const DEFAULT_WIDTH: usize = 80;

/// Format an annotated program (with trivia) to a string with the given line width.
pub fn format(program: &crate::ast::AnnotatedProgram, width: usize) -> String {
    let doc = format_program(program);
    pretty(width, &doc)
}

#[cfg(test)]
mod tests;
