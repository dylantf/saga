mod doc;
mod decl;
mod expr;
mod helpers;
mod pat;
mod program;
mod type_expr;

pub use doc::{Doc, pretty};
pub use program::format_program;

/// Format an annotated program (with trivia) to a string with the given line width.
pub fn format(program: &crate::ast::AnnotatedProgram, width: usize) -> String {
    let doc = format_program(program);
    pretty(width, &doc)
}
