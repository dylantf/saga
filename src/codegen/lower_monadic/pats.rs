//! Pattern lowering for the new lowerer.
//!
//! Sub-step 7a only needs enough to render function-parameter patterns as
//! Core Erlang variable names. The full `Pat → CPat` lowering — constructors,
//! tuples, lists, binaries, alias patterns — arrives in sub-step 7g.
//!
//! Mirrors `src/codegen/lower/pats.rs::lower_params`; copied here per the
//! agent-guide "no imports from frozen files" rule.

use crate::ast::Pat;

use super::util::core_var;

/// Map a function's parameter patterns to Core Erlang variable names.
///
/// `Pat::Var { name }` keeps its name (mangled via `core_var`); every other
/// pattern (including the eventual destructuring forms) gets a positional
/// `_Arg{i}` placeholder. Sub-step 7g revisits this for real pattern
/// lowering with `case` desugaring on the function entry.
pub(super) fn lower_param_names(params: &[Pat]) -> Vec<String> {
    params
        .iter()
        .enumerate()
        .map(|(i, pat)| match pat {
            Pat::Var { name, .. } => core_var(name),
            _ => format!("_Arg{}", i),
        })
        .collect()
}
