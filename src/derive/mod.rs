//! Deriving pass: expands `deriving (Show, ...)` clauses on type definitions
//! into synthetic `ImplDef` nodes. Runs before typechecking so the generated
//! impls are validated like any hand-written impl.
//!
//! Split across submodules by concern:
//! - `imports`   — collecting structural summaries of imported decls
//! - `scope`     — derive scope and trait-default inheritance support
//! - `expand`    — top-level driver and free-variable/constructor qualification
//! - `type_expr` — `TypeExpr` manipulation helpers
//! - `builtin`   — built-in derives (Show, Debug, Eq, Ord, Enum, Default)

mod builtin;
mod expand;
mod imports;
mod scope;
mod type_expr;

// Public API surface (used by other crates / integration tests).
pub use expand::expand_derives;
pub use imports::{
    ImportSummaryCache, ImportedDecls, SummaryEntry, WrapperRecordInfo, WrapperTypeInfo,
    collect_from_project_root, collect_imported_decls, collect_imported_decls_cached,
    collect_imported_decls_with_sources,
};
pub use scope::RoutedTraitInfo;

// Crate-internal re-exports so submodules can reach each other via `use super::*`.
pub(crate) use builtin::*;
pub(crate) use scope::*;
pub(crate) use type_expr::*;
