//! Deriving pass: expands `deriving (Show, ...)` clauses on type definitions
//! into synthetic `ImplDef` nodes. Runs before typechecking so the generated
//! impls are validated like any hand-written impl.
//!
//! Split across submodules by concern:
//! - `imports`   — collecting structural summaries of imported decls
//! - `scope`     — derive scope, trait routing info, specialization
//! - `expand`    — top-level driver and free-variable/constructor qualification
//! - `type_expr` — `TypeExpr` manipulation helpers
//! - `applied`   — applied functional-bridge synthesis
//! - `routed`    — routed-derive method synthesis and from-shape splicing
//! - `generic`   — `Generic` representation derive (records and ADTs)
//! - `builtin`   — built-in derives (Show, Debug, Eq, Ord, Enum, Default)
//! - `helpers`   — small AST construction helpers

mod applied;
mod builtin;
mod expand;
mod generic;
mod helpers;
mod imports;
mod routed;
mod scope;
mod type_expr;

// Public API surface (used by other crates / integration tests).
pub use expand::expand_derives;
pub use imports::{
    collect_from_project_root, collect_imported_decls, ImportedDecls, SummaryEntry,
    WrapperRecordInfo, WrapperTypeInfo,
};
pub use scope::RoutedTraitInfo;

// Crate-internal re-exports so submodules can reach each other via `use super::*`.
pub(crate) use applied::*;
pub(crate) use builtin::*;
pub(crate) use generic::*;
pub(crate) use helpers::*;
pub(crate) use routed::*;
pub(crate) use scope::*;
pub(crate) use type_expr::*;
