//! Monadic IR for the new uniform-effect-translation path.
//!
//! Stage 10 of the refactor. This crate-internal module owns the IR types
//! (`ir`), translator (`translate`), debug pretty-printer (`print`), and
//! structural diagnostics (`stats`).
//!
//! See `docs/planning/uniform-effect-translation/monadic-ir-spec.md` for the
//! full type spec and `agent-guide.md` for the cross-cutting invariants
//! (strict no-imports, NodeId discipline, "fields with a named consumer").

pub mod ir;
pub mod print;
pub mod stats;
pub mod translate;
