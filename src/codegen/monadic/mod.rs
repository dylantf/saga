//! Monadic IR for the new uniform-effect-translation path.
//!
//! Stage 10 of the refactor. This crate-internal module owns the IR types
//! (`ir`) plus, in later steps, the translator (`translate`), debug
//! pretty-printer (`print`), and effect optimization (`effect_opt`).
//!
//! See `docs/planning/uniform-effect-translation/monadic-ir-spec.md` for the
//! full type spec and `agent-guide.md` for the cross-cutting invariants
//! (strict no-imports, NodeId discipline, "fields with a named consumer").

pub mod effect_opt;
pub mod ir;
pub mod print;
pub mod translate;
