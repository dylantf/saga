//! Local utilities for the new lowerer.
//!
//! Copied (not imported) from the old lowerer per the agent-guide's
//! "no imports from frozen files" rule. Each helper here mirrors the
//! corresponding one in `src/codegen/lower/util.rs` so emitted Core Erlang
//! matches the old path's identifier conventions.

/// Map a Saga identifier to a Core Erlang variable name.
///
/// Core Erlang variables must start with an uppercase letter or underscore.
/// Source-lowercase names get capitalized; anything else (already-uppercase,
/// digits, symbols) is prefixed with `_`.
pub(super) fn core_var(name: &str) -> String {
    let mut chars = name.chars();
    match chars.next() {
        None => "_".to_string(),
        Some(first) => {
            let mut result = String::new();
            if first.is_lowercase() {
                result.push(first.to_ascii_uppercase());
            } else {
                result.push('_');
                result.push(first);
            }
            result.extend(chars);
            result
        }
    }
}
