//! Pattern lowering for the new lowerer.
//!
//! Sub-step 7a only needs enough to render function-parameter patterns as
//! Core Erlang variable names. The full `Pat → CPat` lowering — constructors,
//! tuples, lists, binaries, alias patterns — arrives in sub-step 7g.
//!
//! Mirrors `src/codegen/lower/pats.rs::lower_params`; copied here per the
//! agent-guide "no imports from frozen files" rule.

use std::collections::HashMap;

use crate::ast::{Lit, Pat};
use crate::codegen::cerl::{CBinSeg, CLit, CPat};

use super::util::{core_var, lower_lit, mangle_ctor_atom};

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

/// Minimal `Pat → CPat` translation for sub-step 7c (Case patterns).
///
/// Handles the variants needed to lower `MExpr::Case` arms in the simple
/// shapes tests will exercise: variables, wildcards, literals, tuples, and
/// constructor patterns (with the same special cases as `lower_ctor_atom`:
/// `Nil` → `[]`, `True`/`False` → bare atoms, `Cons(h, t)` → cons-pat).
///
/// Surface-syntax patterns (`ListPat`, `ConsPat`, `StringPrefix`, `Record`,
/// `AnonRecord`, `BitStringPat`) are deferred to sub-step 7g; lowering one
/// panics with a clear message.
pub(super) fn lower_pat(pat: &Pat, ctors: &HashMap<String, String>) -> CPat {
    match pat {
        Pat::Wildcard { .. } => CPat::Wildcard,
        Pat::Var { name, .. } => CPat::Var(core_var(name)),
        Pat::Lit { value, .. } => match value {
            Lit::String(s, _) => {
                CPat::Binary(s.as_bytes().iter().map(|&b| CBinSeg::Byte(b)).collect())
            }
            _ => CPat::Lit(lower_lit(value)),
        },
        Pat::Tuple { elements, .. } => {
            CPat::Tuple(elements.iter().map(|p| lower_pat(p, ctors)).collect())
        }
        Pat::Constructor { name, args, .. } => {
            let bare = name.rsplit('.').next().unwrap_or(name);
            match bare {
                "Nil" if args.is_empty() => CPat::Nil,
                "True" if args.is_empty() => CPat::Lit(CLit::Atom("true".to_string())),
                "False" if args.is_empty() => CPat::Lit(CLit::Atom("false".to_string())),
                _ => {
                    if name == "Cons" && args.len() == 2 {
                        return CPat::Cons(
                            Box::new(lower_pat(&args[0], ctors)),
                            Box::new(lower_pat(&args[1], ctors)),
                        );
                    }
                    let tag = mangle_ctor_atom(name, ctors);
                    let mut elems = vec![CPat::Lit(CLit::Atom(tag))];
                    elems.extend(args.iter().map(|p| lower_pat(p, ctors)));
                    CPat::Tuple(elems)
                }
            }
        }
        Pat::Record { .. }
        | Pat::AnonRecord { .. }
        | Pat::StringPrefix { .. }
        | Pat::BitStringPat { .. }
        | Pat::ListPat { .. }
        | Pat::ConsPat { .. }
        | Pat::Or { .. } => {
            panic!(
                "lower_pat: pattern variant deferred to sub-step 7g (full pattern lowering): {:?}",
                pat
            )
        }
    }
}
