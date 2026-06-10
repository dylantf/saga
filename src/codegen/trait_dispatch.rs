//! Trait dispatch classification facts (optimizer track).
//!
//! Records, per trait `DictMethodAccess` call site, whether the dictionary is
//! statically known (`KnownImpl`) or must dispatch dynamically through the
//! runtime dict tuple (`Dynamic`).
//!
//! This is an *optimizer* fact, not a correctness fact: it is optional and
//! fallback-safe. A missing or `Dynamic` entry keeps the normal `element/2`
//! dispatch that lowering already emits. Facts say *which impl*; lowering joins
//! the call shape from `CallEffectInfo` (same App `NodeId`) so the effect ABI is
//! never altered by specialization.
//!
//! Phase 0 is a behavior-neutral shell: it classifies nothing yet, so every
//! dict method call site is implicitly `Dynamic`. Phase 1 fills the map.

use crate::ast::{self, Decl, NodeId};
use std::collections::HashMap;

/// How a single trait `DictMethodAccess` call site dispatches.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DictDispatch {
    /// Runtime dictionary value (e.g. a where-bound dict parameter). The
    /// concrete impl is not known at this site; keep `element/2` dispatch.
    Dynamic,
    /// Statically resolvable to a named dict constructor and method slot.
    KnownImpl {
        /// Dict constructor name, e.g. `__dict_ToJson_Person`.
        dict_constructor: String,
        /// 0-based method slot in trait-declaration order.
        method_index: usize,
        /// Dispatch for each sub-dictionary of a parameterized impl, in order.
        /// Empty for a nullary (monomorphic) dict. A single `Dynamic` sub-dict
        /// makes the whole call ineligible (all-or-nothing).
        sub_dicts: Vec<DictDispatch>,
    },
}

/// Per-call-site trait dispatch facts, keyed by the `DictMethodAccess` App node.
pub type DictDispatchMap = HashMap<NodeId, DictDispatch>;

/// Classify trait dictionary dispatch for a module.
///
/// Phase 0 returns an empty map (every site stays on the default `Dynamic`
/// path). `resolution` is threaded now because Phase 1 needs it to distinguish
/// local from imported dict constructors.
pub fn analyze(
    module_name: &str,
    program: &ast::Program,
    _resolution: &super::resolve::ResolutionMap,
) -> DictDispatchMap {
    let map = DictDispatchMap::new();
    maybe_trace(module_name, program, &map);
    map
}

fn source_module_name(module_name: &str, program: &ast::Program) -> String {
    program
        .iter()
        .find_map(|decl| match decl {
            Decl::ModuleDecl { path, .. } => Some(path.join(".")),
            _ => None,
        })
        .unwrap_or_else(|| module_name.to_string())
}

fn trace_enabled_for(subject: &str) -> bool {
    let Some(filter) = std::env::var_os("SAGA_DEBUG_TRAIT_DISPATCH") else {
        return false;
    };
    let filter = filter.to_string_lossy();
    let filter = filter.trim();
    filter.is_empty() || matches!(filter, "1" | "true" | "all") || subject.contains(filter)
}

fn maybe_trace(module_name: &str, program: &ast::Program, map: &DictDispatchMap) {
    let subject = source_module_name(module_name, program);
    if !trace_enabled_for(&subject) {
        return;
    }
    eprintln!("{}", format_trace(&subject, map));
}

/// Render the dispatch map in NodeId order (a stable proxy for source order).
pub fn format_trace(subject: &str, map: &DictDispatchMap) -> String {
    let mut entries: Vec<(&NodeId, &DictDispatch)> = map.iter().collect();
    entries.sort_by_key(|(id, _)| id.0);
    let mut out = format!("trait-dispatch[{subject}]: {} dict method call(s)", entries.len());
    for (id, dispatch) in entries {
        out.push_str(&format!("\n  app#{} {}", id.0, format_dispatch(dispatch)));
    }
    out
}

fn format_dispatch(dispatch: &DictDispatch) -> String {
    match dispatch {
        DictDispatch::Dynamic => "Dynamic".to_string(),
        DictDispatch::KnownImpl {
            dict_constructor,
            method_index,
            sub_dicts,
        } => {
            let subs: Vec<String> = sub_dicts.iter().map(format_dispatch).collect();
            if subs.is_empty() {
                format!("KnownImpl {dict_constructor}#{method_index}")
            } else {
                format!(
                    "KnownImpl {dict_constructor}#{method_index} [{}]",
                    subs.join(", ")
                )
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_map_traces_zero_calls() {
        let map = DictDispatchMap::new();
        assert_eq!(
            format_trace("Example", &map),
            "trait-dispatch[Example]: 0 dict method call(s)"
        );
    }

    #[test]
    fn format_trace_orders_by_node_id() {
        let mut map = DictDispatchMap::new();
        map.insert(NodeId(7), DictDispatch::Dynamic);
        map.insert(
            NodeId(2),
            DictDispatch::KnownImpl {
                dict_constructor: "__dict_ToJson_Person".to_string(),
                method_index: 0,
                sub_dicts: vec![],
            },
        );
        assert_eq!(
            format_trace("M", &map),
            "trait-dispatch[M]: 2 dict method call(s)\n  \
             app#2 KnownImpl __dict_ToJson_Person#0\n  app#7 Dynamic"
        );
    }

    #[test]
    fn format_dispatch_renders_nested_sub_dicts() {
        let dispatch = DictDispatch::KnownImpl {
            dict_constructor: "__dict_ToJson_List".to_string(),
            method_index: 0,
            sub_dicts: vec![DictDispatch::KnownImpl {
                dict_constructor: "__dict_ToJson_Int".to_string(),
                method_index: 0,
                sub_dicts: vec![],
            }],
        };
        assert_eq!(
            format_dispatch(&dispatch),
            "KnownImpl __dict_ToJson_List#0 [KnownImpl __dict_ToJson_Int#0]"
        );
    }
}
