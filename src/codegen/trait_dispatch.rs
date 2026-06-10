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
//! Keyed by the **outer `App` node id** — the same key `call_effects` uses
//! (`CallEffectMap`) and the same id lowering passes to `lower_dict_method_call`
//! — so the two maps join trivially at the call site.

use crate::ast::{self, Decl, Expr, ExprKind, NodeId};
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
        /// Sub-dictionary *values* of a parameterized impl, in order. Empty for
        /// a nullary (monomorphic) dict. These are dictionary values, not method
        /// call sites, so they carry no method index. A `Dynamic` sub-dict makes
        /// the call ineligible for full specialization (all-or-nothing) — that
        /// admission rule lives in the Phase 2 consumer, not here.
        sub_dicts: Vec<DictValue>,
    },
}

/// A dictionary *value* passed as a sub-dictionary argument to a parameterized
/// impl's dict constructor (e.g. the element dict in `ToJson (List a)`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DictValue {
    /// Statically-known dict constructor, with its own resolved sub-dicts.
    Known {
        constructor: String,
        sub_dicts: Vec<DictValue>,
    },
    /// Runtime dict value (where-bound param), or otherwise unresolved.
    Dynamic,
}

/// Per-call-site trait dispatch facts, keyed by the `DictMethodAccess` App node.
pub type DictDispatchMap = HashMap<NodeId, DictDispatch>;

/// Classify trait dictionary dispatch for a module.
///
/// Classification is purely shape-based on the elaborated dict expression: a
/// `DictRef` head resolves to `KnownImpl`; a `Var` (where-bound) head resolves
/// to `Dynamic`. `resolution` is threaded for later phases (local-vs-imported
/// gating lives in the consumer); classification itself does not need it.
pub fn analyze(
    module_name: &str,
    program: &ast::Program,
    _resolution: &super::resolve::ResolutionMap,
) -> DictDispatchMap {
    let mut map = DictDispatchMap::new();
    for decl in program {
        match decl {
            Decl::FunBinding { body, .. } => visit_expr(body, &mut map),
            // Building-block and impl method bodies live here post-elaboration.
            Decl::DictConstructor { methods, .. } => {
                for method in methods {
                    visit_expr(method, &mut map);
                }
            }
            _ => {}
        }
    }
    maybe_trace(module_name, program, &map);
    map
}

fn visit_expr(expr: &Expr, map: &mut DictDispatchMap) {
    if matches!(expr.kind, ExprKind::App { .. })
        && let Some(dispatch) = classify_app(expr)
    {
        map.insert(expr.id, dispatch);
    }
    super::optimize::walk_expr(expr, &mut |child| visit_expr(child, map));
}

/// Classify an `App` whose peeled head is a `DictMethodAccess`. Returns `None`
/// for any other call shape (those are not trait dispatch sites).
fn classify_app(expr: &Expr) -> Option<DictDispatch> {
    let (head, _args) = peel_app(expr);
    match &head.kind {
        ExprKind::DictMethodAccess {
            dict, method_index, ..
        } => Some(dispatch_for_dict(dict, *method_index)),
        _ => None,
    }
}

/// Resolve the dictionary expression of a method call to a dispatch fact.
fn dispatch_for_dict(dict: &Expr, method_index: usize) -> DictDispatch {
    let (head, sub_dict_exprs) = peel_app(dict);
    match &head.kind {
        ExprKind::DictRef { name } => DictDispatch::KnownImpl {
            dict_constructor: name.clone(),
            method_index,
            sub_dicts: sub_dict_exprs.iter().map(|e| dict_value(e)).collect(),
        },
        // `Var` => where-bound runtime dict; anything else => not a static dict.
        _ => DictDispatch::Dynamic,
    }
}

/// Resolve a sub-dictionary argument (a dictionary *value*) to a `DictValue`.
fn dict_value(expr: &Expr) -> DictValue {
    let (head, sub_dict_exprs) = peel_app(expr);
    match &head.kind {
        ExprKind::DictRef { name } => DictValue::Known {
            constructor: name.clone(),
            sub_dicts: sub_dict_exprs.iter().map(|e| dict_value(e)).collect(),
        },
        _ => DictValue::Dynamic,
    }
}

/// Peel a chain of `App` nodes, returning the innermost non-`App` head and the
/// supplied arguments in source order.
fn peel_app(expr: &Expr) -> (&Expr, Vec<&Expr>) {
    let mut args: Vec<&Expr> = Vec::new();
    let mut current = expr;
    while let ExprKind::App { func, arg } = &current.kind {
        args.push(arg.as_ref());
        current = func;
    }
    args.reverse();
    (current, args)
}

// --- Debug trace --------------------------------------------------------------

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
    let known = entries
        .iter()
        .filter(|(_, d)| matches!(d, DictDispatch::KnownImpl { .. }))
        .count();
    let mut out = format!(
        "trait-dispatch[{subject}]: {} dict method call(s), {known} known",
        entries.len()
    );
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
        } => format!(
            "KnownImpl {dict_constructor}#{method_index}{}",
            format_sub_dicts(sub_dicts)
        ),
    }
}

fn format_sub_dicts(sub_dicts: &[DictValue]) -> String {
    if sub_dicts.is_empty() {
        return String::new();
    }
    let rendered: Vec<String> = sub_dicts.iter().map(format_dict_value).collect();
    format!(" [{}]", rendered.join(", "))
}

fn format_dict_value(value: &DictValue) -> String {
    match value {
        DictValue::Dynamic => "Dynamic".to_string(),
        DictValue::Known {
            constructor,
            sub_dicts,
        } => format!("{constructor}{}", format_sub_dicts(sub_dicts)),
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
            "trait-dispatch[Example]: 0 dict method call(s), 0 known"
        );
    }

    #[test]
    fn format_trace_orders_by_node_id_and_counts_known() {
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
            "trait-dispatch[M]: 2 dict method call(s), 1 known\n  \
             app#2 KnownImpl __dict_ToJson_Person#0\n  app#7 Dynamic"
        );
    }

    #[test]
    fn format_renders_nested_known_sub_dicts() {
        let dispatch = DictDispatch::KnownImpl {
            dict_constructor: "__dict_ToJson_List".to_string(),
            method_index: 0,
            sub_dicts: vec![DictValue::Known {
                constructor: "__dict_ToJson_Int".to_string(),
                sub_dicts: vec![],
            }],
        };
        assert_eq!(
            format_dispatch(&dispatch),
            "KnownImpl __dict_ToJson_List#0 [__dict_ToJson_Int]"
        );
    }

    #[test]
    fn format_renders_dynamic_sub_dict() {
        let dispatch = DictDispatch::KnownImpl {
            dict_constructor: "__dict_ToJson_List".to_string(),
            method_index: 0,
            sub_dicts: vec![DictValue::Dynamic],
        };
        assert_eq!(
            format_dispatch(&dispatch),
            "KnownImpl __dict_ToJson_List#0 [Dynamic]"
        );
    }
}
