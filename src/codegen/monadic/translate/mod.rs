//! Monadic translation pass.
//!
//! Input: an `ast::Program` already in A-normal form (see `codegen::anf`).
//! Output: an `MProgram` — the monadic IR (see `monadic::ir`).
//!
//! Translation is uniform and total: every AST node maps to exactly one rule,
//! the translator emits `Bind` everywhere (never `Let`), and Static-vs-Dynamic
//! handler classification is decided at construction time. Bind→Let promotion
//! and direct-call rewriting are the job of later `effect_opt` passes.
//!
//! See `docs/planning/uniform-effect-translation/monadic-ir-spec.md` for the
//! IR spec and `agent-guide.md` for the cross-cutting invariants.

mod expr;
mod handler;
#[cfg(test)]
mod tests;

use std::collections::HashMap;

use crate::ast::{self, Decl, ExprKind, HandlerBody, NodeId};
use crate::codegen::monadic::ir::{
    EffectInfo, MDecl, MDictConstructor, MExpr, MFunBinding, MProgram, MVal, MVar,
};
use crate::codegen::resolve::ResolutionMap;

/// Entry point.
///
/// `p` must already be ANF-normalized (`codegen::anf::normalize`). `r` is the
/// backend resolution map. `e` is the narrowed effect-info view. Tests
/// construct `EffectInfo` manually with only the fields they need.
pub fn translate(p: &ast::Program, r: &ResolutionMap, e: &EffectInfo<'_>) -> MProgram {
    let mut tr = Translator::new(p, r, e);
    p.iter().map(|d| tr.translate_decl(d)).collect()
}

/// Translator state. One instance per program; reset is not needed between
/// declarations — fresh MVar ids are program-wide unique.
pub(crate) struct Translator<'a> {
    #[allow(dead_code)] // consumed by later steps for head-side resolution lookups.
    pub(crate) resolution: &'a ResolutionMap,
    pub(crate) effect_info: &'a EffectInfo<'a>,
    /// Map effect canonical name → ops sorted alphabetically. Built once at
    /// construction by scanning `Decl::EffectDef` in the input program.
    ///
    /// **Limitation:** only effects defined in the current program are
    /// indexed. Cross-module effect ops would need EffectInfo extension; the
    /// real entry-point wiring (step 8) is expected to either inline all
    /// effect decls or extend the narrowed view. Tests insert the effect's
    /// decl into the program shell to populate this map.
    pub(crate) effect_ops: HashMap<String, Vec<String>>,
    /// Top-level `handler ... for E { ... }` declarations indexed by name.
    /// Used to resolve `with <name>` into a `Static` handler at translation
    /// time.
    pub(crate) handler_decls: HashMap<String, HandlerBody>,
    /// Local in-scope let-bindings whose RHS is a handler-valued expression
    /// (either an inline `handler for E { ... }` expression or an alias chain
    /// that ends at one). Populated/popped per-block-scope by `translate_block`.
    ///
    /// Value is the handler body to embed if the alias resolves statically;
    /// `None` means the binding is known to hold a handler value but its
    /// arms are not statically known (dynamic — e.g. produced by a factory).
    pub(crate) local_static_handlers: HashMap<String, Option<HandlerBody>>,
    /// Fresh MVar id counter — program-wide unique.
    pub(crate) fresh_mvar: u32,
}

impl<'a> Translator<'a> {
    fn new(p: &'a ast::Program, r: &'a ResolutionMap, e: &'a EffectInfo<'a>) -> Self {
        let mut effect_ops: HashMap<String, Vec<String>> = HashMap::new();
        let mut handler_decls: HashMap<String, HandlerBody> = HashMap::new();
        // Seed cross-module effects from the narrowed view first; local
        // `Decl::EffectDef` scans below take precedence on key collisions.
        for (name, ops) in e.effect_ops.iter() {
            effect_ops.insert(name.clone(), ops.clone());
        }
        for decl in p {
            match decl {
                Decl::EffectDef {
                    name, operations, ..
                } => {
                    let mut ops: Vec<String> =
                        operations.iter().map(|op| op.node.name.clone()).collect();
                    ops.sort();
                    effect_ops.insert(name.clone(), ops);
                }
                Decl::HandlerDef { name, body, .. } => {
                    handler_decls.insert(name.clone(), body.clone());
                }
                _ => {}
            }
        }
        Translator {
            resolution: r,
            effect_info: e,
            effect_ops,
            handler_decls,
            local_static_handlers: HashMap::new(),
            fresh_mvar: 0,
        }
    }

    /// Mint a fresh MVar id. Names carry the source spelling for debug; the
    /// id disambiguates shadowed/synthetic vars.
    pub(crate) fn next_mvar_id(&mut self) -> u32 {
        let n = self.fresh_mvar;
        self.fresh_mvar += 1;
        n
    }

    #[allow(dead_code)]
    pub(crate) fn mvar(&mut self, name: impl Into<String>) -> MVar {
        MVar {
            name: name.into(),
            id: self.next_mvar_id(),
        }
    }

    /// 1-based op index inside the effect's canonical (alphabetical) op tuple.
    ///
    /// `effect == ""` is the sentinel for "no `EffectInfo` resolution
    /// available" (e.g. tests that don't populate `effect_calls` /
    /// `handler_arms`). In that case we have no name to look up, so we
    /// return `1` and rely on the lowerer's authoritative recomputation.
    ///
    /// A non-empty `effect` not present in `effect_ops` indicates a
    /// cross-module effect the translator wasn't given visibility into.
    /// That's the open question flagged on step 4 — panic loudly so the
    /// real wiring (step 8 / extending `EffectInfo` with the effect-op
    /// map) can't be skipped silently.
    pub(crate) fn op_index(&self, effect: &str, op: &str) -> u32 {
        if effect.is_empty() {
            return 1;
        }
        let Some(ops) = self.effect_ops.get(effect) else {
            panic!(
                "monadic::translate: effect '{}' not visible to the translator (looking up op \
                 '{}'). Cross-module effect ops are not yet wired — extend `EffectInfo` (e.g. \
                 with an `effect_ops` field) at the entry-point boundary (planning step 8).",
                effect, op
            );
        };
        match ops.iter().position(|n| n == op) {
            Some(i) => (i + 1) as u32,
            None => panic!(
                "monadic::translate: op '{}' not declared on effect '{}' (have: {:?})",
                op, effect, ops
            ),
        }
    }

    fn translate_decl(&mut self, decl: &Decl) -> MDecl {
        match decl {
            Decl::FunBinding {
                id,
                name,
                name_span,
                params,
                body,
                span,
                ..
            } => {
                let body = self.translate_expr(body);
                MDecl::FunBinding(MFunBinding {
                    id: *id,
                    name: name.clone(),
                    name_span: *name_span,
                    params: params.clone(),
                    body,
                    span: *span,
                })
            }
            Decl::Val {
                id,
                public,
                name,
                value,
                span,
                ..
            } => MDecl::Val(MVal {
                id: *id,
                public: *public,
                name: name.clone(),
                value: self.translate_expr(value),
                span: *span,
            }),
            Decl::Let {
                id,
                name,
                value,
                span,
                ..
            } => {
                // Top-level `let` decls are not common in this backend, but
                // when present they translate as Val-shaped binders.
                MDecl::Val(MVal {
                    id: *id,
                    public: false,
                    name: name.clone(),
                    value: self.translate_expr(value),
                    span: *span,
                })
            }
            Decl::DictConstructor {
                id,
                name,
                dict_params,
                methods,
                method_effects,
                method_open_rows,
                impl_effects,
                span,
            } => {
                let methods = methods.iter().map(|m| self.translate_expr(m)).collect();
                MDecl::DictConstructor(MDictConstructor {
                    id: *id,
                    name: name.clone(),
                    dict_params: dict_params.clone(),
                    methods,
                    method_effects: method_effects.clone(),
                    method_open_rows: method_open_rows.clone(),
                    impl_effects: impl_effects.clone(),
                    span: *span,
                })
            }
            other => MDecl::Passthrough(other.clone()),
        }
    }
}

/// Wrap a sequence of `Bind`s around a tail expression. Each entry is a
/// (var, value) pair, applied from last to first (closest binder is at the
/// front of `bindings` when iterated; we reverse internally so the first
/// pushed binding is the outermost). Callers push in source order.
pub(crate) fn wrap_binds(bindings: Vec<(MVar, MExpr)>, tail: MExpr) -> MExpr {
    let mut acc = tail;
    for (var, value) in bindings.into_iter().rev() {
        acc = MExpr::Bind {
            var,
            value: Box::new(value),
            body: Box::new(acc),
        };
    }
    acc
}

/// Helper: take an arbitrary node id from an AST node kind we'll need a
/// fallback for. Only used where the source NodeId is meaningfully absent —
/// e.g. a synthetic unit returned for an empty block — and a fresh id is
/// appropriate.
#[inline]
pub(crate) fn fresh_node_id() -> NodeId {
    NodeId::fresh()
}

/// Convenience: detect the shape `HandlerExpr { body }` so we can route
/// `let h = handler for E { ... }` aliasing through a single helper.
pub(crate) fn match_handler_expr(e: &ast::Expr) -> Option<&HandlerBody> {
    match &e.kind {
        ExprKind::HandlerExpr { body } => Some(body),
        _ => None,
    }
}
