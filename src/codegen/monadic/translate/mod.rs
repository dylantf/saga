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
    BindMode, EffectInfo, HandlerValueMap, MDecl, MDictConstructor, MExpr, MFunBinding, MProgram,
    MVal, MVar,
};
use crate::codegen::resolve::ResolutionMap;

/// Entry point.
///
/// `p` must already be ANF-normalized (`codegen::anf::normalize`). `r` is the
/// backend resolution map. `e` is the narrowed effect-info view. Tests
/// construct `EffectInfo` manually with only the fields they need.
pub fn translate(
    p: &ast::Program,
    r: &ResolutionMap,
    e: &EffectInfo<'_>,
) -> (MProgram, HandlerValueMap) {
    translate_with_imports(p, r, e, &HashMap::new())
}

/// Like [`translate`], but also takes a map of imported handler bodies keyed
/// by the bare handler name (the spelling user code refers to via `with X`).
/// Imported handlers are merged into the translator's `handler_decls` so
/// `with <imported_handler>` resolves to `Static` (with arms inlined),
/// instead of falling back to the `Dynamic` path with no effect info.
///
/// Local declarations in `p` take precedence on key collisions: if a handler
/// of the same bare name is defined in the current module, that wins.
pub fn translate_with_imports(
    p: &ast::Program,
    r: &ResolutionMap,
    e: &EffectInfo<'_>,
    imported_handler_decls: &HashMap<String, HandlerBody>,
) -> (MProgram, HandlerValueMap) {
    let mut tr = Translator::new(p, r, e);
    for (name, body) in imported_handler_decls {
        tr.handler_decls
            .entry(name.clone())
            .or_insert_with(|| body.clone());
    }
    let program = p.iter().map(|d| tr.translate_decl(d)).collect();
    let handler_values = tr.build_handler_value_map();
    (program, handler_values)
}

/// Translator state. One instance per program; reset is not needed between
/// declarations — fresh MVar ids are program-wide unique.
pub(crate) struct Translator<'a> {
    #[allow(dead_code)] // consumed by later steps for head-side resolution lookups.
    pub(crate) resolution: &'a ResolutionMap,
    pub(crate) effect_info: &'a EffectInfo<'a>,
    /// Map effect canonical name → ops sorted alphabetically. Seeded from
    /// `EffectInfo::effect_ops` so imported effects are visible, then extended
    /// by scanning local `Decl::EffectDef` declarations in the input program.
    pub(crate) effect_ops: HashMap<String, Vec<String>>,
    /// `(effect, op)` → source parameter count, populated from local effect
    /// declarations. Used to distinguish eta-reduced op references (`ping!`
    /// as a callback) from immediate performs after ANF has lifted them.
    pub(crate) effect_op_param_counts: HashMap<(String, String), usize>,
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
    /// Local variable names known to hold handler values whose arms are
    /// dynamic, but whose handled effects are known from the type
    /// (e.g. `let h = if cond then a else b` where both branches handle `Log`).
    /// Keyed by variable name, value is canonicalized effect names.
    pub(crate) local_handler_effects: HashMap<String, Vec<String>>,
    /// Fresh MVar id counter — program-wide unique.
    pub(crate) fresh_mvar: u32,
}

impl<'a> Translator<'a> {
    fn new(p: &'a ast::Program, r: &'a ResolutionMap, e: &'a EffectInfo<'a>) -> Self {
        let mut effect_ops: HashMap<String, Vec<String>> = HashMap::new();
        let mut effect_op_param_counts: HashMap<(String, String), usize> = HashMap::new();
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
                    for op in operations {
                        effect_op_param_counts
                            .insert((name.clone(), op.node.name.clone()), op.node.params.len());
                    }
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
            effect_op_param_counts,
            handler_decls,
            local_static_handlers: HashMap::new(),
            local_handler_effects: HashMap::new(),
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

    /// Build a map of handler name → pre-translated handler arms for
    /// handler-as-value lowering. Called after the main translation pass.
    /// Skips handlers only if their effect metadata is missing from the
    /// entry-point `EffectInfo` table.
    pub(crate) fn build_handler_value_map(&mut self) -> HandlerValueMap {
        use crate::codegen::monadic::ir::HandlerValueInfo;
        let decls: Vec<(String, HandlerBody)> = self.handler_decls.clone().into_iter().collect();
        let mut map = HandlerValueMap::new();
        for (name, body) in &decls {
            let mut effects: Vec<String> = Vec::new();
            for effect_ref in &body.effects {
                let ename = effect_ref.name.clone();
                if !effects.contains(&ename) {
                    effects.push(ename);
                }
            }
            let canonical_effects: Vec<String> = effects
                .iter()
                .map(|e| self.canonical_effect_name(e))
                .collect();
            // Defensive guard: if the entry-point metadata omitted one of
            // the handler's effects, leave it out of the handler-value map
            // instead of building an op tuple with unknown indexes.
            if canonical_effects
                .iter()
                .any(|e| !self.effect_ops.contains_key(e))
            {
                continue;
            }
            let arms = body
                .arms
                .iter()
                .map(|a| self.translate_handler_arm(&a.node, &canonical_effects))
                .collect();
            let return_clause = body
                .return_clause
                .as_ref()
                .map(|a| self.translate_handler_arm(a, &canonical_effects));
            map.insert(
                name.clone(),
                HandlerValueInfo {
                    effects: canonical_effects,
                    arms,
                    return_clause,
                },
            );
        }
        map
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
    /// A non-empty `effect` not present in `effect_ops` indicates that the
    /// entry-point metadata omitted an effect definition that typechecking
    /// nevertheless resolved for a perform site.
    pub(crate) fn op_index(&self, effect: &str, op: &str) -> u32 {
        if effect.is_empty() {
            return 1;
        }
        let Some(ops) = self.effect_ops.get(effect) else {
            panic!(
                "monadic::translate: effect '{}' not visible to the translator (looking up op \
                 '{}'). The entry-point EffectInfo.effect_ops table is incomplete.",
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
                guard,
                body,
                span,
                ..
            } => {
                // Register `Handler E …`-typed parameters as dynamic handler
                // names for this function's body. The typechecker populates
                // `let_handler_effects` keyed by parameter NodeId
                // ([check_decl.rs] near `bind_pattern`); without this,
                // `with h` over a parameter would fall through with empty
                // effects and skip evidence install.
                let saved_handler_effects = self.local_handler_effects.clone();
                for pat in params {
                    if let ast::Pat::Var {
                        id: pat_id,
                        name: pname,
                        ..
                    } = pat
                        && let Some(effects) = self.effect_info.let_handler_effects.get(pat_id)
                    {
                        let canonical: Vec<String> = effects
                            .iter()
                            .map(|e| self.canonical_effect_name(e))
                            .collect();
                        if !canonical.is_empty() {
                            self.local_handler_effects.insert(pname.clone(), canonical);
                        }
                    }
                }
                let guard = guard.as_ref().map(|g| self.translate_expr(g));
                let body = self.translate_expr(body);
                self.local_handler_effects = saved_handler_effects;
                MDecl::FunBinding(MFunBinding {
                    id: *id,
                    name: name.clone(),
                    name_span: *name_span,
                    params: params.clone(),
                    guard,
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
/// `(var, value, optional destructure_pat)` triple, applied from last to
/// first (closest binder is at the front of `bindings` when iterated; we
/// reverse internally so the first pushed binding is the outermost).
/// Callers push in source order.
///
/// When `destructure_pat` is `Some(p)`, the bound `var` is the synthetic
/// `__pat` binder and the original source pattern needs to match against
/// it. We wrap the body in a `Case` arm so the pattern's sub-vars come
/// into scope for everything after this `Bind`. The `Case` has a single
/// arm — the typechecker has already proven exhaustiveness for
/// irrefutable let-patterns; any non-matching value would have been
/// rejected upstream.
pub(crate) fn wrap_binds(
    bindings: Vec<(MVar, MExpr, Option<crate::ast::Pat>)>,
    tail: MExpr,
) -> MExpr {
    let mut acc = tail;
    for (var, value, destructure_pat) in bindings.into_iter().rev() {
        let mode = bind_mode_for(&var, &value);
        let body = if let Some(pat) = destructure_pat {
            MExpr::Case {
                scrutinee: crate::codegen::monadic::ir::Atom::Var {
                    name: var.clone(),
                    source: crate::ast::NodeId::fresh(),
                },
                arms: vec![crate::codegen::monadic::ir::MArm {
                    pattern: pat,
                    guard: None,
                    body: acc,
                    span: crate::token::Span { start: 0, end: 0 },
                }],
                source: crate::ast::NodeId::fresh(),
            }
        } else {
            acc
        };
        acc = MExpr::Bind {
            var,
            value: Box::new(value),
            body: Box::new(body),
            mode,
        };
    }
    acc
}

fn bind_mode_for(var: &MVar, value: &MExpr) -> BindMode {
    if var.name.starts_with("__anf_") && needs_value_position_delimiter(value) {
        BindMode::ValuePosition
    } else {
        BindMode::Sequence
    }
}

fn needs_value_position_delimiter(value: &MExpr) -> bool {
    match value {
        MExpr::Yield { .. } | MExpr::Resume { .. } | MExpr::With { .. } => true,
        MExpr::Bind { value, body, .. } | MExpr::Let { value, body, .. } => {
            needs_value_position_delimiter(value) || needs_value_position_delimiter(body)
        }
        MExpr::Ensure { body, cleanup } => {
            needs_value_position_delimiter(body) || needs_value_position_delimiter(cleanup)
        }
        MExpr::If {
            then_branch,
            else_branch,
            ..
        } => {
            needs_value_position_delimiter(then_branch)
                || needs_value_position_delimiter(else_branch)
        }
        MExpr::Case { arms, .. } | MExpr::Receive { arms, .. } => arms
            .iter()
            .any(|arm| needs_value_position_delimiter(&arm.body)),
        MExpr::App {
            head:
                crate::codegen::monadic::ir::Atom::Lambda {
                    body: lambda_body, ..
                },
            ..
        } => needs_value_position_delimiter(lambda_body),
        MExpr::HandlerValue {
            arms,
            return_clause,
            ..
        } => {
            arms.iter()
                .any(|arm| needs_value_position_delimiter(&arm.body))
                || return_clause
                    .as_ref()
                    .is_some_and(|arm| needs_value_position_delimiter(&arm.body))
        }
        MExpr::Pure(_)
        | MExpr::App { .. }
        | MExpr::ForeignCall { .. }
        | MExpr::BinOp { .. }
        | MExpr::UnaryMinus { .. }
        | MExpr::FieldAccess { .. }
        | MExpr::RecordUpdate { .. }
        | MExpr::DictMethodAccess { .. }
        | MExpr::BitString { .. }
        | MExpr::LetFun { .. } => false,
    }
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
