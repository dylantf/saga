//! Handler-classification logic.
//!
//! Decides Static vs Dynamic at translation time so the direct-call rewrite
//! in effect optimization can fire on the static variant without re-deciding.

use super::Translator;
use crate::ast::{self, EffectRef, Handler, HandlerArm, HandlerBody, HandlerItem, NodeId};
use crate::codegen::monadic::ir::{Atom, EffectOpRef, MExpr, MHandler, MHandlerArm, MVar};
use crate::token::Span;
use crate::typechecker::ResolvedValue;

impl<'a> Translator<'a> {
    /// Translate the handler expression in `with body handler`.
    pub(crate) fn translate_handler(&mut self, h: &Handler, site_span: Span) -> MHandler {
        match h {
            Handler::Named(named) => self.handler_for_named(&named.name, named.id, site_span),
            Handler::Inline { items, .. } => self.handler_from_inline_items(items, site_span),
        }
    }

    /// Resolve a `with <name>` reference. If the name binds a top-level
    /// handler decl or a statically-known local alias, produce a `Static`
    /// handler with the arms embedded. Otherwise fall back to a `Dynamic`
    /// handler whose op tuple is carried as a runtime value.
    fn handler_for_named(&mut self, name: &str, ref_id: NodeId, site_span: Span) -> MHandler {
        let resolved_name = self.resolved_handler_name(ref_id, name);
        if let Some((static_name, body)) = self.lookup_handler_body(name, &resolved_name) {
            return self.static_from_body(&static_name, &body, ref_id);
        }
        if let Some((static_name, body)) = self.lookup_local_static_handler(name, &resolved_name) {
            return self.static_from_body(&static_name, &body, ref_id);
        }
        // Dynamic — runtime value held in `name`.
        // Extract the effect tag from the typechecker's handler registry so
        // the lowerer can install evidence under the correct tag.
        let effects = self.resolve_dynamic_handler_effects(name, &resolved_name);
        MHandler::Dynamic {
            effects,
            op_tuple: Atom::Var {
                name: MVar {
                    name: resolved_name,
                    id: self.next_mvar_id(),
                },
                source: ref_id,
            },
            return_lambda: None,
            source: site_span_to_node_id(site_span, ref_id),
        }
    }

    /// Build a Static handler from an inline `with { items }` block.
    ///
    /// An inline block may mix:
    ///   - `HandlerItem::Arm` (direct arm)
    ///   - `HandlerItem::Return` (return clause)
    ///   - `HandlerItem::Named` (composes another named handler)
    ///
    /// If every `Named` item resolves to a static handler we can merge arms
    /// from all sources into one flat `Static`. Otherwise (any dynamic
    /// reference), fall back to `Dynamic` keyed on the first named
    /// reference's NodeId so the lowerer can still emit a runtime op-tuple.
    fn handler_from_inline_items(
        &mut self,
        items: &[ast::Annotated<HandlerItem>],
        site_span: Span,
    ) -> MHandler {
        // First pass: classify.
        let mut arms_src: Vec<HandlerArm> = Vec::new();
        let mut return_clause: Option<HandlerArm> = None;
        let mut effects: Vec<String> = Vec::new();
        let mut any_dynamic: Option<(String, NodeId)> = None;
        let mut native_handlers: Vec<MHandler> = Vec::new();

        for ann in items {
            match &ann.node {
                HandlerItem::Arm(arm) => {
                    arms_src.push(arm.clone());
                }
                HandlerItem::Return(arm) => {
                    return_clause = Some(arm.clone());
                }
                HandlerItem::Named(named) => {
                    let resolved_name = self.resolved_handler_name(named.id, &named.name);
                    if let Some((static_name, body)) =
                        self.lookup_handler_body(&named.name, &resolved_name)
                    {
                        if let Some(native) = self.native_from_body(&static_name, &body, named.id) {
                            native_handlers.push(native);
                            merge_body_effects(&body, &mut effects);
                            continue;
                        }
                        merge_body_effects(&body, &mut effects);
                        for ann_arm in &body.arms {
                            arms_src.push(ann_arm.node.clone());
                        }
                        if return_clause.is_none()
                            && let Some(r) = &body.return_clause
                        {
                            return_clause = Some((**r).clone());
                        }
                    } else if let Some((static_name, body)) =
                        self.lookup_local_static_handler(&named.name, &resolved_name)
                    {
                        if let Some(native) = self.native_from_body(&static_name, &body, named.id) {
                            native_handlers.push(native);
                            merge_body_effects(&body, &mut effects);
                            continue;
                        }
                        merge_body_effects(&body, &mut effects);
                        for ann_arm in &body.arms {
                            arms_src.push(ann_arm.node.clone());
                        }
                        if return_clause.is_none()
                            && let Some(r) = &body.return_clause
                        {
                            return_clause = Some((**r).clone());
                        }
                    } else if any_dynamic.is_none() {
                        any_dynamic = Some((resolved_name, named.id));
                    }
                }
            }
        }

        if let Some((name, ref_id)) = any_dynamic {
            let effects = self.resolve_dynamic_handler_effects(&name, &name);
            return MHandler::Dynamic {
                effects,
                op_tuple: Atom::Var {
                    name: MVar {
                        name,
                        id: self.next_mvar_id(),
                    },
                    source: ref_id,
                },
                return_lambda: None,
                source: ref_id,
            };
        }

        let canonical_effects: Vec<String> = effects
            .iter()
            .map(|e| self.canonical_effect_name(e))
            .collect();
        let arms: Vec<MHandlerArm> = arms_src
            .iter()
            .map(|a| self.translate_handler_arm(a, &canonical_effects))
            .collect();
        let return_clause = return_clause
            .as_ref()
            .map(|a| self.translate_handler_arm(a, &canonical_effects));

        let static_part = if !arms.is_empty() || return_clause.is_some() {
            Some(MHandler::Static {
                effects: canonical_effects.clone(),
                arms,
                return_clause,
                source: site_span_to_node_id(site_span, NodeId::fresh()),
            })
        } else {
            None
        };

        let mut handlers = native_handlers;
        if let Some(static_handler) = static_part {
            handlers.push(static_handler);
        }

        match handlers.len() {
            0 => MHandler::Static {
                effects: canonical_effects.clone(),
                arms: Vec::new(),
                return_clause: None,
                source: site_span_to_node_id(site_span, NodeId::fresh()),
            },
            1 => handlers.pop().unwrap(),
            _ => MHandler::Composite {
                handlers,
                source: site_span_to_node_id(site_span, NodeId::fresh()),
            },
        }
    }

    /// Build a Static handler from a known `HandlerBody`.
    fn static_from_body(&mut self, name: &str, body: &HandlerBody, source: NodeId) -> MHandler {
        if let Some(native) = self.native_from_body(name, body, source) {
            return native;
        }
        let mut effects: Vec<String> = Vec::new();
        merge_body_effects(body, &mut effects);
        // Canonicalize the handler's declared effects via `effect_ops` so the
        // lowerer's With-site evidence tags match the canonical names used
        // by `Yield`'s `find_evidence` lookups (the typechecker's resolution
        // is authoritative on canonical naming).
        let canonical_effects: Vec<String> = effects
            .iter()
            .map(|e| self.canonical_effect_name(e))
            .collect();
        let arms = body
            .arms
            .iter()
            .map(|a| self.translate_handler_arm(&a.node, &canonical_effects))
            .collect();
        let return_clause = body
            .return_clause
            .as_ref()
            .map(|a| self.translate_handler_arm(a, &canonical_effects));
        MHandler::Static {
            effects: canonical_effects,
            arms,
            return_clause,
            source,
        }
    }

    fn native_from_body(&self, name: &str, body: &HandlerBody, source: NodeId) -> Option<MHandler> {
        if !body.arms.is_empty() || body.return_clause.is_some() || !is_native_handler_name(name) {
            return None;
        }
        let mut effects: Vec<String> = Vec::new();
        merge_body_effects(body, &mut effects);
        let canonical_effects: Vec<String> = effects
            .iter()
            .map(|e| self.canonical_effect_name(e))
            .collect();
        Some(MHandler::Native {
            effects: canonical_effects,
            handler: name.to_string(),
            source,
        })
    }

    pub(crate) fn translate_handler_arm(
        &mut self,
        arm: &HandlerArm,
        handler_effects: &[String],
    ) -> MHandlerArm {
        let op = self.resolve_handler_arm_op(arm, handler_effects);
        MHandlerArm {
            id: arm.id,
            op,
            params: arm
                .params
                .iter()
                .map(|p| self.canonicalize_pat_constructors(p))
                .collect(),
            body: Box::new(self.translate_expr(&arm.body)),
            finally_block: arm
                .finally_block
                .as_ref()
                .map(|b| Box::new(self.translate_expr(b))),
            span: arm.span,
        }
    }

    /// Pre-resolve a handler arm's op via `EffectInfo.handler_arms` (the
    /// typechecker's authoritative map). Falls back to the surrounding
    /// handler's `for <Effect>` clause when the arm isn't in the map —
    /// which happens for arms whose NodeIds come from an imported module
    /// (their `handler_arms` resolution lives in that module's
    /// `CheckResult`, not the entry-point's narrowed view).
    fn resolve_handler_arm_op(&self, arm: &HandlerArm, handler_effects: &[String]) -> EffectOpRef {
        if let Some(resolved) = self.effect_info.handler_arms.get(&arm.id) {
            let op_index = self.op_index(&resolved.effect, &resolved.op);
            return EffectOpRef {
                effect: resolved.effect.clone(),
                op: resolved.op.clone(),
                op_index,
            };
        }
        // Fallback: find which of the handler's `for <Effect>` declarations
        // owns this op by checking `effect_ops`. If only one effect is in
        // scope, it must be the one; otherwise look for an op-name match.
        let bare_qualifier = arm.qualifier.clone().unwrap_or_default();
        let effect = if !bare_qualifier.is_empty() {
            self.canonical_effect_name(&bare_qualifier)
        } else {
            handler_effects
                .iter()
                .find(|e| {
                    self.effect_ops
                        .get(*e)
                        .is_some_and(|ops| ops.iter().any(|n| n == &arm.op_name))
                })
                .cloned()
                .unwrap_or_default()
        };
        let op_index = self.op_index(&effect, &arm.op_name);
        EffectOpRef {
            effect,
            op: arm.op_name.clone(),
            op_index,
        }
    }

    /// Resolve the effect names for a dynamic handler variable by looking
    /// up the handler name in `EffectInfo.handler_effects` (populated from
    /// the typechecker's handler registry). Returns canonicalized effect
    /// names so `insert_canonical` tags match `find_evidence` lookups.
    fn resolve_dynamic_handler_effects(&self, name: &str, resolved_name: &str) -> Vec<String> {
        if let Some(effects) = self.local_handler_effects.get(name) {
            return effects.clone();
        }
        if let Some(effects) = self.local_handler_effects.get(resolved_name) {
            return effects.clone();
        }
        if let Some(effects) = self
            .effect_info
            .handler_effects
            .get(resolved_name)
            .or_else(|| self.effect_info.handler_effects.get(name))
            .or_else(|| {
                resolved_name
                    .rsplit('.')
                    .next()
                    .and_then(|bare| self.effect_info.handler_effects.get(bare))
            })
        {
            return effects
                .iter()
                .map(|e| self.canonical_effect_name(e))
                .collect();
        }
        Vec::new()
    }

    fn resolved_handler_name(&self, ref_id: NodeId, source_name: &str) -> String {
        match self.effect_info.handler_refs.get(&ref_id) {
            Some(ResolvedValue::Local { name, .. }) => name.clone(),
            Some(ResolvedValue::Global { lookup_name }) => lookup_name.clone(),
            None => source_name.to_string(),
        }
    }

    fn lookup_handler_body(
        &self,
        source_name: &str,
        resolved_name: &str,
    ) -> Option<(String, HandlerBody)> {
        self.handler_decls
            .get(source_name)
            .map(|body| (source_name.to_string(), body.clone()))
            .or_else(|| {
                self.handler_decls
                    .get(resolved_name)
                    .map(|body| (resolved_name.to_string(), body.clone()))
            })
            .or_else(|| {
                resolved_name.rsplit('.').next().and_then(|bare| {
                    self.handler_decls
                        .get(bare)
                        .map(|body| (bare.to_string(), body.clone()))
                })
            })
    }

    fn lookup_local_static_handler(
        &self,
        source_name: &str,
        resolved_name: &str,
    ) -> Option<(String, HandlerBody)> {
        self.local_static_handlers
            .get(source_name)
            .and_then(|body| body.clone().map(|body| (source_name.to_string(), body)))
            .or_else(|| {
                self.local_static_handlers
                    .get(resolved_name)
                    .and_then(|body| body.clone().map(|body| (resolved_name.to_string(), body)))
            })
    }

    /// Map a bare effect name (e.g. `Stdio`) to its canonical form (e.g.
    /// `Std.IO.Stdio`) by scanning `effect_ops` for a dotted key whose
    /// last segment matches. Returns the input unchanged if no canonical
    /// alias is found (already-canonical names pass through).
    pub(crate) fn canonical_effect_name(&self, bare: &str) -> String {
        if bare.contains('.') {
            return bare.to_string();
        }
        for key in self.effect_ops.keys() {
            if key.contains('.')
                && let Some(last) = key.rsplit('.').next()
                && last == bare
            {
                return key.clone();
            }
        }
        bare.to_string()
    }
}

fn merge_body_effects(body: &HandlerBody, out: &mut Vec<String>) {
    for effect_ref in &body.effects {
        let name = effect_ref_name(effect_ref);
        if !out.contains(&name) {
            out.push(name);
        }
    }
}

fn effect_ref_name(r: &EffectRef) -> String {
    r.name.clone()
}

fn is_native_handler_name(name: &str) -> bool {
    matches!(
        name.rsplit('.').next().unwrap_or(name),
        "beam_ref" | "ets_ref" | "beam_actor" | "atomic_ref" | "beam_vec"
    )
}

/// The `With` MExpr variant carries the with-site's NodeId via the calling
/// `translate_expr`. `MHandler::Static.source` wants a NodeId we can hand
/// back to the optimizer/lowerer; we prefer the handler-reference site, and
/// only synthesize when none is available (inline blocks with no named ref).
fn site_span_to_node_id(_span: Span, fallback: NodeId) -> NodeId {
    fallback
}

// Suppress unused warnings when these helpers are not exercised in the
// minimal build configuration.
#[allow(dead_code)]
fn _unused_marker(_: MExpr) {}
