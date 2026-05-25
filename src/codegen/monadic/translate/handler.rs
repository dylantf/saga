//! Handler-classification logic.
//!
//! Decides Static vs Dynamic at translation time so the direct-call rewrite
//! in effect optimization can fire on the static variant without re-deciding.

use super::Translator;
use crate::ast::{self, EffectRef, Handler, HandlerArm, HandlerBody, HandlerItem, NodeId};
use crate::codegen::monadic::ir::{Atom, EffectOpRef, MExpr, MHandler, MHandlerArm, MVar};
use crate::token::Span;

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
        if let Some(body) = self.handler_decls.get(name).cloned() {
            return self.static_from_body(&body, ref_id);
        }
        if let Some(Some(body)) = self.local_static_handlers.get(name).cloned() {
            return self.static_from_body(&body, ref_id);
        }
        // Dynamic — runtime value held in `name`.
        MHandler::Dynamic {
            effects: Vec::new(),
            op_tuple: Atom::Var {
                name: MVar {
                    name: name.to_string(),
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

        for ann in items {
            match &ann.node {
                HandlerItem::Arm(arm) => {
                    arms_src.push(arm.clone());
                }
                HandlerItem::Return(arm) => {
                    return_clause = Some(arm.clone());
                }
                HandlerItem::Named(named) => {
                    if let Some(body) = self.handler_decls.get(&named.name).cloned() {
                        merge_body_effects(&body, &mut effects);
                        for ann_arm in &body.arms {
                            arms_src.push(ann_arm.node.clone());
                        }
                        if return_clause.is_none()
                            && let Some(r) = &body.return_clause
                        {
                            return_clause = Some((**r).clone());
                        }
                    } else if let Some(Some(body)) =
                        self.local_static_handlers.get(&named.name).cloned()
                    {
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
                        any_dynamic = Some((named.name.clone(), named.id));
                    }
                }
            }
        }

        if let Some((name, ref_id)) = any_dynamic {
            return MHandler::Dynamic {
                effects: Vec::new(),
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

        let canonical_effects: Vec<String> =
            effects.iter().map(|e| self.canonical_effect_name(e)).collect();
        let arms = arms_src
            .iter()
            .map(|a| self.translate_handler_arm(a, &canonical_effects))
            .collect();
        let return_clause = return_clause
            .as_ref()
            .map(|a| self.translate_handler_arm(a, &canonical_effects));

        MHandler::Static {
            effects: canonical_effects,
            arms,
            return_clause,
            source: site_span_to_node_id(site_span, NodeId::fresh()),
        }
    }

    /// Build a Static handler from a known `HandlerBody`.
    fn static_from_body(&mut self, body: &HandlerBody, source: NodeId) -> MHandler {
        let mut effects: Vec<String> = Vec::new();
        merge_body_effects(body, &mut effects);
        // Canonicalize the handler's declared effects via `effect_ops` so the
        // lowerer's With-site evidence tags match the canonical names used
        // by `Yield`'s `find_evidence` lookups (the typechecker's resolution
        // is authoritative on canonical naming).
        let canonical_effects: Vec<String> =
            effects.iter().map(|e| self.canonical_effect_name(e)).collect();
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

    fn translate_handler_arm(
        &mut self,
        arm: &HandlerArm,
        handler_effects: &[String],
    ) -> MHandlerArm {
        let op = self.resolve_handler_arm_op(arm, handler_effects);
        MHandlerArm {
            id: arm.id,
            op,
            params: arm.params.clone(),
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
    fn resolve_handler_arm_op(
        &self,
        arm: &HandlerArm,
        handler_effects: &[String],
    ) -> EffectOpRef {
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

    /// Map a bare effect name (e.g. `Stdio`) to its canonical form (e.g.
    /// `Std.IO.Stdio`) by scanning `effect_ops` for a dotted key whose
    /// last segment matches. Returns the input unchanged if no canonical
    /// alias is found (already-canonical names pass through).
    fn canonical_effect_name(&self, bare: &str) -> String {
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
