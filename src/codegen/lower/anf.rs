//! Value-normal form at the lowering roots.
//!
//! Every body the lowerer starts on (a function clause or its guard, a
//! dictionary method, a handler arm or return clause, a `finally` block, an
//! inlined helper or handler arm) passes through `effect_normal_body`
//! first. A body that already satisfies the position rule in
//! `codegen::effect_position` (every operand is a value) is lowered as it
//! is. Any other body is normalized by `normalize::normalize_body` and
//! checked again; a violation that survives is a compiler bug and stops
//! compilation. `lower_operand` checks the same rule again where an operand
//! is lowered, so a body that reached the lowerer without passing through
//! here stops compilation too.
//!
//! This runs after call classification on purpose: which calls perform
//! effects is only known from the frozen plan, and the plan's entries are
//! keyed by node ids that normalization keeps.

use std::borrow::Cow;

use super::Lowerer;
use super::util::collect_effect_call;
use crate::ast::{Expr, ExprKind};
use crate::codegen::cerl::CExpr;
use crate::codegen::effect_position::{self, Violation};
use crate::codegen::normalize;

impl<'a> Lowerer<'a> {
    /// Whether `expr` performs an effect by itself, for the position rule:
    /// a call the plan classified CPS, an applied operation, a nullary
    /// operation, a `with`, a `resume`.
    pub(super) fn performs_effect(&self, expr: &Expr) -> bool {
        match &expr.kind {
            ExprKind::App { .. } => {
                collect_effect_call(expr).is_some() || self.expr_is_effectful_call(expr)
            }
            ExprKind::EffectCall { .. } => self.nullary_operation(expr).is_some(),
            ExprKind::With { .. } | ExprKind::Resume { .. } => true,
            _ => false,
        }
    }

    /// The name and qualifier of `expr` if it is an operation written with
    /// no arguments that performs where it stands: an operation that takes
    /// no parameters (`number!`). An operation that takes parameters is,
    /// unapplied, a reference to it as a function value.
    pub(super) fn nullary_operation<'e>(&self, expr: &'e Expr) -> Option<(&'e str, Option<&'e str>)> {
        let ExprKind::EffectCall {
            name, qualifier, ..
        } = &expr.kind
        else {
            return None;
        };
        let qualifier = qualifier.as_deref();
        let takes_parameters = self
            .resolved_effect_call_name(expr.id, name, qualifier)
            .and_then(|effect| self.effect_defs.get(&effect)?.ops.get(name.as_str()))
            .is_some_and(|op| op.source_param_count > 0);
        (!takes_parameters).then_some((name.as_str(), qualifier))
    }

    pub(super) fn effect_position_violations(&self, body: &Expr) -> Vec<Violation> {
        let mut violations = Vec::new();
        effect_position::check_body(body, &|node| self.performs_effect(node), &mut violations);
        violations
    }

    fn describe_violation(&self, violation: &Violation, root: &str) -> String {
        let location = match &self.source_info {
            Some(info) => format!("{}:{}", info.file, info.line_number(&violation.span)),
            None => format!("offset {}", violation.span.start),
        };
        format!(
            "{} as an operand of {} in {} of {}.{} at {}",
            violation.construct,
            violation.operand_of,
            root,
            self.current_semantic_module_name(),
            self.current_function,
            location
        )
    }

    /// `expr` is about to be lowered as a plain value, as an operand of
    /// `operand_of`. If it is not a value, the body it is in was not
    /// normalized (it did not pass through `effect_normal_body`); stop
    /// instead of lowering it where it stands (with an identity
    /// continuation, if it performs).
    pub(super) fn assert_operand(&self, expr: &Expr, operand_of: &str) {
        if self.in_beam_guard {
            return;
        }
        if !effect_position::is_operand(expr, &|node| self.performs_effect(node)) {
            panic!(
                "internal compiler error: {} reached lowering as an operand of {operand_of} \
                 in {}.{}: its body was not normalized",
                effect_position::construct_name(expr, &|node| self.performs_effect(node)),
                self.current_semantic_module_name(),
                self.current_function,
            );
        }
    }

    /// Lower a guard into guard position. A BEAM guard expression is not
    /// normalized (its operators nest), so the operand rule is off inside
    /// one.
    pub(super) fn lower_guard(&mut self, guard: &Expr) -> CExpr {
        let saved = std::mem::replace(
            &mut self.in_beam_guard,
            effect_position::is_guard_safe(guard),
        );
        let lowered = self.lower_expr(guard);
        self.in_beam_guard = saved;
        lowered
    }

    /// Lower an operand of `operand_of` as a plain value.
    pub(super) fn lower_operand(&mut self, expr: &Expr, operand_of: &str) -> CExpr {
        self.assert_operand(expr, operand_of);
        self.lower_expr(expr)
    }

    /// The guard the lowerer is about to lower: as written when it is a
    /// BEAM guard expression, otherwise a body in value-normal form.
    pub(super) fn effect_normal_guard<'e>(
        &mut self,
        guard: &'e Expr,
        root: &'static str,
    ) -> Cow<'e, Expr> {
        if effect_position::is_guard_safe(guard) {
            Cow::Borrowed(guard)
        } else {
            self.effect_normal_body(guard, root)
        }
    }

    /// The body the lowerer is about to lower, in value-normal form.
    /// `root` names the kind of body for diagnostics.
    pub(super) fn effect_normal_body<'e>(
        &mut self,
        body: &'e Expr,
        root: &'static str,
    ) -> Cow<'e, Expr> {
        if self.effect_position_violations(body).is_empty() {
            return Cow::Borrowed(body);
        }
        let mut counter = self.anf_counter;
        let normalized =
            normalize::normalize_body(body, &|node| self.performs_effect(node), &mut counter);
        self.anf_counter = counter;
        if let Some(violation) = self.effect_position_violations(&normalized).first() {
            panic!(
                "internal compiler error: effect normalization left {}",
                self.describe_violation(violation, root)
            );
        }
        Cow::Owned(normalized)
    }
}
