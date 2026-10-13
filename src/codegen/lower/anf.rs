//! Effect-normal form at the lowering roots.
//!
//! Every body the lowerer starts on (a function clause or its guard, a
//! dictionary method, a handler arm or return clause, a `finally` block, an
//! inlined helper) passes through `effect_normal_body` first. A body that
//! already satisfies the position rule in `codegen::effect_position` is
//! lowered as it is. Any other body is normalized by
//! `normalize::normalize_body` and checked again; a violation that survives
//! is a compiler bug and stops compilation.
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
    /// a call the plan classified CPS, an applied operation, a `with`, a
    /// `resume`.
    ///
    /// A nullary operation (`number!`, a bare `EffectCall`) performs too but
    /// is not counted: no lowering rule gives it the rest of a block as its
    /// continuation yet, so moving it into a `let` would change nothing.
    pub(super) fn performs_effect(&self, expr: &Expr) -> bool {
        match &expr.kind {
            ExprKind::App { .. } => {
                collect_effect_call(expr).is_some() || self.expr_is_effectful_call(expr)
            }
            ExprKind::With { .. } | ExprKind::Resume { .. } => true,
            _ => false,
        }
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
    /// `operand_of`. If it needs a continuation, the body it is in was not
    /// normalized (it did not pass through `effect_normal_body`); stop
    /// instead of lowering it with an identity continuation.
    pub(super) fn assert_operand(&self, expr: &Expr, operand_of: &str) {
        if effect_position::needs_continuation(expr, &|node| self.performs_effect(node)) {
            panic!(
                "internal compiler error: {} reached lowering as an operand of {operand_of} \
                 in {}.{}: its body was not effect-normalized",
                effect_position::construct_name(expr, &|node| self.performs_effect(node)),
                self.current_semantic_module_name(),
                self.current_function,
            );
        }
    }

    /// Lower an operand of `operand_of` as a plain value.
    pub(super) fn lower_operand(&mut self, expr: &Expr, operand_of: &str) -> CExpr {
        self.assert_operand(expr, operand_of);
        self.lower_expr_value(expr)
    }

    /// The body the lowerer is about to lower, in effect-normal form.
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
