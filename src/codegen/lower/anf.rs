//! Effect positions at the lowering roots.
//!
//! Every body the lowerer starts on (a function clause, a dictionary
//! method, a handler arm or return clause, a `finally` block, an inlined
//! helper) passes through `effect_normal_body` first. It checks the body
//! against the position rule in `codegen::effect_position`.

use std::borrow::Cow;
use std::sync::OnceLock;

use super::Lowerer;
use super::util::collect_effect_call;
use crate::ast::{Expr, ExprKind};
use crate::codegen::effect_position::{self, Violation};

/// `SAGA_ANF_REPORT=1`: print every position violation to stderr instead of
/// acting on it.
fn report_mode() -> bool {
    static ON: OnceLock<bool> = OnceLock::new();
    *ON.get_or_init(|| std::env::var_os("SAGA_ANF_REPORT").is_some())
}

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

    /// The body the lowerer is about to lower, in effect-normal form.
    /// `root` names the kind of body for diagnostics.
    pub(super) fn effect_normal_body<'e>(
        &mut self,
        body: &'e Expr,
        root: &'static str,
    ) -> Cow<'e, Expr> {
        if report_mode() {
            for violation in self.effect_position_violations(body) {
                eprintln!("anf-report: {}", self.describe_violation(&violation, root));
            }
        }
        Cow::Borrowed(body)
    }
}
