use crate::ast::{Expr, ExprKind};
use crate::codegen::cerl::CExpr;
use crate::codegen::runtime_shape::{CallableAbi, EvidenceAbi};

use super::Lowerer;

impl<'a> Lowerer<'a> {
    pub(super) fn cps_function_shape_from_type(
        &self,
        ty: &crate::typechecker::Type,
    ) -> Option<EvidenceAbi> {
        CallableAbi::from_type(ty, |effects| self.canonicalize_effects(effects)).cps_evidence()
    }

    pub(super) fn lower_call_args(
        &mut self,
        args: &[&Expr],
    ) -> (Vec<String>, Vec<(String, CExpr)>) {
        let mut arg_vars: Vec<String> = Vec::new();
        let mut bindings: Vec<(String, CExpr)> = Vec::new();
        for arg in args {
            let v = self.fresh();
            self.assert_operand(arg, "a call");
            let ce = self
                .lower_eta_reduced_effect_expr(arg)
                .unwrap_or_else(|| self.lower_expr_value(arg));
            arg_vars.push(v.clone());
            bindings.push((v, ce));
        }
        (arg_vars, bindings)
    }
    pub(super) fn lower_eta_reduced_effect_op_ref(
        &mut self,
        node_id: crate::ast::NodeId,
        op_name: &str,
        qualifier: Option<&str>,
    ) -> Option<CExpr> {
        let effect_name = self.resolved_effect_call_name(node_id, op_name, qualifier)?;
        let _ = self.effect_defs.get(&effect_name)?.ops.get(op_name)?;
        let applied_effect = self
            .check_result
            .effect_at_node
            .get(&node_id)
            .map(crate::typechecker::applied_effect_key)
            .unwrap_or_else(|| effect_name.clone());
        let applied_effect = self.canonicalize_effect(&applied_effect);
        let op_info = self
            .effect_defs
            .get(&effect_name)?
            .ops
            .get(op_name)?
            .clone();

        // A nullary effect op (`fun now : Int`) can't be an eta-reduced *reference*
        // that still awaits arguments -- `now!` is always a saturated perform.
        // Without this, the zero-param loop below would emit `fun () -> perform`,
        // thunking the perform instead of running it. Fall through to
        // `lower_effect_call`, which performs immediately.
        if op_info.source_param_count == 0 {
            return None;
        }

        let mut params = Vec::new();
        let mut runtime_args = Vec::new();
        for idx in 0..op_info.source_param_count {
            let param = self.fresh();
            if op_info.runtime_param_positions.contains(&idx) {
                runtime_args.push(CExpr::Var(param.clone()));
            }
            params.push(param);
        }

        // The typechecker attributes the operation's effect to the place the
        // reference is written, and gives the reference the operation's own
        // function type. So the closure captures the handler in scope here.
        // If that type is effectful (the operation has its own `needs`), the
        // value is a tagged closure and the handler resumes into the
        // caller's continuation; otherwise it is a bare fun.
        let handler_expr = self.evidence_op_lookup(&applied_effect, op_name);
        if self.value_repr_of(node_id) == Some(crate::codegen::runtime_shape::ValueRepr::Tagged) {
            let return_k = "_ReturnK".to_string();
            params.push(self.fresh());
            params.push(return_k.clone());
            runtime_args.push(CExpr::Var(return_k));
            return Some(super::tagged::tag_cps(CExpr::Fun(
                params,
                Box::new(CExpr::Apply(Box::new(handler_expr), runtime_args)),
            )));
        }
        let return_value = self.fresh();
        runtime_args.push(CExpr::Fun(
            vec![return_value.clone()],
            Box::new(CExpr::Var(return_value)),
        ));
        Some(CExpr::Fun(
            params,
            Box::new(CExpr::Apply(Box::new(handler_expr), runtime_args)),
        ))
    }

    pub(super) fn lower_eta_reduced_effect_expr(&mut self, expr: &Expr) -> Option<CExpr> {
        let mut args = Vec::new();
        let mut current = expr;
        let (effect_call_id, op_name, qualifier) = loop {
            match &current.kind {
                ExprKind::App { func, arg, .. } => {
                    args.push(arg.as_ref());
                    current = func.as_ref();
                }
                ExprKind::EffectCall {
                    name, qualifier, ..
                } => {
                    args.reverse();
                    break (current.id, name.as_str(), qualifier.as_deref());
                }
                _ => return None,
            }
        };

        if !args.is_empty() {
            return None;
        }
        self.lower_eta_reduced_effect_op_ref(effect_call_id, op_name, qualifier)
    }
}
