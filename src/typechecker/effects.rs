use std::collections::HashSet;

use crate::ast;
use crate::token::Span;

use super::{Checker, Diagnostic, EffectOpSig, EffectRow, Type};

impl Checker {
    // --- Effect tracking ---

    /// Check body effects against a declared effect row.
    /// Returns Ok if all body effects are covered by the declared row.
    /// Open rows (with tail) allow any extra effects through.
    pub(crate) fn check_effects_via_row(
        &mut self,
        body_effs: &EffectRow,
        declared_row: &EffectRow,
        label: &str,
        span: crate::token::Span,
    ) -> Result<(), Diagnostic> {
        if body_effs.is_empty() && declared_row.is_empty() {
            return Ok(());
        }
        let declared = self.sub.apply_effect_row(declared_row);
        // Open row: extras flow through the tail variable
        if declared.tail.is_some() {
            return Ok(());
        }
        // Closed row: every body effect must appear in declared
        let mut undeclared = Vec::new();
        for (eff_name, _) in &body_effs.effects {
            if !declared.effects.iter().any(|(n, _)| n == eff_name) {
                undeclared.push(eff_name.clone());
            }
        }
        if undeclared.is_empty() {
            return Ok(());
        }
        undeclared.sort();
        if declared.effects.is_empty() {
            Err(Diagnostic::error_at(
                span,
                format!(
                    "{} uses effects {{{}}} but has no 'needs' declaration",
                    label,
                    undeclared.join(", ")
                ),
            ))
        } else {
            Err(Diagnostic::error_at(
                span,
                format!(
                    "{} uses effects {{{}}} not declared in its 'needs' clause",
                    label,
                    undeclared.join(", ")
                ),
            ))
        }
    }

    /// Find which effect an operation belongs to.
    pub(crate) fn effect_for_op(&self, op_name: &str, qualifier: Option<&str>) -> Option<String> {
        if let Some(effect_name) = qualifier
            && self.effects.contains_key(effect_name)
        {
            return Some(effect_name.to_string());
        }
        for (effect_name, info) in &self.effects {
            if info.ops.iter().any(|o| o.name == op_name) {
                return Some(effect_name.clone());
            }
        }
        None
    }

    /// Determine which effects a handler handles.
    pub(crate) fn handler_handled_effects(&self, handler: &ast::Handler) -> HashSet<String> {
        let mut handled = HashSet::new();
        match handler {
            ast::Handler::Named(name, _) => {
                if let Some(info) = self.handlers.get(name) {
                    handled.extend(info.effects.iter().cloned());
                }
            }
            ast::Handler::Inline { named, arms, .. } => {
                for name in named {
                    if let Some(info) = self.handlers.get(name) {
                        handled.extend(info.effects.iter().cloned());
                    }
                }
                for arm in arms {
                    if let Some(effect_name) = self.effect_for_op(&arm.node.op_name, None) {
                        handled.insert(effect_name);
                    }
                }
            }
        }
        handled
    }

    /// Instantiate an effect op signature, reusing cached type param vars for the same effect
    /// within the current function scope. This ensures `get` and `put` from `State s` share `s`.
    pub(crate) fn instantiate_effect_op(
        &mut self,
        effect_name: &str,
        op: &EffectOpSig,
        type_params: &[u32],
    ) -> EffectOpSig {
        if type_params.is_empty() {
            // No effect-level type params, but the op may have free type vars
            // (e.g. Process.spawn returns Pid msg where msg is free).
            // Collect all var IDs and instantiate fresh per call.
            let mut free_vars = std::collections::HashSet::new();
            fn collect_vars(ty: &Type, vars: &mut std::collections::HashSet<u32>) {
                match ty {
                    Type::Var(id) => {
                        vars.insert(*id);
                    }
                    Type::Fun(a, b, _) => {
                        collect_vars(a, vars);
                        collect_vars(b, vars);
                    }
                    Type::Con(_, args) => {
                        for a in args {
                            collect_vars(a, vars);
                        }
                    }
                    Type::Record(fields) => {
                        for (_, ty) in fields {
                            collect_vars(ty, vars);
                        }
                    }
                    Type::Error => {}
                }
            }
            for (_, t) in &op.params {
                collect_vars(t, &mut free_vars);
            }
            collect_vars(&op.return_type, &mut free_vars);
            if free_vars.is_empty() {
                return op.clone();
            }
            let mapping: std::collections::HashMap<u32, Type> =
                free_vars.iter().map(|&id| (id, self.fresh_var())).collect();
            return EffectOpSig {
                name: op.name.clone(),
                params: op
                    .params
                    .iter()
                    .map(|(label, t)| (label.clone(), self.replace_vars(t, &mapping)))
                    .collect(),
                return_type: self.replace_vars(&op.return_type, &mapping),
            };
        }
        // Reuse cached mapping or create fresh vars
        let mapping = if let Some(cached) = self.effect_meta.type_param_cache.get(effect_name) {
            cached.clone()
        } else {
            let mapping: std::collections::HashMap<u32, Type> = type_params
                .iter()
                .map(|&old_id| (old_id, self.fresh_var()))
                .collect();
            self.effect_meta.type_param_cache
                .insert(effect_name.to_string(), mapping.clone());
            mapping
        };
        EffectOpSig {
            name: op.name.clone(),
            params: op
                .params
                .iter()
                .map(|(label, t)| (label.clone(), self.replace_vars(t, &mapping)))
                .collect(),
            return_type: self.replace_vars(&op.return_type, &mapping),
        }
    }

    /// Look up an effect operation by name, optionally qualified (e.g. `Cache.get`).
    /// Returns the op signature with fresh type vars for the effect's type params.
    pub(crate) fn lookup_effect_op(
        &mut self,
        op_name: &str,
        qualifier: Option<&str>,
        span: Span,
    ) -> Result<EffectOpSig, Diagnostic> {
        if let Some(effect_name) = qualifier {
            let info = self
                .effects
                .get(effect_name)
                .ok_or_else(|| {
                    Diagnostic::error_at(span, format!("undefined effect: {}", effect_name))
                })?
                .clone();
            let op = info.ops.iter().find(|o| o.name == op_name).ok_or_else(|| {
                Diagnostic::error_at(
                    span,
                    format!("effect '{}' has no operation '{}'", effect_name, op_name),
                )
            })?;
            Ok(self.instantiate_effect_op(effect_name, op, &info.type_params))
        } else {
            let mut found: Option<(String, EffectOpSig, Vec<u32>)> = None;
            for (eff_name, info) in &self.effects {
                if let Some(op) = info.ops.iter().find(|o| o.name == op_name) {
                    if found.is_some() {
                        return Err(Diagnostic::error_at(
                            span,
                            format!(
                                "ambiguous effect operation '{}': found in multiple effects",
                                op_name
                            ),
                        ));
                    }
                    found = Some((eff_name.clone(), op.clone(), info.type_params.clone()));
                }
            }
            let (eff_name, op, type_params) = found.ok_or_else(|| {
                Diagnostic::error_at(span, format!("undefined effect operation: {}", op_name))
            })?;
            Ok(self.instantiate_effect_op(&eff_name, &op, &type_params))
        }
    }
}
