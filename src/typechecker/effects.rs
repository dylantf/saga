use std::collections::HashSet;

use crate::ast;
use crate::token::Span;

use super::{Checker, Diagnostic, EffectEntry, EffectOpSig, EffectRow, Severity, Type};

enum BareEffectOpResolution {
    Missing,
    Found(String),
    Ambiguous,
}

impl Checker {
    pub(crate) fn normalize_handler_effect_name(&mut self, effect_name: String) -> String {
        if effect_name.contains('.') {
            return effect_name;
        }

        let canonical = if let Some(canonical) = self.scope_map.resolve_effect(&effect_name) {
            canonical.to_string()
        } else {
            self.effects
                .keys()
                .find(|k| k.ends_with(&format!(".{}", effect_name)) || *k == &effect_name)
                .cloned()
                .unwrap_or_else(|| {
                    if let Some(module) = &self.current_module {
                        format!("{}.{}", module, effect_name)
                    } else {
                        effect_name.clone()
                    }
                })
        };

        if canonical != effect_name {
            let warning_key = format!("{} -> {}", effect_name, canonical);
            if self
                .internal_handler_normalization_warnings
                .insert(warning_key)
            {
                self.collected_diagnostics.push(Diagnostic::new(
                    Severity::Warning,
                    format!(
                        "internal warning: normalized bare effect `{}` inside `Handler` type to `{}`; handler effect names should already be canonical",
                        effect_name, canonical
                    ),
                ));
            }
        }

        canonical
    }

    // --- Effect lookup ---

    /// Look up an effect by name. Effects are stored under canonical names
    /// (e.g. "Std.Fail.Fail"). This helper is for internal canonical/effect-map
    /// lookups, not for repairing unresolved source names during inference.
    pub(crate) fn resolve_effect(&mut self, name: &str) -> Option<super::EffectDefInfo> {
        // Try exact match first (canonical)
        if let Some(info) = self.effects.get(name) {
            return Some(info.clone());
        }
        // Resolve through scope_map (handles bare, aliased, and qualified names)
        if let Some(canonical) = self.scope_map.resolve_effect(name).map(|s| s.to_string())
            && let Some(info) = self.effects.get(&canonical)
        {
            return Some(info.clone());
        }
        // Local module: Module.Name
        if let Some(module) = &self.current_module.clone() {
            let local_key = format!("{}.{}", module, name);
            if let Some(info) = self.effects.get(&local_key) {
                return Some(info.clone());
            }
        }
        None
    }

    /// Build a closed `EffectRow` from a list of `EffectRef`s (e.g. a handler's `needs` clause).
    /// Each ref is resolved to its canonical name via `resolve_effect`.
    pub(crate) fn effect_row_from_refs(&mut self, refs: &[ast::EffectRef]) -> EffectRow {
        EffectRow {
            effects: refs
                .iter()
                .map(|e| {
                    let resolved_name = self.canonical_effect_name(&e.name);
                    let args = e
                        .type_args
                        .iter()
                        .map(|te| self.convert_user_type_expr(te, &mut vec![]))
                        .collect();
                    EffectEntry::unnamed(resolved_name, args)
                })
                .collect(),
            tail: None,
        }
    }

    /// Resolve an effect name to its canonical form (e.g. "Log" -> "Std.Log.Log").
    pub(crate) fn canonical_effect_name(&mut self, name: &str) -> String {
        self.resolve_effect(name)
            .and_then(|info| {
                let short = name.rsplit('.').next().unwrap_or(name);
                info.source_module
                    .as_ref()
                    .map(|m| format!("{}.{}", m, short))
            })
            .unwrap_or_else(|| {
                if let Some(m) = &self.current_module {
                    format!("{}.{}", m, name)
                } else {
                    name.to_string()
                }
            })
    }

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
        for entry in &body_effs.effects {
            if !declared.effects.iter().any(|e| e.matches(entry)) {
                undeclared.push(entry.name.clone());
            }
        }
        if undeclared.is_empty() {
            return Ok(());
        }
        undeclared.sort();
        // Pretty-print effect names: strip module prefix for readability
        let pretty_effects: Vec<String> = undeclared
            .iter()
            .map(|e| e.rsplit('.').next().unwrap_or(e).to_string())
            .collect();
        let effects_str = pretty_effects.join(", ");
        if label == "function 'main'" {
            Err(Diagnostic::error_at(
                span,
                format!(
                    "`main` uses effects {{{}}} but no handler is provided. Use `with` to handle them, e.g.:\n\n  main () = {{\n    ...\n  }} with handler_name\n",
                    effects_str,
                ),
            ))
        } else if declared.effects.is_empty() {
            Err(Diagnostic::error_at(
                span,
                format!(
                    "{} uses effects {{{}}} but has no 'needs' declaration",
                    label, effects_str,
                ),
            ))
        } else {
            Err(Diagnostic::error_at(
                span,
                format!(
                    "{} uses effects {{{}}} not declared in its 'needs' clause",
                    label, effects_str,
                ),
            ))
        }
    }

    /// Find which effect an operation belongs to. Returns the canonical
    /// (module-qualified) effect name, e.g. "Std.Fail.Fail".
    pub(crate) fn effect_for_op(&self, op_name: &str, qualifier: Option<&str>) -> Option<String> {
        if let Some(effect_name) = qualifier {
            return self.resolve_effect_qualifier(effect_name);
        }

        match self.resolve_bare_effect_op(op_name) {
            BareEffectOpResolution::Found(effect_name) => Some(effect_name),
            BareEffectOpResolution::Missing | BareEffectOpResolution::Ambiguous => None,
        }
    }

    /// Determine which effects a handler handles.
    pub(crate) fn handler_handled_effects(&mut self, handler: &ast::Handler) -> HashSet<String> {
        let mut handled = HashSet::new();
        match handler {
            ast::Handler::Named(named) => {
                let resolved_name = self.resolved_handler_name(named.id, &named.name);
                if let Some(info) = self.handlers.get(&resolved_name) {
                    handled.extend(info.effects.iter().cloned());
                } else if let Some(effects) = self.handler_effects_from_env(&resolved_name) {
                    handled.extend(effects);
                }
            }
            ast::Handler::Inline { .. } => {
                for named_ref in handler.named_refs() {
                    let resolved_name = self.resolved_handler_name(named_ref.id, &named_ref.name);
                    if let Some(info) = self.handlers.get(&resolved_name) {
                        handled.extend(info.effects.iter().cloned());
                    } else if let Some(effects) = self.handler_effects_from_env(&resolved_name) {
                        handled.extend(effects);
                    }
                }
                for arm in handler.inline_arms() {
                    let resolved_qualifier = self
                        .resolution
                        .handler_arm_qualifier(arm.id)
                        .or(arm.qualifier.as_deref());
                    if let Some(effect_name) = self.effect_for_op(&arm.op_name, resolved_qualifier)
                    {
                        handled.insert(effect_name);
                    }
                }
            }
        }
        handled
    }

    /// Extract handled effect names from a `Handler(...)` type in the env.
    /// Used as a fallback when a name is not in `self.handlers` (e.g. handle bindings).
    pub(crate) fn handler_effects_from_env(&mut self, name: &str) -> Option<Vec<String>> {
        let scheme = self.env.get(name)?;
        let ty = self.sub.apply(&scheme.ty);
        if let Type::Con(ref con_name, ref args) = ty
            && con_name == super::canonicalize_type_name("Handler")
        {
            let effects: Vec<String> = args
                .iter()
                .filter_map(|arg| {
                    let resolved = self.sub.apply(arg);
                    if let Type::Con(eff_name, _) = resolved {
                        Some(self.normalize_handler_effect_name(eff_name))
                    } else {
                        None
                    }
                })
                .collect();
            if effects.is_empty() {
                return None;
            }
            return Some(effects);
        }
        None
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
                effect_name: effect_name.to_string(),
                params: op
                    .params
                    .iter()
                    .map(|(label, t)| (label.clone(), self.replace_vars(t, &mapping)))
                    .collect(),
                return_type: self.replace_vars(&op.return_type, &mapping),
                needs: self.replace_vars_in_effect_row(&op.needs, &mapping),
            };
        }
        // Reuse cached mapping or create fresh vars for effect-level type params
        let mut mapping = if let Some(cached) = self.effect_meta.type_param_cache.get(effect_name) {
            cached.clone()
        } else {
            let mapping: std::collections::HashMap<u32, Type> = type_params
                .iter()
                .map(|&old_id| (old_id, self.fresh_var()))
                .collect();
            self.effect_meta
                .type_param_cache
                .insert(effect_name.to_string(), mapping.clone());
            mapping
        };
        // Also freshen any free vars NOT in the type_params (e.g. `a` in
        // `Fail e { fun fail : e -> a }`). These must be fresh per call
        // site, unlike effect-level params which are shared across ops.
        let type_param_set: std::collections::HashSet<u32> = type_params.iter().copied().collect();
        let mut free_vars = std::collections::HashSet::new();
        fn collect_vars2(ty: &Type, vars: &mut std::collections::HashSet<u32>) {
            match ty {
                Type::Var(id) => {
                    vars.insert(*id);
                }
                Type::Fun(a, b, _) => {
                    collect_vars2(a, vars);
                    collect_vars2(b, vars);
                }
                Type::Con(_, args) => {
                    for a in args {
                        collect_vars2(a, vars);
                    }
                }
                Type::Record(fields) => {
                    for (_, ty) in fields {
                        collect_vars2(ty, vars);
                    }
                }
                Type::Error => {}
            }
        }
        for (_, t) in &op.params {
            collect_vars2(t, &mut free_vars);
        }
        collect_vars2(&op.return_type, &mut free_vars);
        for id in free_vars {
            if !type_param_set.contains(&id) && !mapping.contains_key(&id) {
                mapping.insert(id, self.fresh_var());
            }
        }
        EffectOpSig {
            name: op.name.clone(),
            effect_name: effect_name.to_string(),
            params: op
                .params
                .iter()
                .map(|(label, t)| (label.clone(), self.replace_vars(t, &mapping)))
                .collect(),
            return_type: self.replace_vars(&op.return_type, &mapping),
            needs: self.replace_vars_in_effect_row(&op.needs, &mapping),
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
            // Resolve qualifier through scope_map (bare/aliased -> canonical)
            let canonical = self.resolve_effect_qualifier(effect_name).ok_or_else(|| {
                Diagnostic::error_at(span, format!("undefined effect: {}", effect_name))
            })?;
            let info = self
                .effects
                .get(&canonical)
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
            Ok(self.instantiate_effect_op(&canonical, op, &info.type_params))
        } else {
            let eff_name = match self.resolve_bare_effect_op(op_name) {
                BareEffectOpResolution::Missing => {
                    return Err(Diagnostic::error_at(
                        span,
                        format!("undefined effect operation: {}", op_name),
                    ));
                }
                BareEffectOpResolution::Ambiguous => {
                    return Err(Diagnostic::error_at(
                        span,
                        format!(
                            "ambiguous effect operation '{}': found in multiple effects",
                            op_name
                        ),
                    ));
                }
                BareEffectOpResolution::Found(eff_name) => eff_name,
            };
            let info = self.effects.get(&eff_name).ok_or_else(|| {
                Diagnostic::error_at(span, format!("undefined effect operation: {}", op_name))
            })?;
            let op = info
                .ops
                .iter()
                .find(|o| o.name == op_name)
                .ok_or_else(|| {
                    Diagnostic::error_at(span, format!("undefined effect operation: {}", op_name))
                })?
                .clone();
            let type_params = info.type_params.clone();
            Ok(self.instantiate_effect_op(&eff_name, &op, &type_params))
        }
    }

    fn resolve_effect_qualifier(&self, effect_name: &str) -> Option<String> {
        if let Some(canonical) = self.scope_map.resolve_effect(effect_name)
            && self.effects.contains_key(canonical)
        {
            return Some(canonical.to_string());
        }
        if self.effects.contains_key(effect_name) {
            return Some(effect_name.to_string());
        }
        if let Some(module) = &self.current_module {
            let local_key = format!("{}.{}", module, effect_name);
            if self.effects.contains_key(&local_key) {
                return Some(local_key);
            }
        }
        None
    }

    fn resolve_bare_effect_op(&self, op_name: &str) -> BareEffectOpResolution {
        let Some(candidates) = self.scope_map.effect_ops.get(op_name) else {
            return BareEffectOpResolution::Missing;
        };
        match candidates.len() {
            0 => BareEffectOpResolution::Missing,
            1 => {
                BareEffectOpResolution::Found(candidates.iter().next().cloned().unwrap_or_default())
            }
            _ => BareEffectOpResolution::Ambiguous,
        }
    }
}
