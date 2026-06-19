use std::collections::HashSet;

use crate::ast::{self, Kind};
use crate::token::Span;

use super::{Checker, Diagnostic, EffectEntry, EffectOpSig, EffectRow, Severity, Type};

enum BareEffectOpResolution {
    Missing,
    Found(String),
    /// Op resolves to >1 effect within the chosen tier (locals if any local
    /// effect contributes, otherwise imports). Carries the candidate
    /// canonical effect names for diagnostic listing.
    Ambiguous(Vec<String>),
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
                    let args = self.convert_effect_ref_args(e, &mut vec![]);
                    EffectEntry::unnamed(resolved_name, args)
                })
                .collect(),
            tails: vec![],
        }
    }

    pub(crate) fn convert_effect_ref_args(
        &mut self,
        effect_ref: &ast::EffectRef,
        params: &mut Vec<(String, u32)>,
    ) -> Vec<Type> {
        let resolved_name = self.resolved_effect_name(effect_ref.id, &effect_ref.name);
        let kinds: Vec<Kind> = self
            .effects
            .get(&resolved_name)
            .map(|info| {
                info.type_params
                    .iter()
                    .map(|id| self.var_kind(*id))
                    .collect()
            })
            .unwrap_or_default();
        effect_ref
            .type_args
            .iter()
            .enumerate()
            .map(|(i, te)| {
                let kind = kinds.get(i).copied().unwrap_or(Kind::Star);
                let ty = self.convert_type_expr_kinded(te, params, kind);
                self.canonicalize_handler_effect_types(ty)
            })
            .collect()
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
        // Open row: extras flow through the tail variable(s)
        if declared.is_open() {
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
            BareEffectOpResolution::Missing | BareEffectOpResolution::Ambiguous(_) => None,
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
                        .handler_arm(arm.id)
                        .map(|resolved| resolved.effect.as_str())
                        .or(arm.qualifier.as_deref());
                    if let Some(effect_name) = self
                        .resolution
                        .handler_arm(arm.id)
                        .map(|resolved| resolved.effect.clone())
                        .or_else(|| self.effect_for_op(&arm.op_name, resolved_qualifier))
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
                    Type::Fun(a, b, row) => {
                        collect_vars(a, vars);
                        collect_vars(b, vars);
                        for entry in &row.effects {
                            for arg in &entry.args {
                                collect_vars(arg, vars);
                            }
                        }
                        for tail in &row.tails {
                            collect_vars(tail, vars);
                        }
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
                    Type::Symbol(_) => {}
                    Type::Error => {}
                }
            }
            for (_, t) in &op.params {
                collect_vars(t, &mut free_vars);
            }
            collect_vars(&op.return_type, &mut free_vars);
            for entry in &op.needs.effects {
                for arg in &entry.args {
                    collect_vars(arg, &mut free_vars);
                }
            }
            for tail in &op.needs.tails {
                collect_vars(tail, &mut free_vars);
            }
            for (_, var_id, extra_types) in &op.constraints {
                free_vars.insert(*var_id);
                for ty in extra_types {
                    collect_vars(ty, &mut free_vars);
                }
            }
            if free_vars.is_empty() {
                return op.clone();
            }
            let mapping: std::collections::HashMap<u32, Type> =
                free_vars.iter().map(|&id| (id, self.fresh_var())).collect();
            self.propagate_op_constraint_var_names(op, &mapping);
            return EffectOpSig {
                name: op.name.clone(),
                effect_name: effect_name.to_string(),
                params: op
                    .params
                    .iter()
                    .map(|(label, t)| (label.clone(), Self::replace_vars(t, &mapping)))
                    .collect(),
                return_type: Self::replace_vars(&op.return_type, &mapping),
                needs: self.replace_vars_in_effect_row(&op.needs, &mapping),
                constraints: op
                    .constraints
                    .iter()
                    .map(|(trait_name, var_id, extra_types)| {
                        let fresh = mapping
                            .get(var_id)
                            .and_then(|ty| match ty {
                                Type::Var(id) => Some(*id),
                                _ => None,
                            })
                            .unwrap_or(*var_id);
                        let extra_fresh = extra_types
                            .iter()
                            .map(|ty| Self::replace_vars(ty, &mapping))
                            .collect();
                        (trait_name.clone(), fresh, extra_fresh)
                    })
                    .collect(),
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
                Type::Fun(a, b, row) => {
                    collect_vars2(a, vars);
                    collect_vars2(b, vars);
                    for entry in &row.effects {
                        for arg in &entry.args {
                            collect_vars2(arg, vars);
                        }
                    }
                    for tail in &row.tails {
                        collect_vars2(tail, vars);
                    }
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
                Type::Symbol(_) => {}
                Type::Error => {}
            }
        }
        for (_, t) in &op.params {
            collect_vars2(t, &mut free_vars);
        }
        collect_vars2(&op.return_type, &mut free_vars);
        for entry in &op.needs.effects {
            for arg in &entry.args {
                collect_vars2(arg, &mut free_vars);
            }
        }
        for tail in &op.needs.tails {
            collect_vars2(tail, &mut free_vars);
        }
        for (_, var_id, extra_types) in &op.constraints {
            free_vars.insert(*var_id);
            for ty in extra_types {
                collect_vars2(ty, &mut free_vars);
            }
        }
        for id in free_vars {
            if !type_param_set.contains(&id) && !mapping.contains_key(&id) {
                mapping.insert(id, self.fresh_var());
            }
        }
        self.propagate_op_constraint_var_names(op, &mapping);
        EffectOpSig {
            name: op.name.clone(),
            effect_name: effect_name.to_string(),
            params: op
                .params
                .iter()
                .map(|(label, t)| (label.clone(), Self::replace_vars(t, &mapping)))
                .collect(),
            return_type: Self::replace_vars(&op.return_type, &mapping),
            needs: self.replace_vars_in_effect_row(&op.needs, &mapping),
            constraints: op
                .constraints
                .iter()
                .map(|(trait_name, var_id, extra_types)| {
                    let fresh = mapping
                        .get(var_id)
                        .and_then(|ty| match ty {
                            Type::Var(id) => Some(*id),
                            _ => None,
                        })
                        .unwrap_or(*var_id);
                    let extra_fresh = extra_types
                        .iter()
                        .map(|ty| Self::replace_vars(ty, &mapping))
                        .collect();
                    (trait_name.clone(), fresh, extra_fresh)
                })
                .collect(),
        }
    }

    /// Carry an op constraint's source type-variable name (`where {a: PgType}`)
    /// from the original op var id onto the freshly-instantiated var id, so a
    /// handler arm checked against this instantiation can name the dictionary
    /// param consistently (`__dict_PgType_a`). Keyed by globally-unique var ids,
    /// so this never disturbs unrelated bindings.
    fn propagate_op_constraint_var_names(
        &mut self,
        op: &EffectOpSig,
        mapping: &std::collections::HashMap<u32, Type>,
    ) {
        for (_, var_id, _) in &op.constraints {
            let Some(name) = self.trait_state.where_bound_var_names.get(var_id).cloned() else {
                continue;
            };
            if let Some(Type::Var(fresh)) = mapping.get(var_id) {
                self.trait_state
                    .where_bound_var_names
                    .insert(*fresh, name);
            }
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
                BareEffectOpResolution::Ambiguous(candidates) => {
                    let display = candidates.join(", ");
                    return Err(Diagnostic::error_at(
                        span,
                        format!(
                            "ambiguous effect operation '{}': found in [{}]; qualify the call (e.g. `{}.{}!`)",
                            op_name, display, candidates[0], op_name
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

    // --- Effect row joining (N-ary union) ---
    //
    // Used at multi-element inference sites (list literals, case arms,
    // if/else, tuples, records) so that heterogeneous-effect elements
    // produce a row whose effect set is the union of all input rows.
    // The single-shot unification mechanism in `unify_effect_rows` pins a
    // row variable to the first concrete row it meets; without an
    // explicit join, later elements with disjoint effects are rejected.

    /// Join N effect rows. The result's effect list is the union of all
    /// inputs (matched by canonical effect name; type args are unified
    /// pairwise across same-named entries). The result's tail is closed
    /// if every input is closed, otherwise a single fresh row variable
    /// shared by every open input.
    ///
    /// Side effects:
    /// - Unifies the type args of same-named entries across inputs.
    /// - Binds each open input's tail to a row containing that input's
    ///   missing entries plus the shared fresh tail. This ensures that
    ///   later substitution-application on any input row yields the
    ///   joined row.
    pub(crate) fn join_effect_rows(
        &mut self,
        rows: &[&EffectRow],
        span: Span,
    ) -> Result<EffectRow, Diagnostic> {
        if rows.is_empty() {
            return Ok(EffectRow::empty());
        }

        // Apply substitutions so any already-bound tails are resolved.
        let applied: Vec<EffectRow> = rows.iter().map(|r| self.sub.apply_effect_row(r)).collect();

        // Build the union of entries.
        //
        // Unify type args of same-name entries across inputs while we walk;
        // this MUST happen before binding tails so we never bind a tail to a
        // row containing stale unification variables.
        let mut union: Vec<EffectEntry> = Vec::new();
        for row in &applied {
            for entry in &row.effects {
                if let Some(existing) = union.iter().find(|e| e.matches(entry)) {
                    let existing_args = existing.args.clone();
                    for (existing_arg, new_arg) in existing_args.iter().zip(entry.args.iter()) {
                        self.unify_at(existing_arg, new_arg, span)?;
                    }
                } else {
                    union.push(entry.clone());
                }
            }
        }

        // Decide tail. If any input is open, the result is open and shares
        // a single fresh tail var; otherwise the result is closed.
        let any_open = applied.iter().any(|r| r.is_open());
        if !any_open {
            return Ok(EffectRow {
                effects: union,
                tails: vec![],
            });
        }

        let shared_tail = self.fresh_var();

        // For each open input, bind its tail var(s) so the row widens to
        // (union, shared_tail). The first tail of a row absorbs the extras
        // (union entries this row lacks); any further tails simply alias the
        // shared tail so the row stays open without losing information.
        //
        // Track which tail vars we've bound to avoid double-binding when two
        // inputs happen to share the same tail variable.
        let mut bound: HashSet<u32> = HashSet::new();
        for row in &applied {
            let tail_ids = row.tail_var_ids();
            if tail_ids.is_empty() {
                continue;
            }
            let extras: Vec<EffectEntry> = union
                .iter()
                .filter(|u| !row.effects.iter().any(|re| re.matches(u)))
                .cloned()
                .collect();
            for (i, &tail_id) in tail_ids.iter().enumerate() {
                if !bound.insert(tail_id) {
                    continue;
                }
                let binding = EffectRow {
                    effects: if i == 0 { extras.clone() } else { vec![] },
                    tails: vec![shared_tail.clone()],
                };
                self.sub
                    .bind_row(tail_id, binding)
                    .map_err(|e| e.with_span(span))?;
            }
        }

        Ok(EffectRow {
            effects: union,
            tails: vec![shared_tail],
        })
    }

    /// Join N types into a single type that all inputs fit into.
    ///
    /// - When every input is a function type, joins element-wise: params
    ///   are unified pairwise (no widening on the contravariant side),
    ///   returns are joined recursively (handles nested function types),
    ///   and rows are joined via `join_effect_rows` to produce the row
    ///   union that this whole change is for.
    /// - When the inputs are not all function types, falls back to
    ///   pairwise unification against the first input. The join only
    ///   matters where row variables sit, which is exclusively on
    ///   function types.
    ///
    /// Empty input list returns a fresh type variable; single-element
    /// input is returned unchanged.
    pub(crate) fn join_branch_types(
        &mut self,
        tys: &[Type],
        span: Span,
    ) -> Result<Type, Diagnostic> {
        match tys.len() {
            0 => return Ok(self.fresh_var()),
            1 => return Ok(tys[0].clone()),
            _ => {}
        }

        let applied: Vec<Type> = tys.iter().map(|t| self.sub.apply(t)).collect();

        let all_fun = applied.iter().all(|t| matches!(t, Type::Fun(_, _, _)));
        if !all_fun {
            // Pairwise unify against the first; the join semantics only
            // differ from plain unification on function types' rows.
            let result = applied[0].clone();
            for t in &applied[1..] {
                self.unify_at(&result, t, span)?;
            }
            return Ok(self.sub.apply(&result));
        }

        let mut params: Vec<Type> = Vec::with_capacity(applied.len());
        let mut returns: Vec<Type> = Vec::with_capacity(applied.len());
        let mut rows: Vec<EffectRow> = Vec::with_capacity(applied.len());
        for t in &applied {
            if let Type::Fun(p, r, row) = t {
                params.push((**p).clone());
                returns.push((**r).clone());
                rows.push(row.clone());
            }
        }

        let joined_param = params[0].clone();
        for p in &params[1..] {
            self.unify_at(&joined_param, p, span)?;
        }

        let joined_return = self.join_branch_types(&returns, span)?;

        let row_refs: Vec<&EffectRow> = rows.iter().collect();
        let joined_row = self.join_effect_rows(&row_refs, span)?;

        Ok(Type::Fun(
            Box::new(self.sub.apply(&joined_param)),
            Box::new(joined_return),
            joined_row,
        ))
    }

    /// Pre-widen row variables that appear at multiple positions in an
    /// expected positional/field-typed structure (tuple or anonymous
    /// record) so that the actual element rows can union into the shared
    /// variable rather than pinning it to the first.
    ///
    /// `actual_tys` and `expected_tys` are positional pairs (same length,
    /// matched by index). The expected types live inside an outer
    /// structure — e.g. tuple element types or anonymous-record field
    /// types in canonical (sorted) order.
    ///
    /// For each row tail variable that appears in `Type::Fun(_, _, {.., tail})`
    /// at two or more positions, this function joins the actual rows at
    /// those positions and binds the variable to the result. Subsequent
    /// element-wise unification then succeeds (the shared variable is no
    /// longer free to be pinned by the first element).
    ///
    /// No-op when no shared variable exists, or when the actual at a
    /// shared position isn't a function type — in the latter case the
    /// caller's unification will produce its normal mismatch error.
    pub(crate) fn prewiden_shared_rows(
        &mut self,
        actual_tys: &[Type],
        expected_tys: &[Type],
        span: Span,
    ) -> Result<(), Diagnostic> {
        // Collect tail-var IDs that appear at multiple expected positions.
        let mut tail_positions: std::collections::HashMap<u32, Vec<usize>> =
            std::collections::HashMap::new();
        for (i, expected) in expected_tys.iter().enumerate() {
            let resolved = self.sub.apply(expected);
            let Type::Fun(_, _, row) = &resolved else {
                continue;
            };
            let resolved_row = self.sub.apply_effect_row(row);
            for id in resolved_row.tail_var_ids() {
                tail_positions.entry(id).or_default().push(i);
            }
        }

        for (tail_id, positions) in tail_positions {
            if positions.len() < 2 {
                continue;
            }
            let mut actual_rows: Vec<EffectRow> = Vec::with_capacity(positions.len());
            let mut bail = false;
            for pos in &positions {
                let actual = self.sub.apply(&actual_tys[*pos]);
                let Type::Fun(_, _, row) = actual else {
                    bail = true;
                    break;
                };
                actual_rows.push(self.sub.apply_effect_row(&row));
            }
            if bail {
                continue;
            }
            let row_refs: Vec<&EffectRow> = actual_rows.iter().collect();
            let joined = self.join_effect_rows(&row_refs, span)?;
            self.sub
                .bind_row(tail_id, joined)
                .map_err(|e| e.with_span(span))?;
        }
        Ok(())
    }

    /// Tier-based bare effect-op lookup. Locally defined effects shadow
    /// imported effects: if any local effect contributes the op name, only
    /// locals are considered. Within the chosen tier, exactly one candidate
    /// is `Found`; >1 is `Ambiguous` (with the candidate list); 0 is
    /// `Missing`. The tier split is recovered from `current_module` —
    /// canonical names with that prefix are local, the rest are imports.
    fn resolve_bare_effect_op(&self, op_name: &str) -> BareEffectOpResolution {
        let Some(candidates) = self.scope_map.effect_ops.get(op_name) else {
            return BareEffectOpResolution::Missing;
        };
        let local_prefix = self.current_module.as_deref().map(|m| format!("{}.", m));
        let (locals, imports): (Vec<&String>, Vec<&String>) = candidates
            .iter()
            .partition(|c| local_prefix.as_deref().is_some_and(|p| c.starts_with(p)));
        let chosen = if !locals.is_empty() { locals } else { imports };
        match chosen.len() {
            0 => BareEffectOpResolution::Missing,
            1 => BareEffectOpResolution::Found(chosen[0].clone()),
            _ => {
                let mut names: Vec<String> = chosen.into_iter().cloned().collect();
                names.sort();
                BareEffectOpResolution::Ambiguous(names)
            }
        }
    }
}
