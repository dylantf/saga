use std::collections::HashMap;

use crate::ast::HandlerArm;

use super::{FunInfo, Lowerer};

impl<'a> Lowerer<'a> {
    pub(super) fn module_name_to_erlang(module_name: &str) -> String {
        module_name
            .split('.')
            .map(|s| s.to_lowercase())
            .collect::<Vec<_>>()
            .join("_")
    }

    pub(super) fn imported_handler_external_target(
        &self,
        source_module: &str,
        name: &str,
        arity: usize,
    ) -> Option<(String, String)> {
        self.ctx
            .module_semantics(source_module)
            .and_then(|module_semantics| {
                module_semantics
                    .codegen_info
                    .external_funs
                    .iter()
                    .find(|(fun_name, _, _, fun_arity)| fun_name == name && *fun_arity == arity)
                    .map(|(_, erl_mod, erl_fun, _)| (erl_mod.clone(), erl_fun.clone()))
            })
    }

    pub(super) fn resolved_fun_info(
        &self,
        node_id: crate::ast::NodeId,
        fallback: &str,
    ) -> Option<&FunInfo> {
        match self.resolved.get(&node_id) {
            Some(resolved)
                if resolved.source_module.as_deref() == Some(&self.current_source_module) =>
            {
                self.fun_info
                    .get(fallback)
                    .or_else(|| self.fun_info.get(&resolved.canonical_name))
            }
            Some(resolved) => self
                .fun_info
                .get(&resolved.canonical_name)
                .or_else(|| self.fun_info.get(fallback)),
            None => None,
        }
    }

    pub(super) fn substitute_type_vars(
        ty: &crate::typechecker::Type,
        subst: &HashMap<u32, crate::typechecker::Type>,
    ) -> crate::typechecker::Type {
        use crate::typechecker::{EffectEntry, EffectRow, Type};

        match ty {
            Type::Var(id) => subst.get(id).cloned().unwrap_or(Type::Var(*id)),
            Type::Fun(param, ret, row) => Type::Fun(
                Box::new(Self::substitute_type_vars(param, subst)),
                Box::new(Self::substitute_type_vars(ret, subst)),
                EffectRow {
                    effects: row
                        .effects
                        .iter()
                        .map(|entry| EffectEntry {
                            name: entry.name.clone(),
                            args: entry
                                .args
                                .iter()
                                .map(|arg| Self::substitute_type_vars(arg, subst))
                                .collect(),
                        })
                        .collect(),
                    tails: row
                        .tails
                        .iter()
                        .map(|tail| Self::substitute_type_vars(tail, subst))
                        .collect(),
                },
            ),
            Type::Con(name, args) => Type::Con(
                name.clone(),
                args.iter()
                    .map(|arg| Self::substitute_type_vars(arg, subst))
                    .collect(),
            ),
            Type::Record(fields) => Type::Record(
                fields
                    .iter()
                    .map(|(name, ty)| (name.clone(), Self::substitute_type_vars(ty, subst)))
                    .collect(),
            ),
            Type::Symbol(name) => Type::Symbol(name.clone()),
            Type::Error => Type::Error,
        }
    }

    pub(super) fn bind_type_vars_from_match(
        actual: &crate::typechecker::Type,
        pattern: &crate::typechecker::Type,
        subst: &mut HashMap<u32, crate::typechecker::Type>,
    ) {
        use crate::typechecker::Type;

        match (actual, pattern) {
            (_, Type::Var(id)) => {
                subst.entry(*id).or_insert_with(|| actual.clone());
            }
            (Type::Fun(a1, b1, _), Type::Fun(a2, b2, _)) => {
                Self::bind_type_vars_from_match(a1, a2, subst);
                Self::bind_type_vars_from_match(b1, b2, subst);
            }
            (Type::Con(n1, xs1), Type::Con(n2, xs2)) if n1 == n2 && xs1.len() == xs2.len() => {
                for (x1, x2) in xs1.iter().zip(xs2.iter()) {
                    Self::bind_type_vars_from_match(x1, x2, subst);
                }
            }
            (Type::Record(fs1), Type::Record(fs2)) if fs1.len() == fs2.len() => {
                for ((n1, t1), (n2, t2)) in fs1.iter().zip(fs2.iter()) {
                    if n1 == n2 {
                        Self::bind_type_vars_from_match(t1, t2, subst);
                    }
                }
            }
            _ => {}
        }
    }

    /// Resolve a record's declared `field -> type` map from its name, trying the
    /// canonical `record_name` pinned on a node first, then the surface name, then
    /// a `<module>.<Name>` lookup. Used to recover per-field expected types at
    /// `RecordCreate` so an effectful function-typed field (e.g.
    /// `run: Int -> Int needs {Logger}`) is lowered with the evidence-passing CPS
    /// convention rather than as a plain closure. The field types may still carry
    /// the record's type-parameter vars (we don't substitute concrete args here),
    /// which is sufficient since a field's effect row is independent of them.
    pub(super) fn record_field_types_by_name(
        &self,
        record_name: Option<&str>,
        source_name: &str,
    ) -> Option<HashMap<String, crate::typechecker::Type>> {
        let module_name = self.current_semantic_module_name();
        let info = record_name
            .and_then(|rn| self.check_result.records.get(rn))
            .or_else(|| self.check_result.records.get(source_name))
            .or_else(|| {
                self.check_result
                    .records
                    .get(crate::typechecker::bare_type_name(source_name))
            })
            .or_else(|| {
                self.check_result
                    .records
                    .get(&format!("{module_name}.{source_name}"))
            })?;
        Some(info.fields.iter().cloned().collect())
    }

    pub(super) fn record_field_types_from_expected(
        &self,
        expected_ty: &crate::typechecker::Type,
    ) -> Option<HashMap<String, crate::typechecker::Type>> {
        use crate::typechecker::Type;

        match expected_ty {
            Type::Record(fields) => Some(fields.iter().cloned().collect()),
            Type::Con(name, args) => {
                let info = self.check_result.records.get(name).or_else(|| {
                    self.check_result
                        .records
                        .get(crate::typechecker::bare_type_name(name))
                })?;
                let mut subst = HashMap::new();
                for (param_id, arg_ty) in info.type_params.iter().zip(args.iter()) {
                    subst.insert(*param_id, arg_ty.clone());
                }
                Some(
                    info.fields
                        .iter()
                        .map(|(field, ty)| (field.clone(), Self::substitute_type_vars(ty, &subst)))
                        .collect(),
                )
            }
            _ => None,
        }
    }

    pub(super) fn constructor_arg_types_from_expected(
        &self,
        ctor_name: &str,
        expected_ty: &crate::typechecker::Type,
    ) -> Option<Vec<crate::typechecker::Type>> {
        if matches!(
            expected_ty,
            crate::typechecker::Type::Var(_) | crate::typechecker::Type::Error
        ) {
            return None;
        }
        let scheme = self.check_result.constructors.get(ctor_name)?;
        let mut param_tys = Vec::new();
        let mut current = &scheme.ty;
        while let crate::typechecker::Type::Fun(param, ret, _) = current {
            param_tys.push((**param).clone());
            current = ret;
        }
        let mut subst = HashMap::new();
        Self::bind_type_vars_from_match(expected_ty, current, &mut subst);
        Some(
            param_tys
                .into_iter()
                .map(|ty| Self::substitute_type_vars(&ty, &subst))
                .collect(),
        )
    }

    pub(super) fn function_tail_type_after_params(
        &self,
        name: &str,
        consumed_params: usize,
    ) -> Option<crate::typechecker::Type> {
        let mut ty = self
            .check_result
            .env
            .get(name)
            .map(|scheme| self.check_result.sub.apply(&scheme.ty))?;
        for _ in 0..consumed_params {
            let crate::typechecker::Type::Fun(_, ret, _) = ty else {
                return None;
            };
            ty = *ret;
        }
        Some(ty)
    }

    pub(super) fn current_semantic_module_name(&self) -> &str {
        self.current_handler_source_module
            .as_deref()
            .unwrap_or(&self.current_source_module)
    }

    /// When lowering code from an imported handler, returns the handler's
    /// source module so constructor atoms and patterns resolve against the
    /// correct module. Returns `None` when lowering the current module's
    /// own code (the common case).
    pub(super) fn handler_origin_module(&self) -> Option<&str> {
        self.current_handler_source_module
            .as_deref()
            .filter(|m| *m != self.current_source_module)
    }

    pub(super) fn carried_constructor_origin_module(
        &self,
        node_id: crate::ast::NodeId,
    ) -> Option<&str> {
        self.carried_constructors
            .get(&node_id)
            .and_then(|canonical| canonical.rsplit_once('.').map(|(module, _)| module))
            .filter(|module| *module != self.current_source_module)
    }

    pub(super) fn carried_constructor_name_origin_module(&self, name: &str) -> Option<&str> {
        let bare = name.rsplit('.').next().unwrap_or(name);
        if matches!(bare, "Nil" | "Cons" | "True" | "False")
            || super::beam_interop::exit_reason_bare_atom(bare).is_some()
        {
            return None;
        }
        if self.constructor_atoms.contains_key(bare) {
            return None;
        }
        self.carried_constructor_names
            .get(bare)
            .map(String::as_str)
            .filter(|module| *module != self.current_source_module)
    }

    pub(super) fn constructor_origin_module_for(
        &self,
        node_id: crate::ast::NodeId,
        name: &str,
    ) -> Option<&str> {
        self.carried_constructor_origin_module(node_id)
            .or_else(|| self.carried_constructor_name_origin_module(name))
            .or_else(|| self.handler_origin_module())
    }

    /// Check whether a name refers to a known constructor, accounting for
    /// the current handler origin module if lowering imported handler code.
    pub(super) fn is_known_constructor(&self, name: &str) -> bool {
        if self.constructor_atoms.contains_key(name) {
            return true;
        }
        if let Some(origin) = self.handler_origin_module() {
            let qualified = format!("{}.{}", origin, name);
            return self.constructor_atoms.contains_key(&qualified);
        }
        false
    }

    pub(super) fn front_resolution_for_module(
        &self,
        module_name: &str,
    ) -> Option<&crate::typechecker::ResolutionResult> {
        self.check_result
            .module_check_results()
            .get(module_name)
            .map(|m| &m.resolution)
            .or_else(|| {
                (module_name == self.current_source_module).then_some(&self.check_result.resolution)
            })
            .or_else(|| {
                self.ctx
                    .module_semantics(module_name)
                    .map(|m| m.front_resolution)
            })
    }

    pub(super) fn current_value_ref(
        &self,
        node_id: crate::ast::NodeId,
    ) -> Option<&crate::typechecker::ResolvedValue> {
        self.front_resolution_for_module(self.current_semantic_module_name())
            .and_then(|r| r.value(node_id))
    }

    pub(super) fn current_record_type_name(&self, node_id: crate::ast::NodeId) -> Option<&str> {
        self.carried_record_types
            .get(&node_id)
            .map(String::as_str)
            .or_else(|| {
                self.front_resolution_for_module(self.current_semantic_module_name())
                    .and_then(|r| r.record_type(node_id))
            })
    }

    pub(super) fn handler_arm_effect_for_module(
        &self,
        module_name: &str,
        node_id: crate::ast::NodeId,
    ) -> Option<&str> {
        self.front_resolution_for_module(module_name)
            .and_then(|r| r.handler_arm(node_id))
            .map(|resolved| resolved.effect.as_str())
    }

    pub(super) fn resolved_effect_ref_for_module(
        &self,
        module_name: &str,
        effect_ref: &crate::ast::EffectRef,
    ) -> String {
        self.front_resolution_for_module(module_name)
            .and_then(|r| r.effect_ref(effect_ref.id))
            .map(|resolved| {
                self.effect_canonical
                    .get(resolved)
                    .cloned()
                    .unwrap_or_else(|| resolved.to_string())
            })
            .unwrap_or_else(|| {
                self.effect_canonical
                    .get(&effect_ref.name)
                    .cloned()
                    .unwrap_or_else(|| effect_ref.name.clone())
            })
    }

    pub(super) fn resolved_effect_refs_for_module(
        &self,
        module_name: &str,
        effect_refs: &[crate::ast::EffectRef],
    ) -> Vec<String> {
        effect_refs
            .iter()
            .map(|effect_ref| self.resolved_effect_ref_for_module(module_name, effect_ref))
            .collect()
    }

    pub(super) fn canonical_effect_lookup(&self, effect_name: &str) -> String {
        self.effect_canonical
            .get(effect_name)
            .cloned()
            .unwrap_or_else(|| effect_name.to_string())
    }

    pub(super) fn resolved_effect_call_name(
        &self,
        node_id: crate::ast::NodeId,
        _op_name: &str,
        _qualifier: Option<&str>,
    ) -> Option<String> {
        self.resolved_effect_call_name_for_module(self.current_semantic_module_name(), node_id)
    }

    pub(super) fn resolved_effect_call_name_for_module(
        &self,
        module_name: &str,
        node_id: crate::ast::NodeId,
    ) -> Option<String> {
        self.front_resolution_for_module(module_name)
            .and_then(|r| r.effect_call(node_id))
            .map(|resolved| resolved.effect.as_str())
            .map(|resolved| self.canonical_effect_lookup(resolved))
    }

    pub(super) fn resolved_handler_binding_name(
        &self,
        node_id: crate::ast::NodeId,
    ) -> Option<String> {
        let normalize_lookup = |lookup_name: &str| {
            if self.handle_dynamic_vars.contains_key(lookup_name)
                || self.handle_cond_vars.contains_key(lookup_name)
                || self.handler_defs.contains_key(lookup_name)
            {
                lookup_name.to_string()
            } else {
                self.resolve_handler_name(lookup_name)
            }
        };
        self.front_resolution_for_module(self.current_semantic_module_name())
            .and_then(|r| r.handler_ref(node_id).or_else(|| r.value(node_id)))
            .map(|resolved| match resolved {
                crate::typechecker::ResolvedValue::Local { name, .. } => normalize_lookup(name),
                crate::typechecker::ResolvedValue::Global { lookup_name } => {
                    normalize_lookup(lookup_name)
                }
            })
    }

    pub(super) fn known_handler_binding_name(
        &self,
        node_id: crate::ast::NodeId,
        _fallback: &str,
    ) -> Option<String> {
        let resolved = self.resolved_handler_binding_name(node_id)?;
        if self.handler_defs.contains_key(&resolved)
            || self.handle_dynamic_vars.contains_key(&resolved)
            || self.handle_cond_vars.contains_key(&resolved)
        {
            Some(resolved)
        } else {
            None
        }
    }

    pub(super) fn resolved_env_lookup_name(
        &self,
        node_id: crate::ast::NodeId,
        fallback: &str,
    ) -> String {
        match self.resolved.get(&node_id) {
            Some(resolved)
                if resolved.source_module.as_deref() == Some(&self.current_source_module) =>
            {
                resolved.name.clone()
            }
            Some(resolved) => resolved.canonical_name.clone(),
            None => self
                .current_value_ref(node_id)
                .map(|resolved| match resolved {
                    crate::typechecker::ResolvedValue::Local { name, .. } => name.clone(),
                    crate::typechecker::ResolvedValue::Global { lookup_name } => {
                        lookup_name.clone()
                    }
                })
                .unwrap_or_else(|| fallback.to_string()),
        }
    }

    pub(super) fn record_fields_for_name(&self, name: &str) -> Option<&Vec<String>> {
        self.record_fields.get(name)
    }

    pub(super) fn resolved_record_fields(
        &self,
        node_id: crate::ast::NodeId,
        source_name: &str,
    ) -> Option<&Vec<String>> {
        let module_name = self.current_semantic_module_name();
        self.current_record_type_name(node_id)
            .and_then(|name| self.record_fields_for_name(name))
            .or_else(|| self.record_fields_for_name(source_name))
            .or_else(|| {
                let local_name = format!("{}.{}", module_name, source_name);
                self.record_fields_for_name(&local_name)
            })
            // Last-resort safety net for nodes that reach lowering without a
            // pinned `record_name` (record patterns, and any RecordCreate node
            // elaboration didn't annotate): resolve by the constructor's surface
            // name alone. A record's field layout is intrinsic to its named type,
            // but the lookups above are keyed by NodeId / the *current* module —
            // both lost when a record is inlined across modules (the fold freshens
            // the argument's NodeIds and re-bases lowering to the consumer module).
            // The constructor *tag* survives this via name-based `constructor_atoms`;
            // mirror that for the field layout. Only a *unique* `<mod>.<Name>` match
            // is accepted — an ambiguous bare name falls through so the caller errors
            // loudly rather than guess a wrong field order. RecordCreate now prefers
            // the pinned `record_name` (see `record_create_field_order`), so this is
            // the pattern path's resolver plus belt-and-suspenders for creates.
            .or_else(|| self.record_fields_by_unique_suffix(source_name))
    }

    /// Resolve the tuple field order for a `RecordCreate`. Prefers the canonical
    /// `record_name` pinned on the node by elaboration — that name travels *with*
    /// the node, so it survives the NodeId freshening that cross-module inlining
    /// does (the failure that dropped `insert_all`'s fields). Falls back to the
    /// NodeId / current-module / unique-name path for nodes elaboration didn't
    /// reach (e.g. some derive-synthesized nodes). `None` only when the record's
    /// type is wholly unresolvable — callers must treat that as a compiler bug and
    /// fail loudly, never emit a fieldless or source-ordered tuple.
    pub(super) fn record_create_field_order(
        &self,
        record_name: Option<&str>,
        node_id: crate::ast::NodeId,
        source_name: &str,
    ) -> Option<&Vec<String>> {
        record_name
            .and_then(|rn| self.record_fields_for_name(rn))
            .or_else(|| self.resolved_record_fields(node_id, source_name))
    }

    /// Find a record's field layout by its bare constructor name, scanning every
    /// registered `<module>.<Name>` key. Returns the layout only when exactly one
    /// module defines a record with that name; `None` when there is no match or
    /// the name is ambiguous across modules.
    fn record_fields_by_unique_suffix(&self, source_name: &str) -> Option<&Vec<String>> {
        let suffix = format!(".{source_name}");
        let mut matches = self
            .record_fields
            .iter()
            .filter(|(key, _)| key.ends_with(&suffix));
        match (matches.next(), matches.next()) {
            (Some((_, fields)), None) => Some(fields),
            _ => None,
        }
    }

    pub(super) fn resolved_handler_arm_effect_for_module(
        &self,
        arm: &HandlerArm,
        module_name: &str,
    ) -> Option<String> {
        self.handler_arm_effect_for_module(module_name, arm.id)
            .map(|resolved| self.canonical_effect_lookup(resolved))
    }

    pub(super) fn handler_arm_matches_effect_op_for_module(
        &self,
        arm: &HandlerArm,
        source_module: Option<&str>,
        eff: &str,
        op: &str,
    ) -> bool {
        let module_name = source_module.unwrap_or_else(|| self.current_semantic_module_name());
        self.resolved_handler_arm_effect_for_module(arm, module_name)
            .is_some_and(|resolved| resolved == eff && arm.op_name == op)
    }
}
