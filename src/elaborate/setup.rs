use super::*;

impl Elaborator {
    pub(crate) fn resolved_trait_name(&self, id: crate::ast::NodeId, source: &str) -> String {
        self.resolution.trait_ref(id).unwrap_or(source).to_string()
    }

    pub(crate) fn resolved_impl_trait_name(&self, id: crate::ast::NodeId, source: &str) -> String {
        self.resolution
            .impl_trait_ref(id)
            .or_else(|| self.resolution.trait_ref(id))
            .unwrap_or(source)
            .to_string()
    }

    pub(crate) fn resolved_impl_target_type(&self, id: crate::ast::NodeId, source: &str) -> String {
        self.resolution
            .impl_target_type_ref(id)
            .unwrap_or(source)
            .to_string()
    }

    pub(crate) fn resolved_type_name(&self, id: crate::ast::NodeId, source: &str) -> String {
        self.resolution.type_ref(id).unwrap_or(source).to_string()
    }

    pub(crate) fn resolved_global_value_name(&self, id: crate::ast::NodeId) -> Option<&str> {
        match self.resolution.value(id) {
            Some(ResolvedValue::Global { lookup_name }) => Some(lookup_name.as_str()),
            _ => None,
        }
    }

    pub(crate) fn fun_dict_params_for_callee(
        &self,
        source_name: &str,
        node_id: crate::ast::NodeId,
    ) -> Option<Vec<(String, String)>> {
        // A reference that resolves to a local binding is NOT a top-level
        // dict-parameterized function, even when it shares a name with one
        // (e.g. a parameter `value` shadowing a global
        // `value : a -> _ where {a: Pg}`). Matching it by bare name would wrap
        // the local with dict arguments and apply it like a function at runtime
        // (`apply 18(dict)` → `{badfun,18}`). The only locals that legitimately
        // carry call-site dicts are eta-expanded dict-parameterized
        // let-bindings, which register their name in `let_dict_pat_ids`.
        if matches!(
            self.resolution.value(node_id),
            Some(ResolvedValue::Local { .. })
        ) && !self.let_dict_pat_ids.contains_key(source_name)
        {
            return None;
        }
        if let Some(params) = self.fun_dict_params.get(source_name).cloned() {
            return Some(params);
        }
        if let Some(resolved_name) = self.resolved_global_value_name(node_id)
            && let Some(params) = self.fun_dict_params.get(resolved_name).cloned()
        {
            return Some(params);
        }
        if let Some(canonical) = self.scope_map_values.get(source_name)
            && let Some(params) = self.fun_dict_params.get(canonical).cloned()
        {
            return Some(params);
        }
        None
    }

    /// Resolve trait type args via the resolution map. For App heads (e.g.
    /// `Rep__Box a`), uses the head name — only the head identifies the impl
    /// for dict-name purposes.
    pub(crate) fn resolved_trait_type_args(&self, args: &[crate::ast::TypeExpr]) -> Vec<String> {
        args.iter()
            .map(|te| {
                let head = te.head_name().unwrap_or("");
                self.resolved_type_name(te.head_id().unwrap_or(te.id()), head)
            })
            .collect()
    }

    pub(crate) fn impl_target_key(
        &self,
        canonical_target: &str,
        target_type_expr: Option<&crate::ast::TypeExpr>,
        type_params: &[crate::ast::TypeParam],
    ) -> String {
        let arity = target_type_expr
            .filter(|expr| expr.head_name() == Some("Tuple"))
            .map(|expr| expr.app_arg_count())
            .unwrap_or(type_params.len());
        crate::typechecker::arity_keyed_target_name(canonical_target, arity)
    }

    pub(crate) fn new(result: &CheckResult, module_name: &str) -> Self {
        // Build inferred dict params from checker's env (for functions without
        // explicit where clauses that still have inferred trait constraints).
        // Traits that use operator dispatch, not dictionary dispatch.
        // These should not generate dict params.
        let operator_traits: std::collections::HashSet<&str> = ["Num", "Eq"].into_iter().collect();

        let scheme_dict_params = |scheme: &crate::typechecker::Scheme| -> Vec<(String, String)> {
            scheme
                .constraints
                .iter()
                .filter(|(trait_name, _, _)| !operator_traits.contains(trait_name.as_str()))
                .map(|(trait_name, var_id, extras)| {
                    // Same determinant-extra disambiguation as the where-clause
                    // path, so inferred multi-determinant constraints on one var
                    // get distinct dict-param names.
                    let suffix = dict_var_suffix_from_types(&result.traits, trait_name, extras);
                    (trait_name.clone(), format!("v{}{}", var_id, suffix))
                })
                .collect()
        };

        let mut inferred_dict_params: HashMap<String, Vec<(String, String)>> = HashMap::new();
        for (name, scheme) in result.env.iter() {
            let dict_params = scheme_dict_params(scheme);
            if !dict_params.is_empty() {
                inferred_dict_params.insert(name.to_string(), dict_params);
            }
        }
        for info in result.codegen_info().values() {
            let origins: HashMap<&str, &str> = info
                .export_origins
                .iter()
                .map(|(surface, origin)| (surface.as_str(), origin.as_str()))
                .collect();
            for (name, scheme) in &info.exports {
                let dict_params = scheme_dict_params(scheme);
                if dict_params.is_empty() {
                    continue;
                }
                if let Some(origin) = origins.get(name.as_str()) {
                    inferred_dict_params
                        .entry((*origin).to_string())
                        .or_insert_with(|| dict_params.clone());
                }
                if name.contains('.') {
                    inferred_dict_params
                        .entry(name.clone())
                        .or_insert_with(|| dict_params.clone());
                }
            }
        }
        // Register dict params under all user-facing name forms that resolve
        // to a canonical name with dict params (so "List.sort" finds the params
        // registered under "Std.List.sort").
        for (user_name, canonical) in &result.scope_map.values {
            if user_name != canonical
                && let Some(params) = inferred_dict_params.get(canonical).cloned()
            {
                inferred_dict_params
                    .entry(user_name.clone())
                    .or_insert(params);
            }
        }
        // Merge let-binding dict params (from local let bindings with trait constraints).
        // Keyed by (name, pat_id) to avoid collisions between same-named bindings
        // in different scopes. We store the pat_id set so the elaborator can check
        // whether a specific binding needs dict wrapping.
        let mut let_binding_arities: HashMap<String, usize> = HashMap::new();
        let mut let_dict_pat_ids: HashMap<String, HashSet<crate::ast::NodeId>> = HashMap::new();
        for ((name, pat_id), info) in &result.let_dict_params {
            inferred_dict_params
                .entry(name.clone())
                .or_insert_with(|| info.params.clone());
            let_binding_arities.insert(name.clone(), info.value_arity);
            let_dict_pat_ids
                .entry(name.clone())
                .or_default()
                .insert(*pat_id);
        }

        // Build evidence lookup by node ID
        let mut evidence_by_node: HashMap<crate::ast::NodeId, Vec<TraitEvidence>> = HashMap::new();
        for ev in &result.evidence {
            evidence_by_node
                .entry(ev.node_id)
                .or_default()
                .push(ev.clone());
        }

        // Erlang module name: "Foo.Bar" -> "foo_bar", "" -> ""
        let erlang_module = if module_name.is_empty() {
            String::new()
        } else {
            module_name
                .split('.')
                .map(|s| s.to_lowercase())
                .collect::<Vec<_>>()
                .join("_")
        };

        // Pre-populate dict_names from imported modules' codegen info
        let mut dict_names = HashMap::new();
        let mut impl_dict_params_from_imports: HashMap<ImplKey, Vec<(String, usize)>> =
            HashMap::new();
        for info in result.codegen_info().values() {
            for d in &info.trait_impl_dicts {
                dict_names.insert(
                    (
                        d.trait_name.clone(),
                        d.trait_type_args.clone(),
                        d.target_type.clone(),
                    ),
                    d.dict_name.clone(),
                );
                impl_dict_params_from_imports.insert(
                    (
                        d.trait_name.clone(),
                        d.trait_type_args.clone(),
                        d.target_type.clone(),
                    ),
                    d.param_constraints.clone(),
                );
            }
        }

        // Per-operation `where` constraints, keyed by (effect, op). The op
        // signature stores constraints as (trait, var_id, _); translate the var
        // id back to its source name via `where_bound_var_names` so the dict
        // param name matches what the handler arm body and call site resolve to.
        let mut op_dict_params: HashMap<(String, String), Vec<(String, String)>> = HashMap::new();
        for (effect_name, info) in &result.effects {
            for op in &info.ops {
                let mut pairs = Vec::new();
                for (trait_name, var_id, _) in &op.constraints {
                    if trait_name == "Num" || trait_name == "Eq" {
                        continue;
                    }
                    // The source var name (`where {cols: Link …}` → "cols")
                    // lives in `where_bound_var_names`, keyed by var id. For an
                    // *imported* effect the op's constraint var ids were minted
                    // in the defining module, so this importer's map lacks them.
                    // The name only shapes a handler arm's dict-param name
                    // (imported-effect arms are elaborated in the defining
                    // module, where the name is present); at an `op!` call site —
                    // the cross-module case — only the constraint's trait and
                    // its position matter, since dicts are appended positionally.
                    // So fall back to a stable per-var name, keeping the full
                    // constraint set rather than silently dropping it (which left
                    // the call site short of dict args → an arity crash).
                    let var_name = result
                        .where_bound_var_names
                        .get(var_id)
                        .cloned()
                        .unwrap_or_else(|| format!("v{var_id}"));
                    pairs.push((trait_name.clone(), var_name));
                }
                if !pairs.is_empty() {
                    op_dict_params.insert((effect_name.clone(), op.name.clone()), pairs);
                }
            }
        }

        Elaborator {
            trait_methods: HashMap::new(),
            fun_dict_params: inferred_dict_params,
            handler_dict_params: HashMap::new(),
            op_dict_params,
            dict_names,
            impl_dict_params: impl_dict_params_from_imports,
            impl_where_app_dict_params: HashMap::new(),
            impl_infos: result.trait_impls.clone(),
            traits: result.traits.clone(),
            evidence_by_node,
            current_fun: None,
            current_impl_trait: None,
            current_dict_params: HashMap::new(),
            current_dict_params_by_var: HashMap::new(),
            erlang_module,
            let_binding_arities,
            let_dict_pat_ids,
            scope_map_values: result.scope_map.values.clone(),
            scope_map_effects: result.scope_map.effects.clone(),
            resolution: result.resolution.clone(),
            type_at_node: result.type_at_node.clone(),
            records: result.records.clone(),
            where_bound_var_names: result.where_bound_var_names.clone(),
        }
    }
}
