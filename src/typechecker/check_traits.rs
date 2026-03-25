use crate::ast;
use crate::token::Span;

use super::{Checker, ImplInfo, Scheme, Type, Diagnostic};

impl Checker {
    // --- Trait & impl helpers ---

    /// Replace occurrences of the trait's type param variable with a concrete type.
    /// Used when checking impl bodies: if the trait says `(x: a) -> String`
    /// and the impl is `for User`, we substitute a -> User to get `(x: User) -> String`.
    /// `trait_param_id` identifies which specific var to replace; other free vars are left alone.
    pub(crate) fn substitute_trait_param(&self, trait_param_id: Option<u32>, replacement: &Type, ty: &Type) -> Type {
        match ty {
            Type::Var(id) => {
                let resolved = self.sub.apply(ty);
                if resolved == *ty {
                    // Unresolved var -- only replace if it's the trait's own type param
                    match trait_param_id {
                        Some(param_id) if *id == param_id => replacement.clone(),
                        Some(_) => ty.clone(),
                        // Fallback: no param ID tracked, replace all (legacy behavior)
                        None => replacement.clone(),
                    }
                } else {
                    resolved
                }
            }
            Type::Fun(a, b, row) => Type::Fun(
                Box::new(self.substitute_trait_param(trait_param_id, replacement, a)),
                Box::new(self.substitute_trait_param(trait_param_id, replacement, b)),
                super::EffectRow {
                    effects: row.effects.iter()
                        .map(|(name, args)| {
                            (
                                name.clone(),
                                args.iter()
                                    .map(|t| self.substitute_trait_param(trait_param_id, replacement, t))
                                    .collect(),
                            )
                        })
                        .collect(),
                    tail: row.tail.as_ref().map(|t| Box::new(self.substitute_trait_param(trait_param_id, replacement, t))),
                },
            ),
            Type::Con(name, args) => Type::Con(
                name.clone(),
                args.iter()
                    .map(|a| self.substitute_trait_param(trait_param_id, replacement, a))
                    .collect(),
            ),
            Type::Record(fields) => Type::Record(
                fields
                    .iter()
                    .map(|(fname, ty)| (fname.clone(), self.substitute_trait_param(trait_param_id, replacement, ty)))
                    .collect(),
            ),
            Type::Error => Type::Error,
        }
    }

    // --- Trait & impl registration ---

    pub(crate) fn register_trait_def(
        &mut self,
        name: &str,
        type_param: &str,
        supertraits: &[(String, crate::token::Span)],
        methods: &[&ast::TraitMethod],
    ) -> Result<(), Diagnostic> {
        let mut method_sigs = Vec::new();

        for method in methods {
            let mut params_list: Vec<(String, u32)> = vec![];
            let param_types: Vec<Type> = method
                .params
                .iter()
                .map(|(_, texpr)| self.convert_type_expr(texpr, &mut params_list))
                .collect();
            let return_type = self.convert_type_expr(&method.return_type, &mut params_list);

            // Find the var ID assigned to the trait's type param
            let trait_param_id = params_list
                .iter()
                .find(|(pname, _)| pname == type_param)
                .map(|(_, id)| *id);

            method_sigs.push((
                method.name.clone(),
                param_types,
                return_type,
                trait_param_id,
            ));
        }

        // Add each method to the env as a polymorphic function with trait constraint.
        // e.g. `fun show (x: a) -> String` becomes `show : forall a. Describe a => a -> String`
        for (method_name, param_types, return_type, trait_param_id) in &method_sigs {
            let mut fun_ty = return_type.clone();
            for pt in param_types.iter().rev() {
                fun_ty = Type::arrow(pt.clone(), fun_ty);
            }
            let mut forall = Vec::new();
            super::collect_free_vars(&fun_ty, &mut forall);

            let constraints = match trait_param_id {
                Some(id) => vec![(name.to_string(), *id)],
                None => vec![],
            };

            self.env.insert(
                method_name.clone(),
                Scheme {
                    forall,
                    constraints,
                    ty: fun_ty,
                },
            );
        }

        // Record supertrait references for find-references
        for (st_name, st_span) in supertraits {
            self.lsp.type_references.push((*st_span, st_name.clone()));
        }

        self.trait_state.traits.insert(
            name.into(),
            super::TraitInfo {
                type_param: type_param.into(),
                supertraits: supertraits.iter().map(|(n, _)| n.clone()).collect(),
                methods: method_sigs,
            },
        );
        Ok(())
    }

    // Rust won't let us take an enum variant itself (Decl::ImplDef) so we just pass all its parameters
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn register_impl(
        &mut self,
        trait_name: &str,
        target_type: &str,
        type_params: &[String],
        where_clause: &[ast::TraitBound],
        needs: &[ast::EffectRef],
        methods: &[ast::ImplMethod],
        span: Span,
    ) -> Result<(), Diagnostic> {
        // Check the trait exists
        let trait_info = self.trait_state.traits.get(trait_name).cloned().ok_or_else(|| {
            Diagnostic::error_at(span, format!("impl for undefined trait: {}", trait_name))
        })?;

        // Check all required methods are provided
        let provided: Vec<&str> = methods.iter().map(|m| m.name.as_str()).collect();
        for (required_name, _, _, _) in &trait_info.methods {
            if !provided.contains(&required_name.as_str()) {
                return Err(Diagnostic::error_at(
                    span,
                    format!(
                        "impl {} for {} is missing method '{}'",
                        trait_name, target_type, required_name
                    ),
                ));
            }
        }

        // Check for duplicate methods
        let mut seen_methods: std::collections::HashSet<&str> = std::collections::HashSet::new();
        for name in &provided {
            if !seen_methods.insert(name) {
                return Err(Diagnostic::error_at(
                    span,
                    format!(
                        "impl {} for {} has duplicate method '{}'",
                        trait_name, target_type, name
                    ),
                ));
            }
        }

        // Check for extra methods not in the trait
        for name in &provided {
            if !trait_info.methods.iter().any(|(n, _, _, _)| n == name) {
                return Err(Diagnostic::error_at(
                    span,
                    format!(
                        "impl {} for {} has method '{}' not defined in trait",
                        trait_name, target_type, name
                    ),
                ));
            }
        }

        // Type-check each method body against the trait's expected signature.
        // Substitute the trait's type param with the concrete target type.
        // For parameterized impls (e.g. `impl Show for Box a`), use fresh vars for type params.
        let target = if type_params.is_empty() {
            Type::Con(target_type.into(), vec![])
        } else {
            let param_vars: Vec<Type> = type_params.iter().map(|_| self.fresh_var()).collect();
            // Register where clause bounds on the fresh type vars so method bodies
            // can use trait methods on those vars (e.g. `show x` where `x: a` and `a: Show`).
            for bound in where_clause {
                if let Some(idx) = type_params.iter().position(|p| p == &bound.type_var)
                    && let Some(Type::Var(var_id)) = param_vars.get(idx)
                {
                    self.trait_state.where_bound_var_names
                        .insert(*var_id, bound.type_var.clone());
                    for (trait_req, trait_span) in &bound.traits {
                        self.lsp.type_references.push((*trait_span, trait_req.clone()));
                        self.trait_state.where_bounds
                            .entry(*var_id)
                            .or_default()
                            .insert(trait_req.clone());
                    }
                }
            }
            Type::Con(target_type.into(), param_vars)
        };

        let declared_effects: std::collections::HashSet<String> =
            needs.iter().map(|e| e.name.clone()).collect();

        for m in methods {
            let (method_name, params, body) = (&m.name, &m.params, &m.body);
            let trait_method = trait_info
                .methods
                .iter()
                .find(|(n, _, _, _)| n == method_name)
                .unwrap(); // already validated above

            let trait_param_id = trait_method.3;
            let expected_params: Vec<Type> = trait_method
                .1
                .iter()
                .map(|t| self.substitute_trait_param(trait_param_id, &target, t))
                .collect();
            let expected_return = self.substitute_trait_param(trait_param_id, &target, &trait_method.2);

            let saved_env = self.env.clone();
            let body_scope = self.enter_scope();
            let trait_saved_effs = self.save_effects();

            // Re-insert the trait's method schemes so that method calls inside
            // the impl body resolve to the trait signature, not to a user-defined
            // function that happens to share the name. The saved_env restore at
            // the end of this loop iteration will bring back the user's entry.
            for (m_name, m_param_types, m_return_type, _) in &trait_info.methods {
                let mut fun_ty = m_return_type.clone();
                for pt in m_param_types.iter().rev() {
                    fun_ty = Type::arrow(pt.clone(), fun_ty);
                }
                let mut forall = Vec::new();
                super::collect_free_vars(&fun_ty, &mut forall);
                let constraints: Vec<(String, u32)> = forall
                    .iter()
                    .map(|&var_id| (trait_name.to_string(), var_id))
                    .collect();
                self.env.insert(
                    m_name.clone(),
                    Scheme { forall, constraints, ty: fun_ty },
                );
            }

            // Bind params with expected types
            for (i, pat) in params.iter().enumerate() {
                if i < expected_params.len() {
                    self.bind_pattern(pat, &expected_params[i])?;
                }
            }

            // Infer body and check it matches the expected return type
            let body_ty = self.infer_expr(body)?;
            self.unify_at(&body_ty, &expected_return, body.span)
                .map_err(|e| {
                    Diagnostic::error_at(
                        span,
                        format!(
                            "in impl {} for {}, method '{}': {}",
                            trait_name, target_type, method_name, e.message
                        ),
                    )
                })?;

            // Check that body effects are covered by the impl's needs declaration
            let body_effs = self.restore_effects(trait_saved_effs);
            let scope_result = self.exit_scope(body_scope);
            let body_field_candidates = scope_result.field_candidates;
            let body_effects: std::collections::HashSet<String> = body_effs
                .effects.iter().map(|(n, _)| n.clone()).collect();
            if !body_effects.is_empty() || !declared_effects.is_empty() {
                let undeclared: Vec<String> = body_effects.difference(&declared_effects).cloned().collect();
                if !undeclared.is_empty() {
                    let mut sorted = undeclared;
                    sorted.sort();
                    let label = format!(
                        "impl {} for {}, method '{}'",
                        trait_name, target_type, method_name
                    );
                    if declared_effects.is_empty() {
                        return Err(Diagnostic::error_at(
                            body.span,
                            format!("{} uses effects {{{}}} but has no 'needs' declaration", label, sorted.join(", ")),
                        ));
                    } else {
                        return Err(Diagnostic::error_at(
                            body.span,
                            format!("{} uses effects {{{}}} not declared in its 'needs' clause", label, sorted.join(", ")),
                        ));
                    }
                }
            }

            // Register effects so callers of this method know what they propagate.
            // Union with any effects already registered (from other impls of the same method).
            if !declared_effects.is_empty() {
                self.effect_meta.known_funs.insert(method_name.clone());
            }

            // Check for unresolved field access ambiguities at end of method body
            for (var_id, (record_names, field_span)) in body_field_candidates {
                let resolved = self.sub.apply(&Type::Var(var_id));
                if matches!(resolved, Type::Var(_)) {
                    let mut names = record_names.clone();
                    names.sort();
                    return Err(Diagnostic::error_at(
                        field_span,
                        format!(
                            "ambiguous field access: could be any of [{}] which all have this field; add a type annotation to disambiguate",
                            names.join(", ")
                        ),
                    ));
                }
            }

            self.env = saved_env;
        }

        // Build param_constraints from where clause
        let mut param_constraints = Vec::new();
        for bound in where_clause {
            let param_idx = type_params.iter().position(|p| p == &bound.type_var);
            match param_idx {
                Some(idx) => {
                    for (trait_req, _) in &bound.traits {
                        param_constraints.push((trait_req.clone(), idx));
                    }
                }
                None => {
                    return Err(Diagnostic::error_at(
                        span,
                        format!(
                            "where clause references unknown type variable '{}' (params: {:?})",
                            bound.type_var, type_params
                        ),
                    ));
                }
            }
        }

        let key = (trait_name.to_string(), target_type.to_string());
        if self.trait_state.impls.contains_key(&key) {
            return Err(Diagnostic::error_at(
                span,
                format!(
                    "duplicate impl: {} is already implemented for {}",
                    trait_name, target_type
                ),
            ));
        }
        self.trait_state.impls.insert(
            key,
            ImplInfo {
                param_constraints,
                span: Some(span),
            },
        );
        Ok(())
    }
}
