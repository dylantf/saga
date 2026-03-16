use crate::ast;
use crate::token::Span;

use super::{Checker, ImplInfo, Scheme, Type, TypeError};

impl Checker {
    // --- Trait & impl helpers ---

    /// Replace occurrences of a trait's type param variable with a concrete type.
    /// Used when checking impl bodies: if the trait says `(x: a) -> String`
    /// and the impl is `for User`, we substitute a -> User to get `(x: User) -> String`.
    pub(crate) fn substitute_trait_param(&self, replacement: &Type, ty: &Type) -> Type {
        match ty {
            Type::Var(_) => {
                let resolved = self.sub.apply(ty);
                if resolved == *ty {
                    // Unresolved var -- replace all free vars (trait methods only
                    // have the one type param).
                    replacement.clone()
                } else {
                    resolved
                }
            }
            Type::Arrow(a, b) => Type::Arrow(
                Box::new(self.substitute_trait_param(replacement, a)),
                Box::new(self.substitute_trait_param(replacement, b)),
            ),
            Type::EffArrow(a, b, effs) => Type::EffArrow(
                Box::new(self.substitute_trait_param(replacement, a)),
                Box::new(self.substitute_trait_param(replacement, b)),
                effs.iter()
                    .map(|(name, args)| {
                        (
                            name.clone(),
                            args.iter()
                                .map(|t| self.substitute_trait_param(replacement, t))
                                .collect(),
                        )
                    })
                    .collect(),
            ),
            Type::Con(name, args) => Type::Con(
                name.clone(),
                args.iter()
                    .map(|a| self.substitute_trait_param(replacement, a))
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
        supertraits: &[String],
        methods: &[ast::TraitMethod],
    ) -> Result<(), TypeError> {
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
                fun_ty = Type::Arrow(Box::new(pt.clone()), Box::new(fun_ty));
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

        self.traits.insert(
            name.into(),
            super::TraitInfo {
                type_param: type_param.into(),
                supertraits: supertraits.to_vec(),
                methods: method_sigs
                    .into_iter()
                    .map(|(n, pts, rt, _)| (n, pts, rt))
                    .collect(),
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
        methods: &[(String, Vec<ast::Pat>, ast::Expr)],
        span: Span,
    ) -> Result<(), TypeError> {
        // Check the trait exists
        let trait_info = self.traits.get(trait_name).cloned().ok_or_else(|| {
            TypeError::at(span, format!("impl for undefined trait: {}", trait_name))
        })?;

        // Check all required methods are provided
        let provided: Vec<&str> = methods.iter().map(|(n, _, _)| n.as_str()).collect();
        for (required_name, _, _) in &trait_info.methods {
            if !provided.contains(&required_name.as_str()) {
                return Err(TypeError::at(
                    span,
                    format!(
                        "impl {} for {} is missing method '{}'",
                        trait_name, target_type, required_name
                    ),
                ));
            }
        }

        // Check for extra methods not in the trait
        for name in &provided {
            if !trait_info.methods.iter().any(|(n, _, _)| n == name) {
                return Err(TypeError::at(
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
                    self.where_bound_var_names
                        .insert(*var_id, bound.type_var.clone());
                    for trait_req in &bound.traits {
                        self.where_bounds
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

        for (method_name, params, body) in methods {
            let trait_method = trait_info
                .methods
                .iter()
                .find(|(n, _, _)| n == method_name)
                .unwrap(); // already validated above

            let expected_params: Vec<Type> = trait_method
                .1
                .iter()
                .map(|t| self.substitute_trait_param(&target, t))
                .collect();
            let expected_return = self.substitute_trait_param(&target, &trait_method.2);

            let saved_env = self.env.clone();
            let saved_effects = std::mem::take(&mut self.current_effects);
            let saved_effect_cache = std::mem::take(&mut self.effect_type_param_cache);
            let saved_field_candidates = std::mem::take(&mut self.field_candidates);

            // Bind params with expected types
            for (i, pat) in params.iter().enumerate() {
                if i < expected_params.len() {
                    self.bind_pattern(pat, &expected_params[i])?;
                }
            }

            // Infer body and check it matches the expected return type
            let body_ty = self.infer_expr(body)?;
            self.unify_at(&body_ty, &expected_return, body.span())
                .map_err(|e| {
                    TypeError::at(
                        span,
                        format!(
                            "in impl {} for {}, method '{}': {}",
                            trait_name, target_type, method_name, e.message
                        ),
                    )
                })?;

            // Check that body effects are covered by the impl's needs declaration
            let body_effects = std::mem::replace(&mut self.current_effects, saved_effects);
            self.effect_type_param_cache = saved_effect_cache;
            if !body_effects.is_empty() || !declared_effects.is_empty() {
                let undeclared: Vec<_> = body_effects.difference(&declared_effects).collect();
                if !undeclared.is_empty() {
                    let mut effects: Vec<_> = undeclared.into_iter().cloned().collect();
                    effects.sort();
                    if declared_effects.is_empty() {
                        return Err(TypeError::at(
                            body.span(),
                            format!(
                                "impl {} for {}, method '{}' uses effects {{{}}} but the impl has no 'needs' declaration",
                                trait_name,
                                target_type,
                                method_name,
                                effects.join(", ")
                            ),
                        ));
                    } else {
                        return Err(TypeError::at(
                            body.span(),
                            format!(
                                "impl {} for {}, method '{}' uses effects {{{}}} not declared in 'needs'",
                                trait_name,
                                target_type,
                                method_name,
                                effects.join(", ")
                            ),
                        ));
                    }
                }
            }

            // Register effects so callers of this method know what they propagate.
            // Union with any effects already registered (from other impls of the same method).
            if !declared_effects.is_empty() {
                self.fun_effects
                    .entry(method_name.clone())
                    .or_default()
                    .extend(declared_effects.iter().cloned());
            }

            // Check for unresolved field access ambiguities at end of method body
            let body_field_candidates =
                std::mem::replace(&mut self.field_candidates, saved_field_candidates);
            for (var_id, (record_names, field_span)) in body_field_candidates {
                let resolved = self.sub.apply(&Type::Var(var_id));
                if matches!(resolved, Type::Var(_)) {
                    let mut names = record_names.clone();
                    names.sort();
                    return Err(TypeError::at(
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
                    for trait_req in &bound.traits {
                        param_constraints.push((trait_req.clone(), idx));
                    }
                }
                None => {
                    return Err(TypeError::at(
                        span,
                        format!(
                            "where clause references unknown type variable '{}' (params: {:?})",
                            bound.type_var, type_params
                        ),
                    ));
                }
            }
        }

        self.trait_impls.insert(
            (trait_name.into(), target_type.into()),
            ImplInfo {
                param_constraints,
                span: Some(span),
            },
        );
        Ok(())
    }
}
