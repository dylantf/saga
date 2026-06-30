use crate::ast::{self, TypeParam};
use crate::token::Span;

use super::{Checker, Diagnostic, ImplInfo, Scheme, TraitMethodEffectSig, Type};

fn trait_method_effect_sig(ty: &Type) -> TraitMethodEffectSig {
    let mut user_arity = 0;
    let mut effects = std::collections::BTreeSet::new();
    let mut is_open_row = false;
    let mut current = ty;
    while let Type::Fun(_, ret, row) = current {
        user_arity += 1;
        for entry in &row.effects {
            effects.insert(entry.name.clone());
        }
        if row.is_open() {
            is_open_row = true;
        }
        current = ret;
    }
    TraitMethodEffectSig {
        effects: effects.into_iter().collect(),
        is_open_row,
        user_arity,
    }
}

pub(crate) fn target_key_for_type(ty: &Type) -> Option<String> {
    match ty {
        Type::Con(name, args) => Some(super::arity_keyed_target_name(name, args.len())),
        _ => None,
    }
}

pub(crate) fn match_type_pattern(
    pattern: &Type,
    actual: &Type,
    subst: &mut std::collections::HashMap<u32, Type>,
) -> bool {
    match (pattern, actual) {
        (Type::Var(id), actual) => match subst.get(id).cloned() {
            Some(existing) => existing == *actual,
            None => {
                subst.insert(*id, actual.clone());
                true
            }
        },
        (Type::Con(pn, pa), Type::Con(an, aa)) => {
            pn == an
                && pa.len() == aa.len()
                && pa
                    .iter()
                    .zip(aa.iter())
                    .all(|(p, a)| match_type_pattern(p, a, subst))
        }
        _ => false,
    }
}

pub(crate) fn substitute_pattern_vars(
    ty: &Type,
    subst: &std::collections::HashMap<u32, Type>,
) -> Type {
    match ty {
        Type::Var(id) => subst.get(id).cloned().unwrap_or(Type::Var(*id)),
        Type::Con(name, args) => Type::Con(
            name.clone(),
            args.iter()
                .map(|arg| substitute_pattern_vars(arg, subst))
                .collect(),
        ),
        Type::Fun(a, b, row) => Type::Fun(
            Box::new(substitute_pattern_vars(a, subst)),
            Box::new(substitute_pattern_vars(b, subst)),
            row.clone(),
        ),
        Type::Record(fields) => Type::Record(
            fields
                .iter()
                .map(|(name, ty)| (name.clone(), substitute_pattern_vars(ty, subst)))
                .collect(),
        ),
        other => other.clone(),
    }
}

fn direct_target_var_index(target: &Type, var_id: u32) -> Option<usize> {
    let Type::Con(_, args) = target else {
        return None;
    };
    args.iter()
        .position(|arg| matches!(arg, Type::Var(id) if *id == var_id))
}

impl Checker {
    // --- Trait & impl helpers ---

    /// Resolve a trait name to its canonical form.
    /// Tries: exact match in traits -> scope_map.traits -> current_module.Name.
    pub(crate) fn resolve_trait_name(&self, name: &str) -> Option<String> {
        // Exact match (already canonical)
        if self.trait_state.traits.contains_key(name) {
            return Some(name.to_string());
        }
        // Scope map resolution (bare or aliased -> canonical)
        if let Some(canonical) = self.scope_map.resolve_trait(name)
            && self.trait_state.traits.contains_key(canonical)
        {
            return Some(canonical.to_string());
        }
        // Local module: Module.Name
        if let Some(module) = &self.current_module {
            let canonical = format!("{}.{}", module, name);
            if self.trait_state.traits.contains_key(&canonical) {
                return Some(canonical);
            }
        }
        // Builtin traits (Num, Eq) are registered under bare names
        None
    }

    // --- Trait & impl registration ---

    pub(crate) fn register_trait_def(
        &mut self,
        name: &str,
        type_params: &[TypeParam],
        supertraits: &[ast::TraitRef],
        methods: &[&ast::TraitMethod],
    ) -> Result<(), Diagnostic> {
        // Compute canonical name early — used in scheme constraints below
        let canonical_name = match &self.current_module {
            Some(module) => super::canonical_join(module, name),
            None => name.to_string(),
        };

        let self_param = type_params
            .first()
            .map(|tp| tp.name.as_str())
            .unwrap_or("a");
        let mut method_sigs = Vec::new();

        for method in methods {
            // Pre-seed type parameters with their declared kinds so that
            // method-signature conversion mints fresh vars of the right kind
            // when they're first referenced.
            let mut params_list: Vec<(String, u32)> = type_params
                .iter()
                .map(|tp| {
                    let var = self.fresh_var();
                    let id = match var {
                        Type::Var(id) => id,
                        _ => unreachable!(),
                    };
                    (tp.name.clone(), id)
                })
                .collect();
            let param_types: Vec<Type> = method
                .params
                .iter()
                .map(|(_, texpr)| self.convert_user_type_expr(texpr, &mut params_list))
                .collect();
            let return_type = self.convert_user_type_expr(&method.return_type, &mut params_list);

            // Find the var ID assigned to the trait's self type param
            let trait_param_id = params_list
                .iter()
                .find(|(pname, _)| pname == self_param)
                .map(|(_, id)| *id);

            let effect_row = self.build_effect_row_from_refs(
                &method.effects,
                &method.effect_row_var,
                &mut params_list,
            )?;
            for eff in &method.effects {
                self.record_effect_ref(eff);
            }

            method_sigs.push((
                method.name.clone(),
                param_types,
                return_type,
                effect_row,
                trait_param_id,
                params_list,
            ));
        }

        // Add each method to the env as a polymorphic function with trait constraint.
        // e.g. `fun show (x: a) -> String` becomes `show : forall a. Describe a => a -> String`
        // For phantom type params (not mentioned in the method signature), we create
        // fresh vars and add them to forall so the constraint flows through instantiation.
        let mut trait_method_sigs = Vec::new();
        for (method_name, param_types, return_type, effect_row, trait_param_id, mut params_list) in
            method_sigs
        {
            let fun_ty = self.function_type_with_innermost_effects(
                &param_types,
                return_type.clone(),
                effect_row,
            );
            let mut forall = Vec::new();
            super::collect_free_vars(&fun_ty, &mut forall);

            // Ensure all trait type params appear in `forall`. Pre-seeded
            // params (above) already have var IDs in `params_list`; phantom
            // params not free in `fun_ty` are added here so the constraint
            // can reference them.
            for tp in type_params {
                let tp_name = tp.name.as_str();
                let id = params_list
                    .iter()
                    .find(|(n, _)| n == tp_name)
                    .map(|(_, id)| *id)
                    .unwrap_or_else(|| {
                        let fresh = self.fresh_var();
                        let id = match fresh {
                            Type::Var(id) => id,
                            _ => unreachable!(),
                        };
                        params_list.push((tp.name.clone(), id));
                        id
                    });
                if !forall.contains(&id) {
                    forall.push(id);
                }
            }

            // Build constraint with self param and extra type params.
            let self_id = params_list
                .iter()
                .find(|(n, _)| n == self_param)
                .map(|(_, id)| *id);
            let extra_types: Vec<Type> = type_params[1..]
                .iter()
                .filter_map(|tp| {
                    let tp_name = tp.name.as_str();
                    params_list
                        .iter()
                        .find(|(n, _)| n == tp_name)
                        .map(|(_, id)| Type::Var(*id))
                })
                .collect();
            let constraints = match self_id {
                Some(id) => vec![(canonical_name.clone(), id, extra_types)],
                None => vec![],
            };

            let effect_sig = trait_method_effect_sig(&fun_ty);
            let scheme = Scheme {
                forall,
                constraints,
                ty: fun_ty,
            };

            // Single canonical-keyed env entry. Use sites in the defining
            // module resolve through `ResolutionResult` to the canonical
            // method name, and importers re-register under the same key from
            // the scheme stored on `TraitMethodInfo` below. The scheme itself
            // is owned by `TraitInfo.methods` — env is just a cached lookup
            // view keyed by canonical name.
            let canonical_method = super::canonical_join(&canonical_name, &method_name);
            self.env.insert(canonical_method, scheme.clone());

            trait_method_sigs.push(super::TraitMethodInfo {
                name: method_name,
                param_types,
                return_type,
                trait_param_id,
                scheme,
                effect_sig,
            });
        }

        // Record supertrait references for find-references
        for tr in supertraits {
            let resolved = self.resolved_trait_name_at(tr.id, &tr.name);
            self.lsp.type_references.push((tr.span, resolved));
        }

        // Also register scope_map entry for local traits: bare -> canonical
        if canonical_name != name {
            self.scope_map
                .traits
                .entry(name.to_string())
                .or_insert_with(|| canonical_name.clone());
            self.scope_map
                .traits
                .entry(canonical_name.clone())
                .or_insert_with(|| canonical_name.clone());
        }
        // Local trait methods: register both bare visibility (for use sites
        // in this module) and canonical forms in scope.values for qualified
        // lookups. Mirrors the import-side registration in check_module.rs.
        self.scope_map
            .register_trait_methods(&canonical_name, methods.iter().map(|m| m.name.as_str()));
        for method in methods {
            let method_canonical = super::canonical_join(&canonical_name, &method.name);
            self.scope_map
                .values
                .entry(method_canonical.clone())
                .or_insert_with(|| method_canonical.clone());
        }
        // Resolve supertrait names to canonical form
        let resolved_supertraits: Vec<String> = supertraits
            .iter()
            .map(|tr| self.resolved_trait_name_at(tr.id, &tr.name))
            .collect();
        self.trait_state.traits.insert(
            canonical_name,
            super::TraitInfo {
                type_params: type_params.iter().map(|tp| tp.name.clone()).collect(),
                supertraits: resolved_supertraits,
                methods: trait_method_sigs,
            },
        );
        Ok(())
    }

    // Rust won't let us take an enum variant itself (Decl::ImplDef) so we just pass all its parameters
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn register_impl(
        &mut self,
        impl_id: ast::NodeId,
        trait_name: &str,
        trait_type_args: &[ast::TypeExpr],
        target_type: &str,
        type_params: &[TypeParam],
        target_type_expr: Option<&ast::TypeExpr>,
        where_clause: &[ast::TraitBound],
        where_apps: &[ast::TraitApp],
        needs: &[ast::EffectRef],
        methods: &[ast::ImplMethod],
        span: Span,
    ) -> Result<(), Diagnostic> {
        // Head names for the impls HashMap key (used everywhere as a
        // string-keyed coarse index — exact type identity isn't relevant).
        let trait_type_arg_names: Vec<String> = trait_type_args
            .iter()
            .map(|te| {
                let head = te.head_name().unwrap_or("");
                self.resolved_type_name(te.head_id().unwrap_or(te.id()), head)
            })
            .collect();
        let trait_type_args_names = &trait_type_arg_names;
        // Resolve trait name to canonical form
        let trait_name = self.resolved_impl_trait_name(impl_id, trait_name);
        let trait_name = trait_name.as_str();
        // Check the trait exists
        let trait_info = self
            .trait_state
            .traits
            .get(trait_name)
            .cloned()
            .ok_or_else(|| {
                Diagnostic::error_at(span, format!("impl for undefined trait: {}", trait_name))
            })?;

        // Validate trait type arg arity: extra type params (all except the self param at index 0)
        let expected_extra = trait_info.type_params.len().saturating_sub(1);
        if trait_type_arg_names.len() != expected_extra {
            return Err(Diagnostic::error_at(
                span,
                format!(
                    "trait {} expects {} type argument(s), but {} were provided",
                    trait_name,
                    expected_extra,
                    trait_type_arg_names.len()
                ),
            ));
        }

        // Check all required methods are provided. Default bodies are
        // injected as real ImplMethods by `derive::inherit_trait_defaults`
        // pre-typecheck, so by this point an impl missing a method genuinely
        // has no implementation (explicit or inherited).
        let provided: Vec<&str> = methods.iter().map(|m| m.name.as_str()).collect();
        for required in &trait_info.methods {
            if !provided.contains(&required.name.as_str()) {
                return Err(Diagnostic::error_at(
                    span,
                    format!(
                        "impl {} for {} is missing method '{}'",
                        trait_name, target_type, required.name
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
            if !trait_info.methods.iter().any(|m| &m.name == name) {
                return Err(Diagnostic::error_at(
                    span,
                    format!(
                        "impl {} for {} has method '{}' not defined in trait",
                        trait_name, target_type, name
                    ),
                ));
            }
        }

        // Resolve target type and run overlap/coherence checks before the
        // body type-check. Method bodies mutate the substitution map (they
        // unify the trait's phantom type vars like `b` in `ConvertTo a b` with
        // the impl's return type), so the second impl's body would fail to
        // unify before the overlap check has a chance to fire.
        let resolved_target_type = self.resolved_impl_target_type_name(impl_id, target_type);
        // Reject impls whose target is a type alias — aliases are structural,
        // so an impl on the alias would be ambiguous with an impl on the
        // underlying type. Tell the user to impl on the unfolded form.
        if self.type_aliases.contains_key(&resolved_target_type) {
            return Err(Diagnostic::error_at(
                span,
                format!(
                    "cannot impl trait for type alias `{}` — impl for the underlying type instead",
                    target_type
                ),
            ));
        }
        // Convert the full target pattern first. Parsed source impls provide
        // `target_type_expr`; synthesized impls fall back to the legacy
        // `target_type + type_params` representation.
        let mut impl_type_vars: Vec<(String, u32)> = Vec::new();
        let target = if let Some(target_expr) = target_type_expr {
            self.convert_type_expr(target_expr, &mut impl_type_vars)
        } else if type_params.is_empty() {
            Type::Con(resolved_target_type.clone(), vec![])
        } else {
            let mut param_vars = Vec::new();
            for tp in type_params {
                let fresh = self.fresh_var();
                if let Type::Var(id) = fresh {
                    impl_type_vars.push((tp.name.clone(), id));
                }
                param_vars.push(fresh);
            }
            Type::Con(resolved_target_type.clone(), param_vars)
        };
        let Some(target_key) = target_key_for_type(&target) else {
            return Err(Diagnostic::error_at(
                span,
                "impl target must be a named or tuple type".to_string(),
            ));
        };
        let dup_key = (
            trait_name.to_string(),
            trait_type_args_names.clone(),
            target_key.clone(),
        );
        if self.trait_state.impls.contains_key(&dup_key) {
            let args_str = if trait_type_arg_names.is_empty() {
                String::new()
            } else {
                format!(" {}", trait_type_arg_names.join(" "))
            };
            return Err(Diagnostic::error_at(
                span,
                format!(
                    "duplicate impl: {}{} is already implemented for {} (previously defined elsewhere)",
                    trait_name, args_str, target_type
                ),
            ));
        }

        // Convert each TypeExpr trait_type_arg into a Type, reusing the
        // impl target's pattern variables so extras like `(a, b)` share vars
        // with nested target positions like `Column _ _ a`.
        let trait_type_args_types: Vec<Type> = trait_type_args
            .iter()
            .map(|te| self.convert_type_expr(te, &mut impl_type_vars))
            .collect();
        let target_type_param_ids: Vec<u32> = impl_type_vars.iter().map(|(_, id)| *id).collect();
        let impl_var_id = |vars: &[(String, u32)], name: &str| {
            vars.iter().find(|(n, _)| n == name).map(|(_, id)| *id)
        };

        // Register where clause bounds on impl pattern vars so method bodies
        // can use trait methods on those vars.
        for bound in where_clause {
            if let Some(var_id) = impl_var_id(&impl_type_vars, &bound.type_var) {
                self.trait_state
                    .where_bound_var_names
                    .insert(var_id, bound.type_var.clone());
                for tr in &bound.traits {
                    let resolved_req = self.resolved_trait_name_at(tr.id, &tr.name);
                    self.lsp
                        .type_references
                        .push((tr.span, resolved_req.clone()));
                    self.trait_state
                        .where_bounds
                        .entry(var_id)
                        .or_default()
                        .insert(resolved_req.clone());
                    if !tr.type_args.is_empty() {
                        let extra_types: Vec<Type> = tr
                            .type_args
                            .iter()
                            .map(|te| self.convert_type_expr(te, &mut impl_type_vars))
                            .collect();
                        self.trait_state
                            .where_bound_trait_args
                            .insert((var_id, resolved_req), extra_types);
                    }
                }
            }
        }

        // Validate new-form `where {Trait arg1 arg2 ...}` constraints.
        // Every trait argument must already be bound (to a concrete type or an
        // impl type parameter); a fresh, undetermined argument is an error.
        let local_subst: std::collections::HashMap<String, String> =
            std::collections::HashMap::new();
        let mut where_app_param_constraints: Vec<(String, u32, Vec<Type>)> = Vec::new();
        for app in where_apps {
            let resolved_trait = self
                .resolve_trait_name(&app.trait_name)
                .unwrap_or_else(|| app.trait_name.clone());
            let resolved_trait_info = self
                .trait_state
                .traits
                .get(&resolved_trait)
                .cloned()
                .ok_or_else(|| {
                    Diagnostic::error_at(app.span, format!("unknown trait '{}'", app.trait_name))
                })?;
            self.lsp
                .type_references
                .push((app.span, resolved_trait.clone()));
            // Arity check.
            if app.type_args.len() != resolved_trait_info.type_params.len() {
                return Err(Diagnostic::error_at(
                    app.span,
                    format!(
                        "trait {} expects {} type argument(s), but {} were provided",
                        resolved_trait,
                        resolved_trait_info.type_params.len(),
                        app.type_args.len()
                    ),
                ));
            }
            // Classify each arg as concrete (resolved name) or fresh (unbound).
            // For App heads (e.g. `(Opt a)`), use the constructor's head name
            // as the concrete identifier — type-param positions in the App's
            // args are not relevant to coherence lookup, which is keyed on
            // the head only.
            let mut resolved_names: Vec<Option<String>> = Vec::with_capacity(app.type_args.len());
            let mut fresh_positions: Vec<(usize, String)> = Vec::new();
            let mut impl_param_positions: Vec<(usize, String)> = Vec::new();
            for (i, te) in app.type_args.iter().enumerate() {
                match te {
                    ast::TypeExpr::Named { id, name, .. } => {
                        resolved_names.push(Some(self.resolved_type_name(*id, name)));
                    }
                    ast::TypeExpr::App { .. } => {
                        let head = te.head_name().unwrap_or("");
                        resolved_names.push(Some(
                            self.resolved_type_name(te.head_id().unwrap_or(te.id()), head),
                        ));
                    }
                    ast::TypeExpr::Var { name, .. } => {
                        if let Some(resolved) = local_subst.get(name) {
                            resolved_names.push(Some(resolved.clone()));
                        } else if impl_var_id(&impl_type_vars, name).is_some() {
                            resolved_names.push(Some(format!("$impl_param:{name}")));
                            impl_param_positions.push((i, name.clone()));
                        } else {
                            resolved_names.push(None);
                            fresh_positions.push((i, name.clone()));
                        }
                    }
                    other => {
                        return Err(Diagnostic::error_at(
                            other.span(),
                            "only named types, type variables, and type applications are \
                             supported in trait-app where-clauses"
                                .to_string(),
                        ));
                    }
                }
            }

            if !impl_param_positions.is_empty() {
                if !fresh_positions.is_empty() {
                    return Err(Diagnostic::error_at(
                        app.span,
                        "where-clause TraitApp constraints cannot mix impl type parameters with \
                         fresh existential variables"
                            .to_string(),
                    ));
                }
                let ast::TypeExpr::Var {
                    name: self_param_name,
                    ..
                } = &app.type_args[0]
                else {
                    return Err(Diagnostic::error_at(
                        app.span,
                        "TraitApp constraints on impl type parameters must constrain the first \
                         trait argument"
                            .to_string(),
                    ));
                };
                let Some(self_var_id) = impl_var_id(&impl_type_vars, self_param_name) else {
                    return Err(Diagnostic::error_at(
                        app.span,
                        "TraitApp constraints on impl type parameters must constrain the first \
                         trait argument"
                            .to_string(),
                    ));
                };
                let extra_types: Vec<Type> = app.type_args[1..]
                    .iter()
                    .map(|te| self.convert_type_expr(te, &mut impl_type_vars))
                    .collect();
                self.trait_state
                    .where_bound_var_names
                    .insert(self_var_id, self_param_name.clone());
                self.trait_state
                    .where_bounds
                    .entry(self_var_id)
                    .or_default()
                    .insert(resolved_trait.clone());
                if !extra_types.is_empty() {
                    self.trait_state
                        .where_bound_trait_args
                        .insert((self_var_id, resolved_trait.clone()), extra_types.clone());
                }
                where_app_param_constraints.push((
                    resolved_trait.clone(),
                    self_var_id,
                    extra_types,
                ));
                continue;
            }

            if fresh_positions.is_empty() {
                // All args bound — do a direct impl lookup.
                let self_name = resolved_names[0].clone().unwrap();
                let extras: Vec<String> = resolved_names[1..]
                    .iter()
                    .map(|o| o.clone().unwrap())
                    .collect();
                let key = (resolved_trait.clone(), extras, self_name.clone());
                if !self.trait_state.impls.contains_key(&key) {
                    return Err(Diagnostic::error_at(
                        app.span,
                        format!("no impl of {} for {}", resolved_trait, self_name),
                    ));
                }
            } else {
                // Some trait args are fresh type variables not bound to an impl
                // parameter. Without functional dependencies there is no rule to
                // determine them from the others, so this is unresolvable.
                return Err(Diagnostic::error_at(
                    app.span,
                    format!(
                        "fresh type variable not determined by constraint: trait {}'s extra \
                         parameters cannot be determined from the others",
                        resolved_trait
                    ),
                ));
            }
        }

        let declared_effects: std::collections::HashSet<String> = needs
            .iter()
            .map(|e| self.resolved_effect_name(e.id, &e.name))
            .collect();

        // Expose the impl's own type-param names (with their fresh var IDs) to
        // any nested `convert_type_expr` call inside the method bodies, so an
        // inline ascription like `(x : b)` resolves `b` to the impl's `b`
        // rather than a fresh, unconstrained var. This keeps method bodies of a
        // multi-param impl such as `impl ConvertTo a b for Box a` referring to
        // the same `b` the impl header introduced.
        let saved_outer = std::mem::take(&mut self.outer_named_type_vars);
        for (tp, var_id) in type_params.iter().zip(target_type_param_ids.iter()) {
            self.outer_named_type_vars.insert(tp.name.clone(), *var_id);
        }

        // Per-method effect rows this impl performs, collected from each method
        // body's inferred effects below and stored on the `ImplInfo` so concrete
        // trait-method call sites can propagate the selected impl's effects.
        let mut impl_method_effects: std::collections::HashMap<String, Vec<String>> =
            std::collections::HashMap::new();

        for m in methods {
            let (method_name, params, body) = (&m.name, &m.params, &m.body);
            let trait_method = trait_info
                .methods
                .iter()
                .find(|tm| &tm.name == method_name)
                .unwrap(); // already validated above

            let trait_param_id = trait_method.trait_param_id;
            // Freshen the trait method's non-self forall vars so that
            // unification in one impl's body doesn't leak into the next.
            // E.g. for `trait ConvertTo a b`, the `b` var is shared across
            // impls in the trait's stored signature; without freshening,
            // the first impl pins `b` globally and subsequent impls with
            // a different `b` fail to unify.
            let mut fresh_mapping: std::collections::HashMap<u32, Type> =
                std::collections::HashMap::new();
            for id in &trait_method.scheme.forall {
                if Some(*id) == trait_param_id {
                    continue;
                }
                fresh_mapping.insert(*id, self.fresh_var());
            }
            let freshened_params: Vec<Type> = trait_method
                .param_types
                .iter()
                .map(|t| Self::replace_vars(t, &fresh_mapping))
                .collect();
            let freshened_return = Self::replace_vars(&trait_method.return_type, &fresh_mapping);
            let mut impl_trait_param_mapping: std::collections::HashMap<u32, Type> =
                std::collections::HashMap::new();
            if let Some(self_id) = trait_param_id {
                impl_trait_param_mapping.insert(self_id, target.clone());
            }
            if let Some((_, _, extra_types)) = trait_method
                .scheme
                .constraints
                .iter()
                .find(|(constraint_trait, _, _)| constraint_trait == trait_name)
            {
                for (extra_ty, impl_arg_ty) in extra_types.iter().zip(trait_type_args_types.iter())
                {
                    let fresh_extra = Self::replace_vars(extra_ty, &fresh_mapping);
                    if let Type::Var(id) = fresh_extra {
                        impl_trait_param_mapping.insert(id, impl_arg_ty.clone());
                    }
                }
            }
            let expected_params: Vec<Type> = freshened_params
                .iter()
                .map(|t| Self::replace_vars(t, &impl_trait_param_mapping))
                .collect();
            let expected_return = Self::replace_vars(&freshened_return, &impl_trait_param_mapping);

            let saved_env = self.env.clone();
            let body_scope = self.enter_scope();
            let trait_saved_effs = self.save_effects();

            // Re-insert the trait's method schemes under bare name so that
            // method calls inside the impl body resolve to the trait
            // signature, not to a user-defined function that happens to
            // share the name. The saved_env restore at the end of this loop
            // iteration brings back the user's entry. Schemes are sourced
            // from `TraitMethodInfo.scheme`, the single authority.
            for tm in &trait_info.methods {
                self.env.insert(tm.name.clone(), tm.scheme.clone());
            }

            // Bind every param. The first `expected_params.len()` line up with
            // the trait method's declared parameters; any extras are only valid
            // when the return type is itself a function, so peel an arrow off it
            // per surplus param. Binding *all* params keeps them in scope — a
            // surplus param on a non-function return otherwise leaks from the
            // body as a bogus "undefined variable" instead of a clear arity
            // error.
            let mut remaining_return = expected_return.clone();
            for (i, pat) in params.iter().enumerate() {
                let param_ty = if i < expected_params.len() {
                    expected_params[i].clone()
                } else {
                    match self.sub.apply(&remaining_return) {
                        Type::Fun(arg, ret, _) => {
                            remaining_return = *ret;
                            *arg
                        }
                        _ => {
                            return Err(Diagnostic::error_at(
                                span,
                                format!(
                                    "in impl {} for {}, method '{}' binds {} parameter(s) but the \
                                     trait method's type does not accept that many",
                                    trait_name,
                                    target_type,
                                    method_name,
                                    params.len(),
                                ),
                            ));
                        }
                    }
                };
                self.bind_pattern(pat, &param_ty)?;
            }

            // Infer body and check it matches the (possibly arrow-peeled) return.
            let body_ty = self.infer_expr(body)?;
            self.unify_at(&body_ty, &remaining_return, body.span)
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
            let body_effects: std::collections::HashSet<String> =
                body_effs.effects.iter().map(|e| e.name.clone()).collect();
            // Record this method's own effects (per-method precision: a pure
            // sibling of an effectful impl contributes nothing).
            {
                let mut effs: Vec<String> = body_effects.iter().cloned().collect();
                effs.sort();
                impl_method_effects.insert(method_name.clone(), effs);
            }

            // Effect-capability bounding (opt-in via the trait method's row): an
            // impl may only use effects the trait method permits. A pure trait
            // method permits nothing; a closed named row permits exactly its
            // effects; an open row (`..e`) permits anything. This makes
            // effect-capability declared at the trait — keeping generic callers'
            // obligations modular — rather than smuggled in via the impl. See
            // docs/planning/effect-polymorphic-traits.md ("Effect-capability is
            // opt-in").
            if !trait_method.effect_sig.is_open_row {
                let permitted: std::collections::HashSet<&String> =
                    trait_method.effect_sig.effects.iter().collect();
                let mut exceeded: Vec<String> = body_effects
                    .iter()
                    .filter(|e| !permitted.contains(e))
                    .cloned()
                    .collect();
                if !exceeded.is_empty() {
                    exceeded.sort();
                    let pretty: Vec<String> = exceeded
                        .iter()
                        .map(|e| e.rsplit('.').next().unwrap_or(e).to_string())
                        .collect();
                    return Err(Diagnostic::error_at(
                        body.span,
                        format!(
                            "impl {} for {}, method '{}' uses effect{} {{{}}} that trait method \
                             '{}' does not permit. Declare the effect on the trait method \
                             (e.g. `needs {{..e}}` to allow any impl effects, or `needs {{{}}}` \
                             to allow exactly these).",
                            trait_name,
                            target_type,
                            method_name,
                            if pretty.len() == 1 { "" } else { "s" },
                            pretty.join(", "),
                            method_name,
                            pretty.join(", "),
                        ),
                    ));
                }
            }
            if !body_effects.is_empty() || !declared_effects.is_empty() {
                let undeclared: Vec<String> = body_effects
                    .difference(&declared_effects)
                    .cloned()
                    .collect();
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
                            format!(
                                "{} uses effects {{{}}} but has no 'needs' declaration",
                                label,
                                sorted.join(", ")
                            ),
                        ));
                    } else {
                        return Err(Diagnostic::error_at(
                            body.span,
                            format!(
                                "{} uses effects {{{}}} not declared in its 'needs' clause",
                                label,
                                sorted.join(", ")
                            ),
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

        self.outer_named_type_vars = saved_outer;

        // Build param_constraints from where clause. Keep the old
        // index-based shape when a constrained var is a direct target arg,
        // and also store the variable-id form for structured targets.
        let mut param_constraints = Vec::new();
        let mut param_constraints_by_var = Vec::new();
        let mut param_constraints_by_var_with_args = where_app_param_constraints;
        for bound in where_clause {
            let var_id = impl_var_id(&impl_type_vars, &bound.type_var);
            match var_id {
                Some(var_id) => {
                    for tr in &bound.traits {
                        let resolved_req = self.resolved_trait_name_at(tr.id, &tr.name);
                        if tr.type_args.is_empty() {
                            param_constraints_by_var.push((resolved_req.clone(), var_id));
                            if let Some(idx) = direct_target_var_index(&target, var_id) {
                                param_constraints.push((resolved_req, idx));
                            }
                        } else {
                            let extra_types: Vec<Type> = tr
                                .type_args
                                .iter()
                                .map(|te| self.convert_type_expr(te, &mut impl_type_vars))
                                .collect();
                            param_constraints_by_var_with_args.push((
                                resolved_req.clone(),
                                var_id,
                                extra_types,
                            ));
                        }
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

        self.trait_state.impls.insert(
            dup_key,
            ImplInfo {
                param_constraints,
                param_constraints_by_var,
                param_constraints_by_var_with_args,
                target_pattern: Some(target.clone()),
                trait_type_args: trait_type_args_types,
                target_type_param_ids,
                span: Some(span),
                method_effects: impl_method_effects,
            },
        );
        Ok(())
    }
}
