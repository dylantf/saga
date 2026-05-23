use crate::ast::{self, TypeParam};
use crate::token::Span;

use super::unify::kind_name;
use super::{Checker, Diagnostic, ImplInfo, Scheme, Type};

/// Traits whose first (self) parameter functionally determines the remaining
/// trait parameters. Multiple impls sharing the same target type but with
/// differing trait_type_args are rejected as coherence violations.
///
/// Entries are exact canonical names — both the bare form (used by
/// module-less test sources, where the canonical name is just `Generic`)
/// and the fully-qualified stdlib form. The flag is resolved once at trait
/// registration into `TraitInfo.is_functional`, so use sites read the
/// stored flag instead of re-matching against this list.
///
/// Phase 2 may replace this with an explicit per-trait attribute.
pub(crate) const FUNCTIONAL_TRAITS: &[&str] = &["Generic", "Std.Generic.Generic"];

impl Checker {
    // --- Trait & impl helpers ---

    pub(crate) fn validate_trait_bound_kind(
        &self,
        trait_name: &str,
        type_var_name: &str,
        var_id: u32,
        span: Span,
    ) -> Result<(), Diagnostic> {
        let Some(trait_info) = self.trait_state.traits.get(trait_name) else {
            return Ok(());
        };
        let Some((_, expected_kind)) = trait_info.type_params.first() else {
            return Ok(());
        };
        let actual_kind = self.var_kind(var_id);
        if actual_kind == *expected_kind {
            return Ok(());
        }
        Err(Diagnostic::error_at(
            span,
            format!(
                "kind mismatch: type variable `{}` has kind {} but trait {} expects kind {}",
                type_var_name,
                kind_name(actual_kind),
                trait_name.rsplit('.').next().unwrap_or(trait_name),
                kind_name(*expected_kind),
            ),
        ))
    }

    /// Replace occurrences of the trait's type param variable with a concrete type.
    /// Used when checking impl bodies: if the trait says `(x: a) -> String`
    /// and the impl is `for User`, we substitute a -> User to get `(x: User) -> String`.
    /// `trait_param_id` identifies which specific var to replace; other free vars are left alone.
    pub(crate) fn substitute_trait_param(
        &self,
        trait_param_id: Option<u32>,
        replacement: &Type,
        ty: &Type,
    ) -> Type {
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
                    effects: row
                        .effects
                        .iter()
                        .map(|entry| super::EffectEntry {
                            name: entry.name.clone(),
                            args: entry
                                .args
                                .iter()
                                .map(|t| {
                                    self.substitute_trait_param(trait_param_id, replacement, t)
                                })
                                .collect(),
                        })
                        .collect(),
                    tail: row.tail.as_ref().map(|t| {
                        Box::new(self.substitute_trait_param(trait_param_id, replacement, t))
                    }),
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
                    .map(|(fname, ty)| {
                        (
                            fname.clone(),
                            self.substitute_trait_param(trait_param_id, replacement, ty),
                        )
                    })
                    .collect(),
            ),
            Type::Symbol(name) => Type::Symbol(name.clone()),
            Type::Error => Type::Error,
        }
    }

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
                    let var = self.fresh_var_of_kind(tp.kind);
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

            method_sigs.push((
                method.name.clone(),
                param_types,
                return_type,
                trait_param_id,
                params_list,
            ));
        }

        // Add each method to the env as a polymorphic function with trait constraint.
        // e.g. `fun show (x: a) -> String` becomes `show : forall a. Describe a => a -> String`
        // For phantom type params (not mentioned in the method signature), we create
        // fresh vars and add them to forall so the constraint flows through instantiation.
        let mut trait_method_sigs = Vec::new();
        for (method_name, param_types, return_type, trait_param_id, mut params_list) in method_sigs
        {
            let mut fun_ty = return_type.clone();
            for pt in param_types.iter().rev() {
                fun_ty = Type::arrow(pt.clone(), fun_ty);
            }
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
                        let fresh = self.fresh_var_of_kind(tp.kind);
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
        let is_functional = FUNCTIONAL_TRAITS.contains(&canonical_name.as_str());
        self.trait_state.traits.insert(
            canonical_name,
            super::TraitInfo {
                type_params: type_params
                    .iter()
                    .map(|tp| (tp.name.clone(), tp.kind))
                    .collect(),
                supertraits: resolved_supertraits,
                methods: trait_method_sigs,
                is_functional,
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
                self.resolved_type_name(te.id(), head)
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
        // unify the trait's phantom type vars like `r` in `Generic a r` with
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
        let dup_key = (
            trait_name.to_string(),
            trait_type_args_names.clone(),
            resolved_target_type.clone(),
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
        if trait_info.is_functional {
            for ((existing_trait, existing_args, existing_target), existing_info) in
                &self.trait_state.impls
            {
                if existing_trait == trait_name
                    && existing_target == &resolved_target_type
                    && existing_args != trait_type_args_names
                {
                    let prev_loc = match existing_info.span {
                        Some(s) => format!(" (previous impl at byte {})", s.start),
                        None => String::new(),
                    };
                    return Err(Diagnostic::error_at(
                        span,
                        format!(
                            "coherence violation: trait {} requires that the first parameter \
                             functionally determines the rest, but `{}` already has an impl with \
                             different trait arguments ({:?} vs {:?}){}",
                            trait_name, target_type, existing_args, trait_type_arg_names, prev_loc
                        ),
                    ));
                }
            }
        }

        // Type-check each method body against the trait's expected signature.
        // Substitute the trait's type param with the concrete target type.
        // For parameterized impls (e.g. `impl Show for Box a`), use fresh vars for type params.
        let mut target_type_param_ids: Vec<u32> = Vec::new();
        let target = if type_params.is_empty() {
            Type::Con(resolved_target_type.clone(), vec![])
        } else {
            let param_vars: Vec<Type> = type_params
                .iter()
                .map(|tp| self.fresh_var_of_kind(tp.kind))
                .collect();
            target_type_param_ids = param_vars
                .iter()
                .map(|t| match t {
                    Type::Var(id) => *id,
                    _ => unreachable!(),
                })
                .collect();
            // Register where clause bounds on the fresh type vars so method bodies
            // can use trait methods on those vars (e.g. `show x` where `x: a` and `a: Show`).
            for bound in where_clause {
                if let Some(idx) = type_params.iter().position(|p| p == &bound.type_var)
                    && let Some(Type::Var(var_id)) = param_vars.get(idx)
                {
                    self.trait_state
                        .where_bound_var_names
                        .insert(*var_id, bound.type_var.clone());
                    for tr in &bound.traits {
                        let resolved_req = self.resolved_trait_name_at(tr.id, &tr.name);
                        self.validate_trait_bound_kind(
                            &resolved_req,
                            &bound.type_var,
                            *var_id,
                            tr.span,
                        )?;
                        self.lsp
                            .type_references
                            .push((tr.span, resolved_req.clone()));
                        self.trait_state
                            .where_bounds
                            .entry(*var_id)
                            .or_default()
                            .insert(resolved_req);
                    }
                }
            }
            Type::Con(resolved_target_type.clone(), param_vars)
        };

        // Validate new-form `where {Trait arg1 arg2 ...}` constraints.
        // Process source-order; later constraints can reference fresh vars
        // resolved by earlier ones. For functional traits, the bound first
        // param determines the remaining params via the [Phase 1b] coherence
        // rule; for non-functional traits, all args must be already bound.
        let mut local_subst: std::collections::HashMap<String, String> =
            std::collections::HashMap::new();
        let mut where_app_param_constraints: Vec<(String, usize)> = Vec::new();
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
                        resolved_names.push(Some(self.resolved_type_name(te.id(), head)));
                    }
                    ast::TypeExpr::Var { name, .. } => {
                        if let Some(resolved) = local_subst.get(name) {
                            resolved_names.push(Some(resolved.clone()));
                        } else if type_params.iter().any(|tp| &tp.name == name) {
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
                if app.type_args.len() != 1 {
                    return Err(Diagnostic::error_at(
                        app.span,
                        "TraitApp constraints on impl type parameters currently support \
                         single-parameter traits only"
                            .to_string(),
                    ));
                }
                let (_, param_name) = &impl_param_positions[0];
                let Some(param_idx) = type_params.iter().position(|p| p == param_name) else {
                    continue;
                };
                if let Some(var_id) = target_type_param_ids.get(param_idx) {
                    self.trait_state
                        .where_bound_var_names
                        .insert(*var_id, param_name.clone());
                    self.trait_state
                        .where_bounds
                        .entry(*var_id)
                        .or_default()
                        .insert(resolved_trait.clone());
                }
                where_app_param_constraints.push((resolved_trait.clone(), param_idx));
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
                // Some args fresh. Must be a functional trait.
                if !resolved_trait_info.is_functional {
                    return Err(Diagnostic::error_at(
                        app.span,
                        format!(
                            "fresh type variable not determined by constraint: trait {} is not \
                             a functional trait (only functional traits can determine extra \
                             parameters from the first)",
                            resolved_trait
                        ),
                    ));
                }
                // The self position (index 0) must be concrete for the
                // functional rule to fire.
                let self_name = match &resolved_names[0] {
                    Some(s) => s.clone(),
                    None => {
                        return Err(Diagnostic::error_at(
                            app.span,
                            format!(
                                "trait {}'s self parameter must be known to resolve fresh \
                                 type variables",
                                resolved_trait
                            ),
                        ));
                    }
                };
                // Find a matching impl for (trait, _, self_name).
                let matched = self
                    .trait_state
                    .impls
                    .iter()
                    .find(|((t, _, tgt), _)| t == &resolved_trait && tgt == &self_name);
                let ((_, extras, _), _) = matched.ok_or_else(|| {
                    Diagnostic::error_at(
                        app.span,
                        format!("no impl of {} for {}", resolved_trait, self_name),
                    )
                })?;
                // Bind each fresh var to its corresponding resolved extra.
                for (i, fresh_name) in fresh_positions {
                    if i == 0 {
                        // self position can't be fresh here (we errored above)
                        continue;
                    }
                    let value = extras.get(i - 1).cloned().ok_or_else(|| {
                        Diagnostic::error_at(
                            app.span,
                            format!(
                                "internal: matched impl for {} on {} has unexpected arity",
                                resolved_trait, self_name
                            ),
                        )
                    })?;
                    local_subst.insert(fresh_name, value);
                }
            }
        }

        let declared_effects: std::collections::HashSet<String> = needs
            .iter()
            .map(|e| self.resolved_effect_name(e.id, &e.name))
            .collect();

        // Expose the impl's own type-param names (with their fresh var IDs) to
        // any nested `convert_type_expr` call inside the method bodies, so an
        // inline ascription like `(Proxy : Proxy n)` resolves `n` to the
        // impl's `n` rather than a fresh, unconstrained var. This is what
        // lets `impl ToJson for Labeled n a where {n : KnownSymbol}` reflect
        // the symbol at runtime.
        let saved_outer = std::mem::take(&mut self.outer_named_type_vars);
        for (tp, var_id) in type_params.iter().zip(target_type_param_ids.iter()) {
            self.outer_named_type_vars.insert(tp.name.clone(), *var_id);
        }

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
            // E.g. for `trait Generic a r`, the `r` var is shared across
            // impls in the trait's stored signature; without freshening,
            // the first impl pins `r` globally and subsequent impls with
            // a different `r` fail to unify.
            let mut fresh_mapping: std::collections::HashMap<u32, Type> =
                std::collections::HashMap::new();
            for id in &trait_method.scheme.forall {
                if Some(*id) == trait_param_id {
                    continue;
                }
                let kind = self.var_kind(*id);
                fresh_mapping.insert(*id, self.fresh_var_of_kind(kind));
            }
            let freshened_params: Vec<Type> = trait_method
                .param_types
                .iter()
                .map(|t| Self::replace_vars(t, &fresh_mapping))
                .collect();
            let freshened_return = Self::replace_vars(&trait_method.return_type, &fresh_mapping);
            let expected_params: Vec<Type> = freshened_params
                .iter()
                .map(|t| self.substitute_trait_param(trait_param_id, &target, t))
                .collect();
            let expected_return =
                self.substitute_trait_param(trait_param_id, &target, &freshened_return);

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
            let body_effects: std::collections::HashSet<String> =
                body_effs.effects.iter().map(|e| e.name.clone()).collect();
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

        // Build param_constraints from where clause
        let mut param_constraints = Vec::new();
        for bound in where_clause {
            let param_idx = type_params.iter().position(|p| p == &bound.type_var);
            match param_idx {
                Some(idx) => {
                    for tr in &bound.traits {
                        let resolved_req = self.resolved_trait_name_at(tr.id, &tr.name);
                        if let Some(var_id) = target_type_param_ids.get(idx) {
                            self.validate_trait_bound_kind(
                                &resolved_req,
                                &bound.type_var,
                                *var_id,
                                tr.span,
                            )?;
                        }
                        param_constraints.push((resolved_req, idx));
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
        param_constraints.extend(where_app_param_constraints);

        // Convert each TypeExpr trait_type_arg into a Type, reusing the
        // impl's type-param fresh-var ids so that the stored extras share
        // tvars with `target_type_param_ids`. Call sites substitute those
        // tvars from the concrete args of the target type.
        let mut conv_params: Vec<(String, u32)> = type_params
            .iter()
            .map(|tp| tp.name.clone())
            .zip(target_type_param_ids.iter().copied())
            .collect();
        let trait_type_args_types: Vec<Type> = trait_type_args
            .iter()
            .map(|te| self.convert_type_expr(te, &mut conv_params))
            .collect();

        self.trait_state.impls.insert(
            dup_key,
            ImplInfo {
                param_constraints,
                trait_type_args: trait_type_args_types,
                target_type_param_ids,
                span: Some(span),
            },
        );
        Ok(())
    }
}
