use super::*;

impl Checker {

    pub(crate) fn check_pending_constraints(&mut self) -> Result<(), Diagnostic> {
        // Build resolved where bounds (substitution may have chained var IDs)
        let mut resolved_bounds: std::collections::HashMap<u32, std::collections::HashSet<String>> =
            std::collections::HashMap::new();
        // Also resolve var names through substitution
        let mut resolved_var_names: std::collections::HashMap<u32, String> =
            std::collections::HashMap::new();
        let mut resolved_bound_trait_args: std::collections::HashMap<(u32, String), Vec<Type>> =
            std::collections::HashMap::new();
        for (&var_id, traits) in &self.trait_state.where_bounds {
            if let Type::Var(resolved_id) = self.sub.apply(&Type::Var(var_id)) {
                resolved_bounds
                    .entry(resolved_id)
                    .or_default()
                    .extend(traits.iter().cloned());
                if let Some(name) = self.trait_state.where_bound_var_names.get(&var_id) {
                    resolved_var_names.insert(resolved_id, name.clone());
                }
                for trait_name in traits {
                    if let Some(extras) = self
                        .trait_state
                        .where_bound_trait_args
                        .get(&(var_id, trait_name.clone()))
                    {
                        resolved_bound_trait_args.insert(
                            (resolved_id, trait_name.clone()),
                            extras.iter().map(|ty| self.sub.apply(ty)).collect(),
                        );
                    }
                }
            }
        }

        // Process constraints in a loop since conditional impls may push new ones.
        // Within each batch, sort so that constraints whose self-type already
        // resolves to a concrete Type::Con are processed first. Constraints
        // whose self is still a Var depend on prior constraints to pin them
        // (e.g. `Show r` waits on a sibling `ConvertTo T r` to unify `r`), and
        // erroring on them before the pinning constraint runs produces spurious
        // "ambiguous" diagnostics.
        loop {
            let mut constraints = std::mem::take(&mut self.trait_state.pending_constraints);
            if constraints.is_empty() {
                break;
            }
            constraints.sort_by_key(|(_, _, ty, _, _)| matches!(self.sub.apply(ty), Type::Var(_)));
            // Worklist bookkeeping: a Var-self constraint that isn't resolvable
            // this pass (e.g. `Show q` before a sibling `ConvertTo c q` has
            // unified `q`) is *deferred* rather than reported, because a sibling
            // constraint processed later — or a later pass — may still pin it.
            // The sort puts concrete-self constraints first, but it cannot
            // topologically order the Var-self group by their mutual
            // dependencies, so deferral + progress retry is what makes solving
            // order-independent.
            let sub_before = self.sub.solved_count();
            #[allow(clippy::type_complexity)]
            let mut deferred: Vec<(
                (String, Vec<Type>, Type, Span, crate::ast::NodeId),
                Diagnostic,
            )> = Vec::new();
            for (trait_name, trait_type_arg_types, ty, span, node_id) in constraints {
                let resolved = self.sub.apply(&ty);
                if matches!(resolved, Type::Error) {
                    continue;
                }
                // If this constraint originated inside a synthesized routed-
                // derive impl, the eventual failure should be rewritten to
                // point at the user's deriving clause and name the user-facing
                // trait + target type instead of building-block types from the
                // synthesized body.
                let routed_origin = self
                    .trait_state
                    .routed_constraint_origins
                    .get(&node_id)
                    .cloned();
                let rewrite_diag = |default_msg: String, default_span: Span| -> Diagnostic {
                    match &routed_origin {
                        Some(info) => Diagnostic::error_at(
                            info.deriving_span,
                            format!(
                                "cannot derive `{}` for `{}`: missing required instance ({}). \
                                 Make sure all field types implement `{}`, or also derive \
                                 `{}` on them.",
                                info.trait_name,
                                info.target_type,
                                default_msg,
                                info.trait_name,
                                info.trait_name,
                            ),
                        ),
                        None => Diagnostic::error_at(default_span, default_msg),
                    }
                };
                // Resolve trait type args to concrete type names for impl lookup
                let resolved_trait_type_args: Vec<String> = trait_type_arg_types
                    .iter()
                    .filter_map(|t| {
                        let resolved_t = self.sub.apply(t);
                        match &resolved_t {
                            Type::Con(name, _) => Some(name.clone()),
                            _ => None,
                        }
                    })
                    .collect();
                match &resolved {
                    // Concrete type (includes primitives): check that an impl exists.
                    // Trait names must already be canonicalized by the resolver/checker
                    // boundary; do not fall back to bare final segments here.
                    Type::Con(type_name, args) => {
                        let resolved_trait = self
                            .resolve_trait_name(&trait_name)
                            .unwrap_or_else(|| trait_name.clone());
                        // For tuple types, look up the arity-specific impl
                        // first (user-written `impl T for (a, b)`), then fall
                        // back to the arity-agnostic bare key used by the
                        // built-in Show/Debug/Eq tuple impls.
                        let arity_keyed_name =
                            crate::typechecker::arity_keyed_target_name(type_name, args.len());
                        let mut impl_info = self
                            .trait_state
                            .impls
                            .get(&(
                                resolved_trait.clone(),
                                resolved_trait_type_args.clone(),
                                arity_keyed_name.clone(),
                            ))
                            .cloned();
                        if impl_info.is_none() && arity_keyed_name != *type_name {
                            impl_info = self
                                .trait_state
                                .impls
                                .get(&(
                                    resolved_trait.clone(),
                                    resolved_trait_type_args.clone(),
                                    type_name.clone(),
                                ))
                                .cloned();
                        }
                        if impl_info.is_none()
                            && resolved_trait_type_args.len() != trait_type_arg_types.len()
                        {
                            let matches: Vec<crate::typechecker::ImplInfo> = self
                                .trait_state
                                .impls
                                .iter()
                                .filter(|((tn, _, tt), _)| {
                                    tn == &resolved_trait && tt == &arity_keyed_name
                                })
                                .map(|(_, info)| info.clone())
                                .collect();
                            if matches.len() == 1 {
                                impl_info = Some(matches[0].clone());
                            }
                        }

                        if impl_info.is_none() {
                            let matches: Vec<crate::typechecker::ImplInfo> = self
                                .trait_state
                                .impls
                                .iter()
                                .filter(|((tn, _, tt), info)| {
                                    if tn != &resolved_trait || tt != &arity_keyed_name {
                                        return false;
                                    }
                                    let mut pattern_subst = std::collections::HashMap::new();
                                    let Some(pattern) = &info.target_pattern else {
                                        return false;
                                    };
                                    if !crate::typechecker::check_traits::match_type_pattern(
                                        pattern,
                                        &resolved,
                                        &mut pattern_subst,
                                    ) {
                                        return false;
                                    }
                                    if trait_type_arg_types.len() != info.trait_type_args.len() {
                                        return false;
                                    }
                                    trait_type_arg_types
                                        .iter()
                                        .zip(info.trait_type_args.iter())
                                        .all(|(actual_extra, pattern_extra)| {
                                            let expected_extra =
                                                crate::typechecker::check_traits::substitute_pattern_vars(
                                                    pattern_extra,
                                                    &pattern_subst,
                                                );
                                            let resolved_actual = self.sub.apply(actual_extra);
                                            crate::typechecker::check_traits::match_type_pattern(
                                                &expected_extra,
                                                &resolved_actual,
                                                &mut pattern_subst,
                                            )
                                        })
                                })
                                .map(|(_, info)| info.clone())
                                .collect();
                            if matches.len() == 1 {
                                impl_info = Some(matches[0].clone());
                            }
                        }

                        let mut pattern_subst = std::collections::HashMap::new();
                        let impl_info = impl_info.and_then(|info| {
                            if let Some(pattern) = &info.target_pattern
                                && !crate::typechecker::check_traits::match_type_pattern(
                                    pattern,
                                    &resolved,
                                    &mut pattern_subst,
                                )
                            {
                                return None;
                            }
                            let mut impl_vars = Vec::new();
                            for extra in &info.trait_type_args {
                                crate::typechecker::collect_free_vars(extra, &mut impl_vars);
                            }
                            for (_, _, extra_types) in &info.param_constraints_by_var_with_args {
                                for extra in extra_types {
                                    crate::typechecker::collect_free_vars(extra, &mut impl_vars);
                                }
                            }
                            for var_id in impl_vars {
                                if let std::collections::hash_map::Entry::Vacant(entry) =
                                    pattern_subst.entry(var_id)
                                {
                                    entry.insert(self.fresh_var());
                                }
                            }
                            for (actual_extra, pattern_extra) in
                                trait_type_arg_types.iter().zip(info.trait_type_args.iter())
                            {
                                let expected_extra =
                                    crate::typechecker::check_traits::substitute_pattern_vars(
                                        pattern_extra,
                                        &pattern_subst,
                                    );
                                let resolved_actual = self.sub.apply(actual_extra);
                                if !crate::typechecker::check_traits::match_type_pattern(
                                    &expected_extra,
                                    &resolved_actual,
                                    &mut pattern_subst,
                                ) && self.unify(actual_extra, &expected_extra).is_err()
                                {
                                    return None;
                                }
                            }
                            Some(info)
                        });
                        match impl_info.as_ref() {
                            None => {
                                // Check if this might be caused by a user function
                                // shadowing a trait method that would have worked.
                                let mut hint = String::new();
                                for (t_name, t_info) in &self.trait_state.traits {
                                    let has_impl = self
                                        .trait_state
                                        .impls
                                        .keys()
                                        .any(|(tn, _, tt)| tn == t_name && tt == type_name);
                                    if has_impl {
                                        for tm in &t_info.methods {
                                            // A user function shadowing a trait method by bare
                                            // name will have its own env entry without this
                                            // trait's constraint. Trait methods themselves no
                                            // longer have bare env entries, so any hit here is
                                            // either a user shadow or unrelated.
                                            if let Some(scheme) = self.env.get(&tm.name) {
                                                let is_trait_scheme = scheme
                                                    .constraints
                                                    .iter()
                                                    .any(|(c, _, _)| c == t_name);
                                                if !is_trait_scheme {
                                                    hint = format!(
                                                        ". `{}` shadows trait method `{}.{}`. \
                                                         rename it to use the trait method",
                                                        tm.name, t_name, tm.name
                                                    );
                                                }
                                            }
                                        }
                                    }
                                }
                                let display_trait =
                                    resolved_trait.rsplit('.').next().unwrap_or(&resolved_trait);
                                return Err(rewrite_diag(
                                    format!(
                                        "no impl of {} for {}{}",
                                        display_trait, type_name, hint
                                    ),
                                    span,
                                ));
                            }
                            Some(info) => {
                                // Resolve extra type args through substitution so the
                                // elaborator sees concrete types for dict key lookup.
                                let resolved_extra_types: Vec<Type> = trait_type_arg_types
                                    .iter()
                                    .map(|t| self.sub.apply(t))
                                    .collect();
                                // Record evidence for the elaboration pass
                                self.evidence.push(crate::typechecker::TraitEvidence {
                                    node_id,
                                    trait_name: trait_name.clone(),
                                    resolved_type: Some((type_name.clone(), args.clone())),
                                    resolved_record_type: None,
                                    type_var_name: None,
                                    trait_type_args: resolved_extra_types,
                                    resolved_symbol: None,
                                });
                                // Push conditional constraints for type parameters
                                if type_name == crate::typechecker::canonicalize_type_name("Tuple")
                                    && info.target_pattern.is_none()
                                {
                                    // Tuples: propagate the trait to all elements
                                    for arg_ty in args {
                                        self.trait_state.pending_constraints.push((
                                            trait_name.clone(),
                                            vec![],
                                            arg_ty.clone(),
                                            span,
                                            node_id,
                                        ));
                                    }
                                } else {
                                    for (req_trait, var_id, extra_types) in
                                        &info.param_constraints_by_var_with_args
                                    {
                                        if let Some(arg_ty) = pattern_subst.get(var_id) {
                                            let resolved_extras = extra_types
                                                .iter()
                                                .map(|extra| {
                                                    crate::typechecker::check_traits::substitute_pattern_vars(
                                                        extra,
                                                        &pattern_subst,
                                                    )
                                                })
                                                .collect();
                                            self.trait_state.pending_constraints.push((
                                                req_trait.clone(),
                                                resolved_extras,
                                                arg_ty.clone(),
                                                span,
                                                node_id,
                                            ));
                                        }
                                    }
                                    for (req_trait, var_id) in &info.param_constraints_by_var {
                                        if let Some(arg_ty) = pattern_subst.get(var_id) {
                                            self.trait_state.pending_constraints.push((
                                                req_trait.clone(),
                                                vec![],
                                                arg_ty.clone(),
                                                span,
                                                node_id,
                                            ));
                                        }
                                    }
                                    if info.param_constraints_by_var_with_args.is_empty()
                                        && info.param_constraints_by_var.is_empty()
                                    {
                                        for (req_trait, param_idx) in &info.param_constraints {
                                            if let Some(arg_ty) = args.get(*param_idx) {
                                                self.trait_state.pending_constraints.push((
                                                    req_trait.clone(),
                                                    vec![],
                                                    arg_ty.clone(),
                                                    span,
                                                    node_id,
                                                ));
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                    // Still a type variable: check where clause bounds
                    Type::Var(id) => {
                        let covering_trait = resolved_bounds.get(id).and_then(|bounds| {
                            bounds
                                .iter()
                                .find(|bound_trait| self.trait_implies(bound_trait, &trait_name))
                                .cloned()
                        });
                        let Some(covering_trait) = covering_trait else {
                            // Not resolvable yet. Defer instead of erroring: a
                            // later constraint (or a later worklist pass) may
                            // still pin this variable. If nothing does, the
                            // post-loop progress check re-raises this prebuilt
                            // diagnostic.
                            let display = trait_name.rsplit('.').next().unwrap_or(&trait_name);
                            let diag = rewrite_diag(
                                format!(
                                    "ambiguous type variable requires {}. Add a type annotation to pin the unconstrained type variable",
                                    display
                                ),
                                span,
                            );
                            deferred.push((
                                (
                                    trait_name,
                                    trait_type_arg_types,
                                    Type::Var(*id),
                                    span,
                                    node_id,
                                ),
                                diag,
                            ));
                            continue;
                        };
                        if let Some(bound_extras) =
                            resolved_bound_trait_args.get(&(*id, covering_trait))
                        {
                            for (required, bound) in
                                trait_type_arg_types.iter().zip(bound_extras.iter())
                            {
                                self.unify_at(required, bound, span)?;
                            }
                        }
                        // Record evidence for polymorphic passthrough
                        let var_name = resolved_var_names.get(id).cloned();
                        self.evidence.push(crate::typechecker::TraitEvidence {
                            node_id,
                            trait_name: trait_name.clone(),
                            resolved_type: None,
                            resolved_record_type: None,
                            type_var_name: var_name,
                            trait_type_args: trait_type_arg_types
                                .iter()
                                .map(|t| self.sub.apply(t))
                                .collect(),
                            resolved_symbol: None,
                        });
                    }
                    Type::Fun(_, _, _) => {
                        let display = trait_name.rsplit('.').next().unwrap_or(&trait_name);
                        return Err(rewrite_diag(
                            format!("no impl of {} for function type", display),
                            span,
                        ));
                    }
                    Type::Record(_) => {
                        let display = trait_name.rsplit('.').next().unwrap_or(&trait_name);
                        return Err(rewrite_diag(
                            format!("no impl of {} for anonymous record type", display),
                            span,
                        ));
                    }
                    // Error/Never type: skip trait checking
                    Type::Error => {}
                }
            }
            // Retry deferred (not-yet-resolvable) constraints only if this pass
            // made progress: the substitution grew, or sibling processing
            // queued fresh constraints. Without progress the deferrals are
            // genuinely ambiguous, so re-raise the first one's diagnostic. This
            // bounds the loop — progress is monotone (the substitution only
            // grows) — while making constraint solving order-independent.
            if !deferred.is_empty() {
                let progressed = self.sub.solved_count() > sub_before
                    || !self.trait_state.pending_constraints.is_empty();
                if progressed {
                    self.trait_state
                        .pending_constraints
                        .extend(deferred.into_iter().map(|(constraint, _)| constraint));
                } else {
                    return Err(deferred.into_iter().next().unwrap().1);
                }
            }
        }
        Ok(())
    }

    // --- Supertrait checking ---

    /// Verify that every impl's trait has its supertraits also implemented for the same type.
    pub(crate) fn check_supertrait_impls(&self) -> Result<(), Diagnostic> {
        for ((trait_name, _trait_type_args, target_type), impl_info) in &self.trait_state.impls {
            if let Some(trait_info) = self.trait_state.traits.get(trait_name) {
                for supertrait in &trait_info.supertraits {
                    // Supertraits are always single-param (no type args).
                    // For arity-keyed tuple targets, the supertrait impl may
                    // be either the same arity-keyed form (user-written) or
                    // the bare canonical tuple key (built-in Show/Debug/Eq);
                    // either satisfies the supertrait obligation.
                    let bare_tuple_fallback: Option<(String, Vec<String>, String)> = {
                        let tuple_canon = crate::typechecker::canonicalize_type_name("Tuple");
                        if let Some(prefix) = target_type.strip_suffix(|c: char| c.is_ascii_digit())
                            && let Some(prefix) = prefix.strip_suffix('.')
                            && prefix == tuple_canon
                        {
                            Some((supertrait.clone(), vec![], prefix.to_string()))
                        } else {
                            None
                        }
                    };
                    let primary_key = (supertrait.clone(), vec![], target_type.clone());
                    if !self.trait_state.impls.contains_key(&primary_key)
                        && !bare_tuple_fallback
                            .as_ref()
                            .map(|k| self.trait_state.impls.contains_key(k))
                            .unwrap_or(false)
                    {
                        let msg = format!(
                            "impl {} for {} requires impl {} for {} (supertrait)",
                            trait_name, target_type, supertrait, target_type
                        );
                        return Err(match impl_info.span {
                            Some(span) => Diagnostic::error_at(span, msg),
                            None => Diagnostic::error(msg),
                        });
                    }
                }
            }
        }
        Ok(())
    }
}
