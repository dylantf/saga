use super::*;

impl Checker {
    /// Eagerly pin functional-dependency *determined* variables for any pending
    /// constraint whose determinants are already concrete, by selecting the
    /// unique matching impl and unifying the determined args. This only refines
    /// the substitution — it neither consumes pending constraints nor reports
    /// errors — so eager consumers (e.g. field-access disambiguation) can see a
    /// determined record type before `check_pending_constraints` runs at the
    /// end of the body. Coherence guarantees the match is unique, so committing
    /// early is sound. Idempotent; loops to a fixpoint for chained fundeps.
    pub(crate) fn improve_pending_fundeps(&mut self) {
        loop {
            let before = self.sub.solved_count();
            let pending = self.trait_state.pending_constraints.clone();
            for (trait_name, extras, self_ty, _, _) in &pending {
                let resolved_trait = self
                    .resolve_trait_name(trait_name)
                    .unwrap_or_else(|| trait_name.clone());
                let Some(fundep) = self
                    .trait_state
                    .traits
                    .get(&resolved_trait)
                    .and_then(|ti| ti.fundep.clone())
                else {
                    continue;
                };
                let resolved_self = self.sub.apply(self_ty);
                let Type::Con(self_head, self_args) = &resolved_self else {
                    continue;
                };
                let arity_keyed = crate::typechecker::arity_keyed_target_name(self_head, self_args.len());
                let det_positions = fundep.determinant_extra_positions();
                let determined_positions = fundep.determined_extra_positions();
                // Every determinant extra must already be concrete, otherwise we
                // can't pick the impl yet.
                let dets_concrete = det_positions.iter().all(|&p| {
                    extras
                        .get(p)
                        .map(|e| matches!(self.sub.apply(e), Type::Con(..) | Type::Symbol(_)))
                        .unwrap_or(false)
                });
                if !dets_concrete {
                    continue;
                }
                // Find the unique impl whose self type and determinant extras
                // match this constraint.
                let candidates: Vec<(crate::typechecker::ImplInfo, std::collections::HashMap<u32, Type>)> = self
                    .trait_state
                    .impls
                    .iter()
                    .filter_map(|((tn, _, tt), info)| {
                        if tn != &resolved_trait || tt != &arity_keyed {
                            return None;
                        }
                        let mut pattern_subst = std::collections::HashMap::new();
                        if let Some(pattern) = &info.target_pattern
                            && !crate::typechecker::check_traits::match_type_pattern(
                                pattern,
                                &resolved_self,
                                &mut pattern_subst,
                            )
                        {
                            return None;
                        }
                        for &p in &det_positions {
                            let (Some(impl_extra), Some(call_extra)) =
                                (info.trait_type_args.get(p), extras.get(p))
                            else {
                                continue;
                            };
                            let expected = crate::typechecker::check_traits::substitute_pattern_vars(
                                impl_extra,
                                &pattern_subst,
                            );
                            let actual = self.sub.apply(call_extra);
                            if !crate::typechecker::check_traits::match_type_pattern(
                                &expected,
                                &actual,
                                &mut pattern_subst,
                            ) {
                                return None;
                            }
                        }
                        Some((info.clone(), pattern_subst))
                    })
                    .collect();
                if candidates.len() != 1 {
                    continue;
                }
                let (info, mut pattern_subst) = candidates.into_iter().next().unwrap();
                // Only pin determined extras that are still unresolved. Re-pinning
                // an already-resolved extra would mint a fresh impl var and bind
                // it every pass, growing `solved_count` without bound — an
                // infinite loop. Skipping resolved ones makes this converge.
                let to_pin: Vec<usize> = determined_positions
                    .iter()
                    .copied()
                    .filter(|&p| {
                        extras
                            .get(p)
                            .map(|e| matches!(self.sub.apply(e), Type::Var(_)))
                            .unwrap_or(false)
                    })
                    .collect();
                if to_pin.is_empty() {
                    continue;
                }
                // Bind any remaining impl pattern variables (not pinned by the
                // determinant match) to fresh vars so the determined args are
                // fully grounded.
                let mut impl_vars = Vec::new();
                for extra in &info.trait_type_args {
                    crate::typechecker::collect_free_vars(extra, &mut impl_vars);
                }
                for var_id in impl_vars {
                    pattern_subst
                        .entry(var_id)
                        .or_insert_with(|| self.fresh_var());
                }
                for p in to_pin {
                    let (Some(call_extra), Some(impl_extra)) =
                        (extras.get(p), info.trait_type_args.get(p))
                    else {
                        continue;
                    };
                    let pinned =
                        crate::typechecker::check_traits::substitute_pattern_vars(impl_extra, &pattern_subst);
                    let _ = self.unify(call_extra, &pinned);
                }
            }
            if self.sub.solved_count() == before {
                break;
            }
        }
    }


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
        // (e.g. `ToJson r` waits on `Generic T r`), and erroring on them
        // before the pinning constraint runs produces spurious "ambiguous"
        // diagnostics.
        loop {
            let mut constraints = std::mem::take(&mut self.trait_state.pending_constraints);
            if constraints.is_empty() {
                break;
            }
            constraints.sort_by_key(|(_, _, ty, _, _)| matches!(self.sub.apply(ty), Type::Var(_)));
            // Worklist bookkeeping: a Var-self constraint that isn't resolvable
            // this pass (e.g. `Show q` before the `Two c q` fundep has pinned
            // `q`) is *deferred* rather than reported, because a sibling
            // constraint processed later — or a later pass — may still pin it.
            // The sort puts concrete-self constraints first, but it cannot
            // topologically order the Var-self group by their mutual fundep
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

                        // Functional-trait coherence fallback: if extras are
                        // unresolved (and direct lookup missed), scan for the
                        // unique impl with the matching self-type and pin the
                        // extras to its stored args. The trait info table
                        // marks Generic-like traits as functional.
                        if impl_info.is_none()
                            && resolved_trait_type_args.len() != trait_type_arg_types.len()
                            && self
                                .trait_state
                                .traits
                                .get(&resolved_trait)
                                .map(|ti| ti.is_functional)
                                .unwrap_or(false)
                        {
                            // Extra-arg positions that *determine* the rest. For
                            // a multi-variable determinant (`a b -> c`), the
                            // self type alone doesn't pick the impl — we must
                            // also match the resolved determinant extras (`b`),
                            // then pin the determined extras (`c`).
                            let det_extra_positions = self
                                .trait_state
                                .traits
                                .get(&resolved_trait)
                                .and_then(|ti| ti.fundep.as_ref())
                                .map(|fd| fd.determinant_extra_positions())
                                .unwrap_or_default();
                            let matches: Vec<(
                                crate::typechecker::ImplInfo,
                                std::collections::HashMap<u32, Type>,
                            )> = self
                                .trait_state
                                .impls
                                .iter()
                                .filter_map(|((tn, _, tt), info)| {
                                    if tn != &resolved_trait || tt != &arity_keyed_name {
                                        return None;
                                    }
                                    let mut pattern_subst = std::collections::HashMap::new();
                                    if let Some(pattern) = &info.target_pattern
                                        && !crate::typechecker::check_traits::match_type_pattern(
                                            pattern,
                                            &resolved,
                                            &mut pattern_subst,
                                        )
                                    {
                                        return None;
                                    }
                                    // Filter by the determinant extras: each must
                                    // be resolved at the call site and match this
                                    // impl's stored arg. An unresolved determinant
                                    // means we can't commit yet, so drop the
                                    // candidate and let the constraint defer.
                                    for &p in &det_extra_positions {
                                        let (Some(impl_extra), Some(call_extra)) = (
                                            info.trait_type_args.get(p),
                                            trait_type_arg_types.get(p),
                                        ) else {
                                            continue;
                                        };
                                        let actual = self.sub.apply(call_extra);
                                        if matches!(actual, Type::Var(_)) {
                                            return None;
                                        }
                                        let expected = crate::typechecker::check_traits::substitute_pattern_vars(
                                            impl_extra,
                                            &pattern_subst,
                                        );
                                        if !crate::typechecker::check_traits::match_type_pattern(
                                            &expected,
                                            &actual,
                                            &mut pattern_subst,
                                        ) {
                                            return None;
                                        }
                                    }
                                    Some((info.clone(), pattern_subst))
                                })
                                .collect();
                            if matches.len() == 1 {
                                let (info, mut pattern_subst) = matches[0].clone();
                                // Substitute the impl's type-param vars with the
                                // call-site target. For structured targets such
                                // as `Leaf (Column n a)`, the determined vars
                                // live inside the target pattern, so prefer the
                                // full pattern substitution. For legacy/builtin
                                // impls without a pattern, fall back to top-level
                                // argument zipping.
                                if pattern_subst.is_empty() {
                                    pattern_subst.extend(
                                        info.target_type_param_ids
                                            .iter()
                                            .zip(args.iter())
                                            .map(|(id, t)| (*id, t.clone())),
                                    );
                                }
                                let mut impl_vars = Vec::new();
                                for extra in &info.trait_type_args {
                                    crate::typechecker::collect_free_vars(extra, &mut impl_vars);
                                }
                                for (_, _, extra_types) in &info.param_constraints_by_var_with_args
                                {
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
                                let pinned: Vec<Type> = info
                                    .trait_type_args
                                    .iter()
                                    .map(|t| {
                                        crate::typechecker::check_traits::substitute_pattern_vars(
                                            t,
                                            &pattern_subst,
                                        )
                                    })
                                    .collect();
                                for (var_ty, pinned_ty) in
                                    trait_type_arg_types.iter().zip(pinned.iter())
                                {
                                    let _ = self.unify(var_ty, pinned_ty);
                                }
                                impl_info = Some(info);
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
                                let expected_extra = crate::typechecker::check_traits::substitute_pattern_vars(
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
                        if is_generic_trait_name(&trait_name)
                            && let Some(rep_ty) = trait_type_arg_types.first()
                            && let Some(record_ty) =
                                anon_record_from_generic_rep(&self.sub.apply(rep_ty))
                        {
                            self.unify_at(&Type::Var(*id), &record_ty, span)?;
                            self.trait_state.pending_constraints.push((
                                trait_name,
                                trait_type_arg_types,
                                Type::Var(*id),
                                span,
                                node_id,
                            ));
                            continue;
                        }

                        if is_generic_trait_name(&trait_name) {
                            let mut extra_vars = Vec::new();
                            for extra in &trait_type_arg_types {
                                crate::typechecker::collect_free_vars(&self.sub.apply(extra), &mut extra_vars);
                            }
                            if !extra_vars.is_empty()
                                && !self.trait_state.pending_constraints.is_empty()
                            {
                                self.trait_state.pending_constraints.push((
                                    trait_name,
                                    trait_type_arg_types,
                                    Type::Var(*id),
                                    span,
                                    node_id,
                                ));
                                continue;
                            }
                        }

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
                                (trait_name, trait_type_arg_types, Type::Var(*id), span, node_id),
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
                            trait_type_args: trait_type_arg_types.iter().map(|t| self.sub.apply(t)).collect(),
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
                    Type::Record(fields) => {
                        let resolved_trait = self
                            .resolve_trait_name(&trait_name)
                            .unwrap_or_else(|| trait_name.clone());
                        if is_generic_trait_name(&resolved_trait) {
                            let rep_ty = anon_record_generic_rep(fields);
                            for extra in &trait_type_arg_types {
                                self.unify_at(extra, &rep_ty, span)?;
                            }
                            let resolved_extra_types: Vec<Type> = trait_type_arg_types
                                .iter()
                                .map(|t| self.sub.apply(t))
                                .collect();
                            self.evidence.push(crate::typechecker::TraitEvidence {
                                node_id,
                                trait_name: trait_name.clone(),
                                resolved_type: None,
                                resolved_record_type: Some(resolved.clone()),
                                type_var_name: None,
                                trait_type_args: resolved_extra_types,
                                resolved_symbol: None,
                            });
                            continue;
                        }
                        let display = trait_name.rsplit('.').next().unwrap_or(&trait_name);
                        return Err(rewrite_diag(
                            format!("no impl of {} for anonymous record type", display),
                            span,
                        ));
                    }
                    Type::Symbol(name) => {
                        let resolved_trait = self
                            .resolve_trait_name(&trait_name)
                            .unwrap_or_else(|| trait_name.clone());
                        if resolved_trait == crate::typechecker::KNOWN_SYMBOL_TRAIT {
                            self.evidence.push(crate::typechecker::TraitEvidence {
                                node_id,
                                trait_name: resolved_trait,
                                resolved_type: None,
                                resolved_record_type: None,
                                type_var_name: None,
                                trait_type_args: vec![],
                                resolved_symbol: Some(name.clone()),
                            });
                        } else {
                            let display = trait_name.rsplit('.').next().unwrap_or(&trait_name);
                            return Err(rewrite_diag(
                                format!("no impl of {} for symbol type '{}", display, name),
                                span,
                            ));
                        }
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
            // grows) — while making fundep solving order-independent.
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
