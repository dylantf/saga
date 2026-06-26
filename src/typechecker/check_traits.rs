use crate::ast::{self, TypeParam};
use crate::token::Span;

use super::unify::kind_name;
use super::{Checker, Diagnostic, ImplInfo, Scheme, TraitMethodEffectSig, Type};

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

/// Conservatively decide whether two impl target patterns can never describe
/// the same type. Used by the functional-dependency coherence check: two impls
/// whose determining parameter (the `for` target) shares an arity-keyed head
/// (e.g. both `Column`) may still be perfectly disjoint when some concrete
/// argument position differs — e.g. `Column src Required n a` vs
/// `Column src Optional n a`, where `Required` and `Optional` are distinct
/// nullary constructors. Returns `true` only when we are certain there is a
/// definite clash; pattern variables match anything and so are never disjoint.
pub(crate) fn types_disjoint(a: &Type, b: &Type) -> bool {
    match (a, b) {
        (Type::Var(_), _) | (_, Type::Var(_)) => false,
        (Type::Con(n1, a1), Type::Con(n2, a2)) => {
            n1 != n2 || a1.len() != a2.len() || a1.iter().zip(a2).any(|(x, y)| types_disjoint(x, y))
        }
        (Type::Symbol(s1), Type::Symbol(s2)) => s1 != s2,
        _ => false,
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
        (Type::Symbol(a), Type::Symbol(b)) => a == b,
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
        functional_dependency: Option<&ast::TraitFunctionalDependency>,
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
        let has_builtin_functional_rule = FUNCTIONAL_TRAITS.contains(&canonical_name.as_str());
        // Resolve the parameter name -> index, used to build the fundep's
        // index sets and validate that every mentioned name is a real param.
        let param_index = |name: &str| type_params.iter().position(|tp| tp.name == name);
        let mut fundep: Option<super::TraitFundep> = None;
        if let Some(fd) = functional_dependency {
            let Some(first_param) = type_params.first() else {
                return Err(Diagnostic::error_at(
                    fd.span,
                    "functional dependency requires a trait self parameter".to_string(),
                ));
            };
            if fd.determined.is_empty() {
                return Err(Diagnostic::error_at(
                    fd.span,
                    "functional dependency must determine at least one parameter".to_string(),
                ));
            }
            // The self/first parameter must be a determinant: concrete-self
            // impl selection recovers the determined params from the self type,
            // so the self type has to sit on the determining side.
            if !fd.determinant.iter().any(|d| d == &first_param.name) {
                return Err(Diagnostic::error_at(
                    fd.span,
                    format!(
                        "unsupported functional dependency: the trait's first parameter `{}` must appear on the determining side",
                        first_param.name
                    ),
                ));
            }
            let mut determinant_idx = Vec::new();
            for d in &fd.determinant {
                let Some(idx) = param_index(d) else {
                    return Err(Diagnostic::error_at(
                        fd.span,
                        format!(
                            "functional dependency mentions unknown trait parameter `{}`",
                            d
                        ),
                    ));
                };
                if determinant_idx.contains(&idx) {
                    return Err(Diagnostic::error_at(
                        fd.span,
                        format!(
                            "functional dependency repeats determining parameter `{}`",
                            d
                        ),
                    ));
                }
                determinant_idx.push(idx);
            }
            let mut determined_idx = Vec::new();
            for d in &fd.determined {
                let Some(idx) = param_index(d) else {
                    return Err(Diagnostic::error_at(
                        fd.span,
                        format!(
                            "functional dependency mentions unknown trait parameter `{}`",
                            d
                        ),
                    ));
                };
                if determinant_idx.contains(&idx) {
                    return Err(Diagnostic::error_at(
                        fd.span,
                        format!("functional dependency cannot determine `{}` from itself", d),
                    ));
                }
                if determined_idx.contains(&idx) {
                    return Err(Diagnostic::error_at(
                        fd.span,
                        format!("functional dependency repeats determined parameter `{}`", d),
                    ));
                }
                determined_idx.push(idx);
            }
            // Every parameter must be covered: a param that is neither
            // determining nor determined would be left free, which breaks the
            // coherence guarantee the rest of the compiler relies on.
            if determinant_idx.len() + determined_idx.len() != type_params.len() {
                let uncovered: Vec<&str> = type_params
                    .iter()
                    .enumerate()
                    .filter(|(i, _)| !determinant_idx.contains(i) && !determined_idx.contains(i))
                    .map(|(_, tp)| tp.name.as_str())
                    .collect();
                return Err(Diagnostic::error_at(
                    fd.span,
                    format!(
                        "functional dependency must cover all trait parameters; `{}` left undetermined",
                        uncovered.join(" ")
                    ),
                ));
            }
            fundep = Some(super::TraitFundep {
                determinant: determinant_idx,
                determined: determined_idx,
            });
        } else if has_builtin_functional_rule {
            // Legacy builtin rule (Generic): first param determines the rest.
            fundep = Some(super::TraitFundep {
                determinant: vec![0],
                determined: (1..type_params.len()).collect(),
            });
        }
        let is_functional = fundep.is_some();
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
                fundep,
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
        is_routed_derive: bool,
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
                let fresh = self.fresh_var_of_kind(tp.kind);
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
        if let Some(fundep) = &trait_info.fundep {
            // Positions (within the extra trait args) of the determinant
            // parameters other than self. Self is `target_key`, handled below.
            let det_extra_positions = fundep.determinant_extra_positions();
            for ((existing_trait, existing_args, existing_target), existing_info) in
                &self.trait_state.impls
            {
                // Two impls clash only when their determining inputs coincide:
                // the self head (`target_key`) and every determinant extra arg
                // must match. Differing on a determinant arg means the impls
                // determine outputs for distinct inputs, so they may coexist.
                let determinants_agree = existing_target == &target_key
                    && det_extra_positions
                        .iter()
                        .all(|&p| existing_args.get(p) == trait_type_args_names.get(p));
                if existing_trait == trait_name
                    && determinants_agree
                    && existing_args != trait_type_args_names
                {
                    // The determining inputs coincide, but the functional
                    // dependency is only violated if the targets can actually
                    // overlap. Compare the full target patterns: distinct
                    // concrete constructors in the same argument position (e.g.
                    // `Required` vs `Optional`) make the targets disjoint, so
                    // both impls may coexist.
                    if let Some(existing_pattern) = &existing_info.target_pattern
                        && types_disjoint(existing_pattern, &target)
                    {
                        continue;
                    }
                    let prev_loc = match existing_info.span {
                        Some(s) => format!(" (previous impl at byte {})", s.start),
                        None => String::new(),
                    };
                    return Err(Diagnostic::error_at(
                        span,
                        format!(
                            "coherence violation: trait {} requires that the determining \
                             parameters functionally determine the rest, but `{}` already has an \
                             impl with the same determining arguments but different determined \
                             arguments ({:?} vs {:?}){}",
                            trait_name, target_type, existing_args, trait_type_arg_names, prev_loc
                        ),
                    ));
                }
            }
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
                    self.validate_trait_bound_kind(
                        &resolved_req,
                        &bound.type_var,
                        var_id,
                        tr.span,
                    )?;
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
        // Process source-order; later constraints can reference fresh vars
        // resolved by earlier ones. For functional traits, the bound first
        // param determines the remaining params via the [Phase 1b] coherence
        // rule; for non-functional traits, all args must be already bound.
        let mut local_subst: std::collections::HashMap<String, String> =
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

        let mut declared_effects: std::collections::HashSet<String> = needs
            .iter()
            .map(|e| self.resolved_effect_name(e.id, &e.name))
            .collect();
        // Routed-derive impls are synthesized with `needs: vec![]`. Their
        // effect rows come from the trait method signatures — which were
        // canonicalized at trait-registration time in the trait's defining
        // module — rather than from source-level EffectRefs we'd have to
        // re-resolve in the consuming module (which may not even have those
        // effects in scope). See docs/name-resolution.md: "instances, rows,
        // and lowering metadata can still be computed later" from already-
        // resolved trait data.
        if is_routed_derive {
            for tm in &trait_info.methods {
                if methods.iter().any(|m| m.name == tm.name) {
                    for eff in &tm.effect_sig.effects {
                        declared_effects.insert(eff.clone());
                    }
                }
            }
        }

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
            // opt-in"). Routed-derive impls are synthesized from the trait
            // methods themselves, so they are within the row by construction;
            // skip them to avoid false positives on canonicalization edge cases.
            if !is_routed_derive && !trait_method.effect_sig.is_open_row {
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
                        self.validate_trait_bound_kind(
                            &resolved_req,
                            &bound.type_var,
                            var_id,
                            tr.span,
                        )?;
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

        // Resolve the fundep-determined `where`-app dict params now, while the
        // full impl registry is in scope, and stash them on the ImplInfo. The
        // elaborator recomputes these for impls in its own module, but an
        // importing module never sees this impl's AST, so it relies on this
        // pre-resolved copy (which travels via `ModuleExports.trait_impls`).
        let where_app_dict_params = self.compute_where_app_dict_params(where_apps, type_params);

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
                where_app_dict_params,
            },
        );
        Ok(())
    }

    fn impl_tparam_id(type_params: &[TypeParam], name: &str) -> Option<u32> {
        type_params
            .iter()
            .position(|tp| tp.name == name)
            .map(|idx| u32::MAX - idx as u32)
    }

    /// Typechecker-side mirror of the elaborator's
    /// `Elaborator::type_expr_to_constraint_type`: convert a `where`-app type
    /// argument into a `Type`, using the `u32::MAX - idx` convention for impl
    /// type parameters so the result matches what `dict_for_type` expects.
    fn where_app_constraint_type(
        &self,
        expr: &ast::TypeExpr,
        type_params: &[TypeParam],
        local_subst: &std::collections::HashMap<String, Type>,
    ) -> Option<Type> {
        match expr {
            ast::TypeExpr::Named { id, name, .. } => {
                Some(Type::Con(self.resolved_type_name(*id, name), vec![]))
            }
            ast::TypeExpr::Var { name, .. } => local_subst
                .get(name)
                .cloned()
                .or_else(|| Self::impl_tparam_id(type_params, name).map(Type::Var)),
            ast::TypeExpr::App { .. } => {
                let head = expr.head_name()?;
                let head_id = expr.head_id().unwrap_or(expr.id());
                let mut args = Vec::new();
                let mut current = expr;
                while let ast::TypeExpr::App { func, arg, .. } = current {
                    args.push(self.where_app_constraint_type(arg, type_params, local_subst)?);
                    current = func;
                }
                args.reverse();
                Some(Type::Con(self.resolved_type_name(head_id, head), args))
            }
            ast::TypeExpr::Symbol { name, .. } => Some(Type::Symbol(name.clone())),
            ast::TypeExpr::Labeled { inner, .. } => {
                self.where_app_constraint_type(inner, type_params, local_subst)
            }
            ast::TypeExpr::Record { fields, .. } => fields
                .iter()
                .map(|(name, ty)| {
                    self.where_app_constraint_type(ty, type_params, local_subst)
                        .map(|ty| (name.clone(), ty))
                })
                .collect::<Option<Vec<_>>>()
                .map(Type::Record),
            ast::TypeExpr::Arrow { .. } => None,
        }
    }

    /// Mirror of the elaborator's `resolve_functional_where_app_fresh_vars`:
    /// pin the determined extra params of a fundep `where`-app from the matching
    /// impl, recording them in `local_subst` so later args (and the self
    /// position) resolve to concrete types.
    fn resolve_fundep_where_app(
        &self,
        app: &ast::TraitApp,
        resolved_trait: &str,
        self_type: &Type,
        type_params: &[TypeParam],
        local_subst: &mut std::collections::HashMap<String, Type>,
    ) {
        let Some(info) = self.trait_state.traits.get(resolved_trait) else {
            return;
        };
        let Some(fundep) = &info.fundep else {
            return;
        };
        let Type::Con(self_name, self_args) = self_type else {
            return;
        };
        let Some((_, impl_info)) =
            self.trait_state
                .impls
                .iter()
                .find(|((trait_name, _, target), _)| {
                    trait_name == resolved_trait && target == self_name
                })
        else {
            return;
        };
        let mut subst = std::collections::HashMap::new();
        for (var_id, arg) in impl_info.target_type_param_ids.iter().zip(self_args.iter()) {
            subst.insert(*var_id, arg.clone());
        }
        let determined = fundep.determined_extra_positions();
        for (idx, arg) in app.type_args.iter().enumerate().skip(1) {
            if !determined.contains(&(idx - 1)) {
                continue;
            }
            let ast::TypeExpr::Var { name, .. } = arg else {
                continue;
            };
            if Self::impl_tparam_id(type_params, name).is_some() || local_subst.contains_key(name) {
                continue;
            }
            if let Some(extra) = impl_info.trait_type_args.get(idx - 1) {
                local_subst.insert(name.clone(), substitute_pattern_vars(extra, &subst));
            }
        }
    }

    /// Mirror of the elaborator's `where_app_dict_params_for_impl`, run at
    /// registration so the resolved params travel cross-module on `ImplInfo`.
    fn compute_where_app_dict_params(
        &self,
        where_apps: &[ast::TraitApp],
        type_params: &[TypeParam],
    ) -> Vec<crate::typechecker::state::WhereAppDictParam> {
        use crate::typechecker::state::WhereAppDictParam;
        let mut params = Vec::new();
        let mut local_subst: std::collections::HashMap<String, Type> =
            std::collections::HashMap::new();
        for app in where_apps {
            if matches!(app.trait_name.as_str(), "Num" | "Eq") {
                continue;
            }
            let resolved_trait = self
                .resolve_trait_name(&app.trait_name)
                .unwrap_or_else(|| app.trait_name.clone());
            let Some(first_arg) = app.type_args.first() else {
                continue;
            };
            let Some(self_type) =
                self.where_app_constraint_type(first_arg, type_params, &local_subst)
            else {
                continue;
            };
            self.resolve_fundep_where_app(
                app,
                &resolved_trait,
                &self_type,
                type_params,
                &mut local_subst,
            );
            let ast::TypeExpr::Var { name, .. } = first_arg else {
                continue;
            };
            if Self::impl_tparam_id(type_params, name).is_some() {
                continue;
            }
            let Some(self_type) = local_subst.get(name).cloned() else {
                continue;
            };
            let Some(trait_type_args) = app.type_args[1..]
                .iter()
                .map(|arg| self.where_app_constraint_type(arg, type_params, &local_subst))
                .collect::<Option<Vec<_>>>()
            else {
                continue;
            };
            params.push(WhereAppDictParam {
                trait_name: resolved_trait,
                trait_type_args,
                self_type,
            });
        }
        params
    }
}
