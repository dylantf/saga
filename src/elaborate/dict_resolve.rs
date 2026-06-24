use super::*;

impl Elaborator {
    /// Resolve which dictionary to use for a given trait at a given node.
    /// Returns a DictRef expression or None if no evidence found.
    pub(crate) fn resolve_dict(
        &self,
        trait_name: &str,
        node_id: crate::ast::NodeId,
        span: Span,
    ) -> Option<Expr> {
        self.resolve_dict_nth(trait_name, node_id, span, 0)
    }

    pub(crate) fn resolve_call_dict_nth(
        &self,
        trait_name: &str,
        callee_id: crate::ast::NodeId,
        call_id: crate::ast::NodeId,
        span: Span,
        occurrence: usize,
    ) -> Option<Expr> {
        self.resolve_dict_nth(trait_name, callee_id, span, occurrence)
            .or_else(|| {
                (callee_id != call_id)
                    .then(|| self.resolve_dict_nth(trait_name, call_id, span, occurrence))
                    .flatten()
            })
    }

    pub(crate) fn resolve_dict_from_arg_type(
        &self,
        trait_name: &str,
        arg: &Expr,
        span: Span,
    ) -> Option<Expr> {
        let ty = self.type_at_node.get(&arg.id)?.clone();
        self.dict_for_type(trait_name, &[], &ty, span)
    }

    /// Resolve the `occurrence`-th evidence entry for `trait_name` at `node_id`.
    /// When a function has multiple where-clause bounds for the same trait
    /// (e.g. `where {a: Debug, b: Debug}`), each dict param needs a different
    /// evidence entry. The occurrence index selects which one.
    pub(crate) fn resolve_dict_nth(
        &self,
        trait_name: &str,
        node_id: crate::ast::NodeId,
        span: Span,
        occurrence: usize,
    ) -> Option<Expr> {
        // Check if we have evidence for this node
        if let Some(evidence_list) = self.evidence_by_node.get(&node_id) {
            let mut count = 0;
            for ev in evidence_list {
                if ev.trait_name == trait_name {
                    if count < occurrence {
                        count += 1;
                        continue;
                    }
                    // KnownSymbol with concrete symbol: dict is a bare String
                    // carrying the symbol's source name. SymbolIntrinsic lowers
                    // to the binary literal at codegen.
                    if let Some(sym) = &ev.resolved_symbol {
                        return Some(Expr::synth(
                            span,
                            ExprKind::SymbolIntrinsic {
                                symbol: sym.clone(),
                            },
                        ));
                    }
                    if let Some(record_ty) = &ev.resolved_record_type {
                        return self.dict_for_type(
                            trait_name,
                            &ev.trait_type_args,
                            record_ty,
                            span,
                        );
                    }
                    return match &ev.resolved_type {
                        Some((type_name, args)) => {
                            // Concrete type: build the dict via dict_for_type,
                            // which handles where-clause constraints correctly.
                            let ty = Type::Con(type_name.clone(), args.clone());
                            self.dict_for_type(trait_name, &ev.trait_type_args, &ty, span)
                        }
                        None => {
                            // Polymorphic: use the dict param from current function.
                            // If evidence has a type_var_name, use it to build the
                            // specific dict param name (handles multiple where-clause
                            // bounds for the same trait, e.g. `where {e: Show, a: Show}`).
                            if let Some(ref var_name) = ev.type_var_name {
                                self.dict_param_for_trait_var(
                                    trait_name,
                                    var_name,
                                    &ev.trait_type_args,
                                    span,
                                )
                            } else {
                                self.current_dict_param_or_supertrait(trait_name, span)
                            }
                        }
                    };
                }
            }
        }

        // No evidence at this node -- fall back to current function's dict param
        // (handles inferred constraints where the typechecker absorbed the constraint
        // into the function's scheme rather than recording node-level evidence).
        if let Some(expr) = self.current_dict_param_or_supertrait(trait_name, span) {
            return Some(expr);
        }

        // No matching evidence for this trait. Might be a built-in trait
        // (Num, Eq) that uses direct BEAM BIF dispatch rather than dictionary dispatch.
        None
    }

    pub(crate) fn supertrait_index(
        &self,
        subtrait: &str,
        required_supertrait: &str,
    ) -> Option<usize> {
        self.traits.get(subtrait).and_then(|info| {
            info.supertraits
                .iter()
                .position(|supertrait| supertrait == required_supertrait)
        })
    }

    pub(crate) fn project_supertrait_dict(
        &self,
        subtrait: &str,
        required_supertrait: &str,
        dict: Expr,
        span: Span,
    ) -> Option<Expr> {
        self.supertrait_index(subtrait, required_supertrait)
            .map(|supertrait_index| {
                Expr::synth(
                    span,
                    ExprKind::DictSuperAccess {
                        dict: Box::new(dict),
                        trait_name: subtrait.to_string(),
                        supertrait_index,
                    },
                )
            })
    }

    pub(crate) fn dict_param_for_trait_var(
        &self,
        trait_name: &str,
        var_name: &str,
        trait_type_args: &[Type],
        span: Span,
    ) -> Option<Expr> {
        // For multi-variable-determinant fundeps, several constraints on the
        // same self var are distinguished by a determinant suffix baked into
        // the dict-param's var key. Try the qualified key first; for ordinary
        // traits the suffix is empty so this is identical to the base lookup.
        let suffix = dict_var_suffix_from_types(&self.traits, trait_name, trait_type_args);
        let qualified_var = format!("{}{}", var_name, suffix);
        if let Some(param_name) = self
            .current_dict_params_by_var
            .get(&(trait_name.to_string(), qualified_var.clone()))
        {
            return Some(Expr::synth(
                span,
                ExprKind::Var {
                    name: param_name.clone(),
                },
            ));
        }

        for ((bound_trait, bound_var), param_name) in &self.current_dict_params_by_var {
            if bound_var == &qualified_var
                && let Some(projected) = self.project_supertrait_dict(
                    bound_trait,
                    trait_name,
                    Expr::synth(
                        span,
                        ExprKind::Var {
                            name: param_name.clone(),
                        },
                    ),
                    span,
                )
            {
                return Some(projected);
            }
        }

        None
    }

    pub(crate) fn current_dict_param_or_supertrait(
        &self,
        trait_name: &str,
        span: Span,
    ) -> Option<Expr> {
        if let Some(name) = self.current_dict_params.get(trait_name) {
            return Some(Expr::synth(span, ExprKind::Var { name: name.clone() }));
        }

        for (bound_trait, param_name) in &self.current_dict_params {
            if let Some(projected) = self.project_supertrait_dict(
                bound_trait,
                trait_name,
                Expr::synth(
                    span,
                    ExprKind::Var {
                        name: param_name.clone(),
                    },
                ),
                span,
            ) {
                return Some(projected);
            }
        }

        None
    }

    /// Build the show function expression for a concrete type.
    /// Returns an expression that, when applied to a value of that type, produces a string.
    pub(crate) fn show_fn_for_type(&self, trait_name: &str, ty: &Type, span: Span) -> Option<Expr> {
        let dict = self.dict_for_type(trait_name, &[], ty, span)?;
        Some(Expr::synth(
            span,
            ExprKind::DictMethodAccess {
                dict: Box::new(dict),
                trait_name: trait_name.to_string(),
                method_index: 0,
            },
        ))
    }

    /// Build the dict expression for a concrete type (the dict itself, not the method).
    /// `trait_type_args` are the resolved extra type arguments for multi-param traits.
    pub(crate) fn dict_for_type(
        &self,
        trait_name: &str,
        trait_type_args: &[Type],
        ty: &Type,
        span: Span,
    ) -> Option<Expr> {
        if matches!(trait_name, "Num" | "Eq") {
            return Some(Expr::synth(span, ExprKind::Tuple { elements: vec![] }));
        }

        match ty {
            Type::Record(fields) if is_generic_trait(trait_name) => {
                Some(self.build_anon_record_generic_dict(fields, span))
            }
            Type::Con(name, args)
                if name == crate::typechecker::canonicalize_type_name("Tuple")
                    && (trait_name == SHOW || trait_name == DEBUG) =>
            {
                // Tuples don't have a dict constructor; build an inline dict
                // containing the show lambda: {fun t -> "(" ++ ... ++ ")"}
                let show_lambda = self.build_tuple_show_lambda(trait_name, args, span)?;
                Some(Expr::synth(
                    span,
                    ExprKind::Tuple {
                        elements: vec![show_lambda],
                    },
                ))
            }
            Type::Con(name, args) => {
                // Tuple impls are arity-keyed (`Std.Base.Tuple.2`), so for
                // tuple lookup we synthesize that name from the args. Non-
                // tuple names pass through `arity_keyed_target_name` unchanged.
                let keyed_name = crate::typechecker::arity_keyed_target_name(name, args.len());
                let key = (
                    trait_name.to_string(),
                    trait_type_arg_names(trait_type_args),
                    keyed_name,
                );
                let (key, inferred_trait_args_from_target) = if self.dict_names.contains_key(&key) {
                    (key, false)
                } else {
                    let matches: Vec<_> = self
                        .dict_names
                        .keys()
                        .filter(|(candidate_trait, _, candidate_target)| {
                            candidate_trait == trait_name && candidate_target == &key.2
                        })
                        .cloned()
                        .collect();
                    let chosen = if matches.len() <= 1 {
                        matches.into_iter().next()
                    } else {
                        // Several impls share this trait + arity-keyed target
                        // head (e.g. two disjoint `Column src Required n a` and
                        // `Column src Optional n a` Selectable impls). The
                        // trait args here are typically still unresolved out-
                        // vars, so disambiguate on the concrete self type:
                        // match each impl's full target pattern against `ty` —
                        // the distinct concrete constructors in the determining
                        // positions leave exactly one match.
                        let mut pattern_matched: Vec<ImplKey> = matches
                            .into_iter()
                            .filter(|candidate| {
                                self.impl_infos
                                    .get(candidate)
                                    .and_then(|info| info.target_pattern.as_ref())
                                    .is_some_and(|pattern| {
                                        let mut subst = HashMap::new();
                                        match_type_pattern(pattern, ty, &mut subst)
                                    })
                            })
                            .collect();
                        (pattern_matched.len() == 1)
                            .then(|| pattern_matched.pop())
                            .flatten()
                    };
                    match chosen {
                        Some(key) => (key, true),
                        None => return None,
                    }
                };
                let dict_name = self.dict_names.get(&key)?;
                let impl_info = self.impl_infos.get(&key);
                let mut dict_expr: Expr = Expr::synth(
                    span,
                    ExprKind::DictRef {
                        name: dict_name.clone(),
                    },
                );
                // Local impls are recorded in `impl_where_app_dict_params`
                // (always, even empty). Imported impls are not — the importing
                // module never sees their AST — so fall back to the resolved
                // copy the typechecker stashed on `ImplInfo`.
                if let Some(params) = self
                    .impl_where_app_dict_params
                    .get(&key)
                    .or_else(|| self.impl_infos.get(&key).map(|i| &i.where_app_dict_params))
                {
                    let target_arg_subst = Self::impl_type_param_subst(args);
                    for param in params {
                        let self_type =
                            substitute_pattern_vars(&param.self_type, &target_arg_subst);
                        let trait_type_args: Vec<Type> = param
                            .trait_type_args
                            .iter()
                            .map(|arg| substitute_pattern_vars(arg, &target_arg_subst))
                            .collect();
                        let sub_dict = self.dict_for_type(
                            &param.trait_name,
                            &trait_type_args,
                            &self_type,
                            span,
                        )?;
                        dict_expr = Expr::synth(
                            span,
                            ExprKind::App {
                                func: Box::new(dict_expr),
                                arg: Box::new(sub_dict),
                            },
                        );
                    }
                }
                if let Some(info) = impl_info
                    && let Some(pattern) = &info.target_pattern
                {
                    let mut subst = HashMap::new();
                    if !match_type_pattern(pattern, ty, &mut subst) {
                        return None;
                    }
                    if !inferred_trait_args_from_target {
                        if info.trait_type_args.len() != trait_type_args.len() {
                            return None;
                        }
                        for (pattern_arg, actual_arg) in
                            info.trait_type_args.iter().zip(trait_type_args.iter())
                        {
                            if !match_type_pattern(pattern_arg, actual_arg, &mut subst) {
                                return None;
                            }
                        }
                    }
                    for (constraint_trait, var_id, extra_types) in
                        &info.param_constraints_by_var_with_args
                    {
                        // Num/Eq dispatch via BEAM BIFs, not dictionaries, so the
                        // impl's dict constructor takes no parameter for them
                        // (see `dict_params_from_where*`). Applying a `{}` here
                        // would over-apply the constructor and crash with badfun.
                        if matches!(constraint_trait.as_str(), "Num" | "Eq") {
                            continue;
                        }
                        let arg_ty = subst.get(var_id)?;
                        let resolved_extra_types: Vec<Type> = extra_types
                            .iter()
                            .map(|extra| substitute_pattern_vars(extra, &subst))
                            .collect();
                        let sub_dict = self.dict_for_type(
                            constraint_trait,
                            &resolved_extra_types,
                            arg_ty,
                            span,
                        )?;
                        dict_expr = Expr::synth(
                            span,
                            ExprKind::App {
                                func: Box::new(dict_expr),
                                arg: Box::new(sub_dict),
                            },
                        );
                    }
                    for (constraint_trait, var_id) in &info.param_constraints_by_var {
                        if matches!(constraint_trait.as_str(), "Num" | "Eq") {
                            continue;
                        }
                        let arg_ty = subst.get(var_id)?;
                        let sub_dict = self.dict_for_type(constraint_trait, &[], arg_ty, span)?;
                        dict_expr = Expr::synth(
                            span,
                            ExprKind::App {
                                func: Box::new(dict_expr),
                                arg: Box::new(sub_dict),
                            },
                        );
                    }
                } else if let Some(constraints) = self.impl_dict_params.get(&key) {
                    // Use explicit where-clause constraints (handles cases like
                    // Ord where the impl needs both Ord and Eq dicts per type param).
                    for (constraint_trait, param_idx) in constraints {
                        if matches!(constraint_trait.as_str(), "Num" | "Eq") {
                            continue;
                        }
                        if let Some(arg_ty) = args.get(*param_idx) {
                            let sub_dict =
                                self.dict_for_type(constraint_trait, &[], arg_ty, span)?;
                            dict_expr = Expr::synth(
                                span,
                                ExprKind::App {
                                    func: Box::new(dict_expr),
                                    arg: Box::new(sub_dict),
                                },
                            );
                        }
                    }
                } else {
                    // Fallback: one sub-dict per type arg for the main trait.
                    // Works for simple cases like Show for List a where {a: Show}.
                    for arg_ty in args {
                        let sub_dict =
                            self.dict_for_type(trait_name, trait_type_args, arg_ty, span)?;
                        dict_expr = Expr::synth(
                            span,
                            ExprKind::App {
                                func: Box::new(dict_expr),
                                arg: Box::new(sub_dict),
                            },
                        );
                    }
                }
                Some(dict_expr)
            }
            Type::Var(id) => {
                // Polymorphic type var: look up the current scope's dict param
                // for this trait + var combination. Two key conventions live
                // in `current_dict_params_by_var`:
                //   - inferred constraints store keys as `"v{id}"`
                //   - explicit where-clause bounds store keys as the source
                //     name (e.g. `"a"`)
                // Try both. For the source-name path we translate the var id
                // through `where_bound_var_names` (recorded by the typechecker
                // at impl/fn registration). Without this translation, two
                // distinct vars bound to the same trait (e.g. tuple impl
                // `where {a: ToJson, b: ToJson, c: ToJson}`) would all fall
                // through to the single-trait fallback and resolve to the
                // last-inserted dict.
                let var_key = format!("v{}", id);
                if let Some(expr) =
                    self.dict_param_for_trait_var(trait_name, &var_key, trait_type_args, span)
                {
                    return Some(expr);
                }
                if let Some(src_name) = self.where_bound_var_names.get(id)
                    && let Some(expr) =
                        self.dict_param_for_trait_var(trait_name, src_name, trait_type_args, span)
                {
                    return Some(expr);
                }
                // Fall back to single-trait lookup
                self.current_dict_param_or_supertrait(trait_name, span)
            }
            Type::Symbol(name) => {
                // KnownSymbol's "dict" is the symbol's source name as a String.
                // SymbolIntrinsic lowers to a binary literal at codegen. This
                // branch fires when a parameterized impl (e.g.
                // `impl ToJson for Variant n a where {n: KnownSymbol, ...}`)
                // recursively constructs a sub-dict for the symbol parameter.
                Some(Expr::synth(
                    span,
                    ExprKind::SymbolIntrinsic {
                        symbol: name.clone(),
                    },
                ))
            }
            _ => None,
        }
    }
}
