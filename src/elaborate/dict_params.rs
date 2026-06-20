use super::*;

impl Elaborator {
    /// Per-operation dict params for a handler arm, looked up by the arm's
    /// resolved (or qualified) effect and op name. Empty when the op has no
    /// `where` constraints of its own.
    pub(crate) fn op_dict_params_for_arm(&self, arm: &HandlerArm) -> Vec<(String, String)> {
        let effect = self
            .resolution
            .handler_arm(arm.id)
            .map(|r| r.effect.clone())
            .or_else(|| arm.qualifier.clone());
        self.op_dict_params_lookup(effect.as_deref(), &arm.op_name)
    }


    /// Per-operation dict params for an `op!` call site, looked up by the call's
    /// resolved (or qualified) effect and op name.
    pub(crate) fn op_dict_params_for_call(
        &self,
        node_id: crate::ast::NodeId,
        op_name: &str,
        qualifier: Option<&str>,
    ) -> Vec<(String, String)> {
        let effect = self
            .resolution
            .effect_call(node_id)
            .map(|r| r.effect.clone())
            .or_else(|| qualifier.map(str::to_string));
        self.op_dict_params_lookup(effect.as_deref(), op_name)
    }


    /// If `expr` is an App spine whose head is an `EffectCall` for an operation
    /// with its own `where` constraints, elaborate it and append the per-call
    /// dictionary arguments (outermost, so they follow the user args). Returns
    /// `None` for any other expression, leaving normal App elaboration to run.
    pub(crate) fn elaborate_effect_call_spine(&mut self, expr: &Expr) -> Option<Expr> {
        // Peel App nodes to find the EffectCall head and the user args (in order).
        let mut user_args: Vec<&Expr> = Vec::new();
        let mut current = expr;
        let (head, op_name, qualifier) = loop {
            match &current.kind {
                ExprKind::App { func, arg } => {
                    user_args.push(arg);
                    current = func;
                }
                ExprKind::EffectCall { name, qualifier, .. } => {
                    break (current, name.clone(), qualifier.clone());
                }
                _ => return None,
            }
        };
        user_args.reverse();

        let op_pairs = self.op_dict_params_for_call(head.id, &op_name, qualifier.as_deref());
        if op_pairs.is_empty() {
            return None;
        }

        // Rebuild the call spine with elaborated head and user args.
        let mut result = self.elaborate_expr(head);
        for arg in &user_args {
            let elab_arg = self.elaborate_expr(arg);
            result = Expr::synth(
                expr.span,
                ExprKind::App {
                    func: Box::new(result),
                    arg: Box::new(elab_arg),
                },
            );
        }

        // Append a dict arg per op constraint, resolved from the EffectCall
        // node's evidence (the concrete type is known at the call site).
        let mut trait_occurrences: HashMap<&str, usize> = HashMap::new();
        for (trait_name, _) in &op_pairs {
            let occ = trait_occurrences.entry(trait_name.as_str()).or_insert(0);
            if let Some(dict_expr) =
                self.resolve_dict_nth(trait_name, head.id, head.span, *occ)
            {
                result = Expr::synth(
                    expr.span,
                    ExprKind::App {
                        func: Box::new(result),
                        arg: Box::new(dict_expr),
                    },
                );
            }
            *occ += 1;
        }
        Some(result)
    }


    pub(crate) fn op_dict_params_lookup(&self, effect: Option<&str>, op_name: &str) -> Vec<(String, String)> {
        let Some(effect) = effect else {
            return Vec::new();
        };
        self.op_dict_params
            .get(&(effect.to_string(), op_name.to_string()))
            .cloned()
            .unwrap_or_default()
    }


    /// Extract dict param info from a where clause: [(trait_name, type_var_name)]
    /// for traits that use dictionary dispatch (excludes Num/Eq which use BIFs).
    ///
    /// Note: trait type args (the `_` in the destructure) are intentionally not used here.
    /// Dict params are keyed by (trait_name, self_type_var) - one dict per constraint.
    /// The extra type args (e.g. `b` in `a: ConvertTo b`) are resolved separately
    /// through TraitEvidence when looking up which concrete dict to pass at call sites.
    pub(crate) fn dict_params_from_where(&self, where_clause: &[TraitBound]) -> Vec<(String, String)> {
        let mut dict_params = Vec::new();
        for bound in where_clause {
            for tr in &bound.traits {
                if tr.name != "Num" && tr.name != "Eq" {
                    let resolved = self.resolved_trait_name(tr.id, &tr.name);
                    let suffix =
                        dict_var_suffix_from_type_exprs(&self.traits, &resolved, &tr.type_args);
                    dict_params.push((resolved, format!("{}{}", bound.type_var, suffix)));
                }
            }
        }
        dict_params
    }


    /// Like [`dict_params_from_where`], but emits bounds that carry trait type
    /// arguments (multi-parameter traits, e.g. `field: ReadLeft out`) ahead of
    /// those that don't (e.g. `n: KnownSymbol`). This mirrors the order in
    /// which the call site applies sub-dictionaries: `dict_for_type`
    /// ([`dict_resolve`]) runs `param_constraints_by_var_with_args` before
    /// `param_constraints_by_var`, so a conditional impl's dict-constructor
    /// parameters must line up positionally with the args passed to it.
    ///
    /// Without this split, a where clause that *interleaves* the two kinds —
    /// `where {n: KnownSymbol, field: ReadLeft out}` — builds a constructor
    /// `(__dict_KnownSymbol_n, __dict_ReadLeft_field)` (source order) but is
    /// called with `(ReadLeft_field, KnownSymbol_n)`, binding the symbol-name
    /// String to `__dict_ReadLeft_field` and the ReadLeft dict tuple to
    /// `__dict_KnownSymbol_n` — a runtime crash when the latter is appended as
    /// a String. The where-clause order matters for any impl mixing a single-
    /// param bound with a multi-param bound; codecs over single-param traits
    /// (all bounds in `param_constraints_by_var`) are unaffected, which is why
    /// the derived `saga_json` path never hit this.
    pub(crate) fn dict_params_from_where_call_order(
        &self,
        where_clause: &[TraitBound],
    ) -> Vec<(String, String)> {
        let mut with_args = Vec::new();
        let mut without_args = Vec::new();
        for bound in where_clause {
            for tr in &bound.traits {
                if tr.name == "Num" || tr.name == "Eq" {
                    continue;
                }
                let resolved = self.resolved_trait_name(tr.id, &tr.name);
                let suffix =
                    dict_var_suffix_from_type_exprs(&self.traits, &resolved, &tr.type_args);
                let pair = (resolved, format!("{}{}", bound.type_var, suffix));
                if tr.type_args.is_empty() {
                    without_args.push(pair);
                } else {
                    with_args.push(pair);
                }
            }
        }
        with_args.extend(without_args);
        with_args
    }


    pub(crate) fn dict_params_from_where_apps(&self, where_apps: &[TraitApp]) -> Vec<(String, String)> {
        let mut dict_params = Vec::new();
        for app in where_apps {
            if matches!(app.trait_name.as_str(), "Num" | "Eq") {
                continue;
            }
            let Some(TypeExpr::Var { name, .. }) = app.type_args.first() else {
                continue;
            };
            let resolved = self.resolved_trait_name(app.id, &app.trait_name);
            // `type_args[0]` is the self var; the determinant extras are the rest.
            let suffix =
                dict_var_suffix_from_type_exprs(&self.traits, &resolved, &app.type_args[1..]);
            dict_params.push((resolved, format!("{}{}", name, suffix)));
        }
        dict_params
    }


    pub(crate) fn impl_type_param_id(type_params: &[TypeParam], name: &str) -> Option<u32> {
        type_params
            .iter()
            .position(|tp| tp.name == name)
            .map(|idx| u32::MAX - idx as u32)
    }


    pub(crate) fn impl_type_param_subst(args: &[Type]) -> HashMap<u32, Type> {
        args.iter()
            .enumerate()
            .map(|(idx, arg)| (u32::MAX - idx as u32, arg.clone()))
            .collect()
    }


    pub(crate) fn type_expr_to_constraint_type(
        &self,
        expr: &TypeExpr,
        type_params: &[TypeParam],
        local_subst: &HashMap<String, Type>,
    ) -> Option<Type> {
        match expr {
            TypeExpr::Named { id, name, .. } => {
                Some(Type::Con(self.resolved_type_name(*id, name), vec![]))
            }
            TypeExpr::Var { name, .. } => local_subst
                .get(name)
                .cloned()
                .or_else(|| Self::impl_type_param_id(type_params, name).map(Type::Var)),
            TypeExpr::App { .. } => {
                let head = expr.head_name()?;
                let head_id = expr.head_id().unwrap_or(expr.id());
                let mut args = Vec::new();
                let mut current = expr;
                while let TypeExpr::App { func, arg, .. } = current {
                    args.push(self.type_expr_to_constraint_type(arg, type_params, local_subst)?);
                    current = func;
                }
                args.reverse();
                Some(Type::Con(self.resolved_type_name(head_id, head), args))
            }
            TypeExpr::Symbol { name, .. } => Some(Type::Symbol(name.clone())),
            TypeExpr::Labeled { inner, .. } => {
                self.type_expr_to_constraint_type(inner, type_params, local_subst)
            }
            TypeExpr::Record { fields, .. } => fields
                .iter()
                .map(|(name, ty)| {
                    self.type_expr_to_constraint_type(ty, type_params, local_subst)
                        .map(|ty| (name.clone(), ty))
                })
                .collect::<Option<Vec<_>>>()
                .map(Type::Record),
            TypeExpr::Arrow { .. } => None,
        }
    }


    pub(crate) fn resolve_functional_where_app_fresh_vars(
        &self,
        app: &TraitApp,
        resolved_trait: &str,
        self_type: &Type,
        type_params: &[TypeParam],
        local_subst: &mut HashMap<String, Type>,
    ) {
        let Some(info) = self.traits.get(resolved_trait) else {
            return;
        };
        let Some(fundep) = &info.fundep else {
            return;
        };
        let Type::Con(self_name, self_args) = self_type else {
            return;
        };
        let Some((_, impl_info)) = self.impl_infos.iter().find(|((trait_name, _, target), _)| {
            trait_name == resolved_trait && target == self_name
        }) else {
            return;
        };
        let mut subst = HashMap::new();
        for (var_id, arg) in impl_info.target_type_param_ids.iter().zip(self_args.iter()) {
            subst.insert(*var_id, arg.clone());
        }
        // Only the *determined* parameters are pinned from the impl; the
        // determinant parameters are inputs, not outputs of the dependency.
        let determined = fundep.determined_extra_positions();
        for (idx, arg) in app.type_args.iter().enumerate().skip(1) {
            if !determined.contains(&(idx - 1)) {
                continue;
            }
            let TypeExpr::Var { name, .. } = arg else {
                continue;
            };
            if Self::impl_type_param_id(type_params, name).is_some()
                || local_subst.contains_key(name)
            {
                continue;
            }
            if let Some(extra) = impl_info.trait_type_args.get(idx - 1) {
                local_subst.insert(name.clone(), substitute_pattern_vars(extra, &subst));
            }
        }
    }


    pub(crate) fn where_app_dict_params_for_impl(
        &self,
        where_apps: &[TraitApp],
        type_params: &[TypeParam],
    ) -> Vec<ImplWhereAppDictParam> {
        let mut params = Vec::new();
        let mut local_subst = HashMap::new();
        for app in where_apps {
            if matches!(app.trait_name.as_str(), "Num" | "Eq") {
                continue;
            }
            let resolved_trait = self.resolved_trait_name(app.id, &app.trait_name);
            let Some(first_arg) = app.type_args.first() else {
                continue;
            };
            let Some(self_type) =
                self.type_expr_to_constraint_type(first_arg, type_params, &local_subst)
            else {
                continue;
            };

            self.resolve_functional_where_app_fresh_vars(
                app,
                &resolved_trait,
                &self_type,
                type_params,
                &mut local_subst,
            );

            let TypeExpr::Var { name, .. } = first_arg else {
                continue;
            };
            if Self::impl_type_param_id(type_params, name).is_some() {
                continue;
            }
            let Some(self_type) = local_subst.get(name).cloned() else {
                continue;
            };
            let Some(trait_type_args) = app.type_args[1..]
                .iter()
                .map(|arg| self.type_expr_to_constraint_type(arg, type_params, &local_subst))
                .collect::<Option<Vec<_>>>()
            else {
                continue;
            };
            params.push(ImplWhereAppDictParam {
                trait_name: resolved_trait,
                trait_type_args,
                self_type,
            });
        }
        params
    }


    /// Set up `current_dict_params` from a where clause, saving the previous state.
    /// Returns the saved state to be restored later via `restore_dict_params`.
    pub(crate) fn setup_dict_params_from_pairs(
        &mut self,
        dict_params: &[(String, String)],
    ) -> (HashMap<String, String>, HashMap<(String, String), String>) {
        let saved = (
            std::mem::take(&mut self.current_dict_params),
            std::mem::take(&mut self.current_dict_params_by_var),
        );
        for (resolved, type_var) in dict_params {
            let bare = resolved.rsplit('.').next().unwrap_or(resolved);
            let param_name = format!("__dict_{}_{}", bare, type_var);
            self.current_dict_params
                .insert(resolved.clone(), param_name.clone());
            self.current_dict_params_by_var
                .insert((resolved.clone(), type_var.clone()), param_name);
        }
        saved
    }


    pub(crate) fn setup_dict_params(
        &mut self,
        where_clause: &[TraitBound],
    ) -> (HashMap<String, String>, HashMap<(String, String), String>) {
        let dict_params = self.dict_params_from_where(where_clause);
        self.setup_dict_params_from_pairs(&dict_params)
    }


    /// Add dict params on top of the current ones (without clearing), returning
    /// the prior maps so the caller can restore them. Used for handler arms
    /// nested inside a function whose own dict params must stay in scope.
    pub(crate) fn push_dict_params_from_pairs(
        &mut self,
        dict_params: &[(String, String)],
    ) -> (HashMap<String, String>, HashMap<(String, String), String>) {
        let saved = (
            self.current_dict_params.clone(),
            self.current_dict_params_by_var.clone(),
        );
        for (resolved, type_var) in dict_params {
            let bare = resolved.rsplit('.').next().unwrap_or(resolved);
            let param_name = format!("__dict_{}_{}", bare, type_var);
            self.current_dict_params
                .insert(resolved.clone(), param_name.clone());
            self.current_dict_params_by_var
                .insert((resolved.clone(), type_var.clone()), param_name);
        }
        saved
    }


    /// Restore `current_dict_params` from a previous `setup_dict_params` call.
    pub(crate) fn restore_dict_params(
        &mut self,
        saved: (HashMap<String, String>, HashMap<(String, String), String>),
    ) {
        self.current_dict_params = saved.0;
        self.current_dict_params_by_var = saved.1;
    }

}
