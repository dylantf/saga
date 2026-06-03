use super::*;

impl<'a, 'info> DirectLowerer<'a, 'info> {
    pub(super) fn classify_program(&mut self, program: &MProgram) {
        self.callable_type_shapes.clear();
        self.local_fun_bindings.clear();
        self.direct_values.clear();
        self.function_plans.clear();
        self.local_dict_constructor_arities.clear();
        self.local_hof_direct_specializations.clear();
        self.local_dict_constructors.clear();
        for decl in program {
            match decl {
                MDecl::FunBinding(fb) => {
                    self.local_fun_bindings.insert(fb.name.clone(), fb.clone());
                    let shape = match self.effect_info.fun_effects.get(&fb.name) {
                        Some(effects) if effects.is_empty() => RuntimeFunctionShape::Pure,
                        Some(effects) => {
                            RuntimeFunctionShape::Cps(crate::codegen::runtime_shape::CpsShape {
                                static_effects: effects.iter().cloned().collect(),
                                is_open_row: false,
                            })
                        }
                        None => {
                            RuntimeFunctionShape::Cps(crate::codegen::runtime_shape::CpsShape {
                                static_effects: vec![],
                                is_open_row: true,
                            })
                        }
                    };
                    self.callable_type_shapes.insert(fb.name.clone(), shape);
                }
                MDecl::Val(v) => {
                    if self.expr_is_direct_subset(&v.value) {
                        self.direct_values.insert(v.name.clone());
                    }
                }
                MDecl::DictConstructor(dc) => {
                    if self.can_lower_dict_constructor(dc) {
                        self.local_dict_constructor_arities
                            .insert(dc.name.clone(), dc.dict_params.len());
                        self.local_dict_constructors
                            .insert(dc.name.clone(), dc.clone());
                    }
                }
                MDecl::Passthrough(_) => {}
            }
        }
    }

    pub(super) fn compute_function_lowering_plans(&mut self, program: &MProgram) {
        self.compute_direct_body_plans(program);
        self.compute_direct_cps_island_body_plans(program);
        self.compute_cps_body_plans(program);
        self.compute_hof_direct_specializations(program);
    }

    fn compute_direct_body_plans(&mut self, program: &MProgram) {
        let single_clause_funs = single_clause_function_names(program);
        let funs: Vec<&MFunBinding> = program
            .iter()
            .filter_map(|decl| match decl {
                MDecl::FunBinding(fb) => Some(fb),
                _ => None,
            })
            .collect();

        let mut changed = true;
        while changed {
            changed = false;
            for fb in &funs {
                if !single_clause_funs.contains(&fb.name) {
                    continue;
                }
                if self.function_plans.contains_key(&fb.name) {
                    continue;
                }
                if self.can_lower_fun_binding(fb) {
                    self.function_plans
                        .insert(fb.name.clone(), FunctionLoweringPlan::DirectBody);
                    changed = true;
                }
            }
        }
    }

    fn compute_cps_body_plans(&mut self, program: &MProgram) {
        let single_clause_funs = single_clause_function_names(program);
        for decl in program {
            let MDecl::FunBinding(fb) = decl else {
                continue;
            };
            if !single_clause_funs.contains(&fb.name) {
                continue;
            }
            if self.function_plans.contains_key(&fb.name) {
                continue;
            }
            if self.can_lower_cps_fun_binding(fb) {
                self.function_plans
                    .insert(fb.name.clone(), FunctionLoweringPlan::CpsBody);
            }
        }
    }

    fn compute_hof_direct_specializations(&mut self, program: &MProgram) {
        let single_clause_funs = single_clause_function_names(program);
        for decl in program {
            let MDecl::FunBinding(fb) = decl else {
                continue;
            };
            if !single_clause_funs.contains(&fb.name) {
                continue;
            }
            if !matches!(
                self.function_plans.get(&fb.name),
                Some(FunctionLoweringPlan::CpsBody)
            ) {
                continue;
            }
            if let Some(specialization) = self.hof_direct_specialization_for_fun_binding(fb) {
                self.local_hof_direct_specializations
                    .insert(fb.name.clone(), specialization);
            }
        }
    }

    fn compute_direct_cps_island_body_plans(&mut self, program: &MProgram) {
        let single_clause_funs = single_clause_function_names(program);
        for decl in program {
            let MDecl::FunBinding(fb) = decl else {
                continue;
            };
            if !single_clause_funs.contains(&fb.name) {
                continue;
            }
            if self.function_plans.contains_key(&fb.name) {
                continue;
            }
            if self.can_lower_direct_cps_island_fun_binding(fb) {
                self.function_plans.insert(
                    fb.name.clone(),
                    FunctionLoweringPlan::DirectBodyWithCpsIsland,
                );
            }
        }
    }

    pub(super) fn compute_local_function_entries(&mut self, program: &MProgram) {
        self.local_function_entries.clear();
        for decl in program {
            let MDecl::FunBinding(fb) = decl else {
                continue;
            };
            let callable_type_shape = self
                .callable_type_shapes
                .get(&fb.name)
                .cloned()
                .unwrap_or_else(|| {
                    RuntimeFunctionShape::Cps(crate::codegen::runtime_shape::CpsShape {
                        static_effects: vec![],
                        is_open_row: true,
                    })
                });
            let entries = FunctionEntryInfo::from_fun_binding(
                fb,
                callable_type_shape,
                self.function_plans.get(&fb.name).copied(),
            );
            self.local_function_entries.insert(fb.name.clone(), entries);
        }
    }

    pub(super) fn compute_imported_function_entries(&mut self) {
        self.imported_function_entries.clear();
        self.imported_hof_direct_specializations.clear();
        for (source_module_name, compiled) in &self.module_ctx.modules {
            if source_module_name == &self.current_module
                || source_module_name.starts_with("Std.")
                || compiled.elaborated.is_empty()
                || !self.current_module_references_module(source_module_name)
            {
                continue;
            }

            let anf_imported = crate::codegen::anf::normalize(
                compiled.elaborated.clone(),
                Some(&compiled.resolution),
            );
            let imported_handler_decls = HashMap::new();
            let (monadic_imported, _) = crate::codegen::monadic::translate::translate_with_imports(
                &anf_imported,
                &compiled.resolution,
                self.effect_info,
                &imported_handler_decls,
            );

            let mut imported = DirectLowerer::new(
                &compiled.resolution,
                self.ctors,
                self.module_ctx,
                self.handler_info,
                self.effect_info,
                LoweringOptions::default(),
            );
            imported.current_module = source_module_name.clone();
            imported.classify_program(&monadic_imported);
            imported.apply_codegen_info_function_shapes(&compiled.codegen_info);
            imported.compute_function_lowering_plans(&monadic_imported);
            imported.compute_local_function_entries(&monadic_imported);

            let erlang_module = erlang_module_name(source_module_name);
            for (name, specialization) in
                imported.import_metadata_hof_direct_specializations(&monadic_imported)
            {
                self.imported_hof_direct_specializations.insert(
                    (erlang_module.clone(), name.clone()),
                    specialization.clone(),
                );
                self.imported_hof_direct_specializations
                    .insert((source_module_name.clone(), name.clone()), specialization);
            }
            for (name, entries) in imported.local_function_entries {
                self.imported_function_entries
                    .insert((erlang_module.clone(), name.clone()), entries.clone());
                self.imported_function_entries
                    .insert((source_module_name.clone(), name.clone()), entries);
            }
        }
    }

    fn current_module_references_module(&self, source_module_name: &str) -> bool {
        if let Some(current) = self.module_ctx.modules.get(&self.current_module) {
            return current.elaborated.iter().any(|decl| {
                matches!(
                    decl,
                    crate::ast::Decl::Import { module_path, .. }
                        if module_path.join(".") == source_module_name
                )
            });
        }

        let erlang_module = erlang_module_name(source_module_name);
        self.resolution.values().any(|resolved| {
            matches!(
                &resolved.kind,
                ResolvedCodegenKind::BeamFunction {
                    erlang_mod: Some(module),
                    ..
                } if module == &erlang_module
            )
        })
    }

    pub(super) fn apply_codegen_info_function_shapes(
        &mut self,
        info: &crate::typechecker::ModuleCodegenInfo,
    ) {
        for (name, effects) in &info.fun_effects {
            let shape = if effects.is_empty() {
                RuntimeFunctionShape::Pure
            } else {
                RuntimeFunctionShape::Cps(crate::codegen::runtime_shape::CpsShape {
                    static_effects: effects.clone(),
                    is_open_row: false,
                })
            };
            self.callable_type_shapes.insert(name.clone(), shape);
        }
    }

    fn import_metadata_hof_direct_specializations(
        &mut self,
        program: &MProgram,
    ) -> Vec<(String, HofDirectSpecialization)> {
        program
            .iter()
            .filter_map(|decl| {
                let MDecl::FunBinding(fb) = decl else {
                    return None;
                };
                self.hof_direct_specialization_for_fun_binding(fb)
                    .map(|specialization| (fb.name.clone(), specialization))
            })
            .collect()
    }

    pub(super) fn assert_no_unlowered_direct_body_functions(&self, program: &MProgram) {
        for decl in program {
            let MDecl::FunBinding(fb) = decl else {
                continue;
            };
            if self
                .local_function_entries
                .get(&fb.name)
                .is_some_and(|entries| {
                    matches!(entries.callable_type_shape, RuntimeFunctionShape::Pure)
                        && entries.direct_entry_arity.is_none()
                })
            {
                self.unsupported(&format!(
                    "direct function '{}' is outside the current direct subset",
                    fb.name
                ));
            }
        }
    }

    pub(super) fn assert_no_unlowered_public_cps_functions(
        &self,
        program: &MProgram,
        is_public: &impl Fn(&str) -> bool,
        is_entry: &impl Fn(&str) -> bool,
    ) {
        for decl in program {
            let MDecl::FunBinding(fb) = decl else {
                continue;
            };
            if (fb.public || is_public(&fb.name) || is_entry(&fb.name))
                && self
                    .local_function_entries
                    .get(&fb.name)
                    .is_some_and(|entries| {
                        entries.is_cps_typed() && entries.cps_adapter_entry_arity.is_none()
                    })
            {
                self.unsupported(&format!(
                    "CPS-shaped function '{}' is not lowered by selective-core yet",
                    fb.name
                ));
            }
        }
    }

    pub(super) fn assert_all_declarations_have_selective_plans(&self, program: &MProgram) {
        for decl in program {
            match decl {
                MDecl::FunBinding(fb) if !self.function_plans.contains_key(&fb.name) => {
                    self.unsupported(&format!(
                        "function '{}' has no selective lowering plan with fallback disabled",
                        fb.name
                    ));
                }
                MDecl::Val(v) if !self.direct_values.contains(&v.name) => {
                    self.unsupported(&format!(
                        "value '{}' has no selective lowering plan with fallback disabled",
                        v.name
                    ));
                }
                MDecl::DictConstructor(dc)
                    if !self.local_dict_constructor_arities.contains_key(&dc.name) =>
                {
                    self.unsupported(&format!(
                        "dict constructor '{}' has no selective lowering plan with fallback disabled",
                        dc.name
                    ));
                }
                MDecl::FunBinding(_)
                | MDecl::Val(_)
                | MDecl::DictConstructor(_)
                | MDecl::Passthrough(_) => {}
            }
        }
    }

    fn can_lower_dict_constructor(&mut self, dc: &MDictConstructor) -> bool {
        self.push_scope();
        for dict_param in &dc.dict_params {
            self.current_scope_mut().insert(dict_param.clone());
        }
        let supported = dc.methods.iter().enumerate().all(|(index, method)| {
            let MExpr::Pure(Atom::Lambda { params, body, .. }) = method else {
                return false;
            };
            if params.iter().any(|p| !direct_param_supported(p)) {
                return false;
            }
            let effectful = dc
                .method_effects
                .get(index)
                .is_some_and(|effects| !effects.is_empty())
                || dc.method_open_rows.get(index).copied().unwrap_or(false);
            self.push_scope();
            for pat in params {
                self.bind_pat_locals(pat);
            }
            let supported = if effectful {
                self.expr_is_cps_island_subset(body) || self.expr_is_direct_subset(body)
            } else {
                self.expr_is_direct_subset(body)
            };
            self.pop_scope();
            supported
        });
        self.pop_scope();
        supported
    }

    fn can_lower_fun_binding(&mut self, fb: &MFunBinding) -> bool {
        if fb.guard.is_some() || fb.params.iter().any(|p| !direct_param_supported(p)) {
            return false;
        }

        let prev_direct_candidate = self.direct_candidate_function.replace(fb.name.clone());
        self.push_scope();
        self.bind_fun_param_locals(fb);
        let supported = self.expr_is_direct_subset(&fb.body);
        self.pop_scope();
        self.direct_candidate_function = prev_direct_candidate;
        supported
    }

    fn can_lower_cps_fun_binding(&mut self, fb: &MFunBinding) -> bool {
        if fb.guard.is_some() || fb.params.iter().any(|p| !direct_param_supported(p)) {
            return false;
        }
        if !matches!(
            self.callable_type_shapes.get(&fb.name),
            Some(RuntimeFunctionShape::Cps(_))
        ) {
            return false;
        }

        self.push_scope();
        self.bind_fun_param_locals(fb);
        let supported = self.expr_is_cps_island_subset(&fb.body);
        self.pop_scope();
        supported
    }

    fn can_lower_direct_cps_island_fun_binding(&mut self, fb: &MFunBinding) -> bool {
        if fb.guard.is_some() || fb.params.iter().any(|p| !direct_param_supported(p)) {
            return false;
        }
        if !matches!(
            self.callable_type_shapes.get(&fb.name),
            Some(RuntimeFunctionShape::Pure)
        ) {
            return false;
        }

        self.push_scope();
        self.bind_fun_param_locals(fb);
        let supported = self.expr_is_cps_island_subset(&fb.body);
        self.pop_scope();
        supported
    }

    fn hof_direct_specialization_for_fun_binding(
        &mut self,
        fb: &MFunBinding,
    ) -> Option<HofDirectSpecialization> {
        if fb.guard.is_some() || fb.params.iter().any(|p| !direct_param_supported(p)) {
            return None;
        }
        if !matches!(
            self.callable_type_shapes.get(&fb.name),
            Some(RuntimeFunctionShape::Cps(_))
        ) {
            return None;
        }

        let (param_shapes, callback_params) = self.hof_direct_specialized_param_shapes(fb)?;
        if callback_params.is_empty() {
            return None;
        }

        self.push_scope();
        for (index, pat) in fb.params.iter().enumerate() {
            self.bind_pat_locals_with_shape(pat, param_shapes.get(index).cloned().flatten());
        }
        let supported = self.expr_is_direct_subset(&fb.body);
        self.pop_scope();
        supported.then(|| HofDirectSpecialization {
            entry_name: format!("__saga_direct_hof_{}", fb.name),
            source_arity: fb.params.len(),
            callback_params,
        })
    }

    pub(super) fn hof_direct_specialized_param_shapes(
        &self,
        fb: &MFunBinding,
    ) -> Option<(Vec<Option<LocalValueShape>>, Vec<HofCallbackParam>)> {
        let mut shapes = self.param_shapes_for_fun(fb);
        let mut callback_params = self.cps_callback_params_called_in_body(fb);
        for (index, pat) in fb.params.iter().enumerate() {
            let Pat::Var { id, .. } = pat else {
                continue;
            };
            if let Some((source_arity, _adapter_arity, _effects)) = self.cps_function_arity_at(*id)
            {
                if !callback_params.iter().any(|param| param.index == index) {
                    callback_params.push(HofCallbackParam {
                        index,
                        source_arity,
                    });
                }
                shapes[index] = Some(LocalValueShape::PureCallable {
                    arity: source_arity,
                });
            }
        }
        for callback in &callback_params {
            shapes[callback.index] = Some(LocalValueShape::PureCallable {
                arity: callback.source_arity,
            });
        }
        Some((shapes, callback_params))
    }

    fn cps_callback_params_called_in_body(&self, fb: &MFunBinding) -> Vec<HofCallbackParam> {
        let param_indices: HashMap<String, usize> = fb
            .params
            .iter()
            .enumerate()
            .filter_map(|(index, pat)| match pat {
                Pat::Var { name, .. } => Some((name.clone(), index)),
                _ => None,
            })
            .collect();
        let mut callbacks = HashMap::new();
        self.collect_cps_callback_param_calls(&fb.body, &param_indices, &mut callbacks);
        let mut callbacks: Vec<HofCallbackParam> = callbacks
            .into_iter()
            .map(|(index, source_arity)| HofCallbackParam {
                index,
                source_arity,
            })
            .collect();
        callbacks.sort_by_key(|param| param.index);
        callbacks
    }

    fn collect_cps_callback_param_calls(
        &self,
        expr: &MExpr,
        param_indices: &HashMap<String, usize>,
        callbacks: &mut HashMap<usize, usize>,
    ) {
        match expr {
            MExpr::App { head, args, .. } => {
                if let Atom::Var { name, source } = head
                    && let Some(index) = param_indices.get(&name.name)
                {
                    let source_arity = self
                        .cps_function_arity_at(*source)
                        .map(|(source_arity, _adapter_arity, _effects)| source_arity)
                        .unwrap_or(args.len());
                    callbacks.entry(*index).or_insert(source_arity);
                }
            }
            MExpr::Bind { value, body, .. } | MExpr::Let { value, body, .. } => {
                self.collect_cps_callback_param_calls(value, param_indices, callbacks);
                self.collect_cps_callback_param_calls(body, param_indices, callbacks);
            }
            MExpr::If {
                then_branch,
                else_branch,
                ..
            } => {
                self.collect_cps_callback_param_calls(then_branch, param_indices, callbacks);
                self.collect_cps_callback_param_calls(else_branch, param_indices, callbacks);
            }
            MExpr::Case { arms, .. } => {
                for arm in arms {
                    self.collect_cps_callback_param_calls(&arm.body, param_indices, callbacks);
                    if let Some(guard) = &arm.guard {
                        self.collect_cps_callback_param_calls(guard, param_indices, callbacks);
                    }
                }
            }
            MExpr::With { body, .. } => {
                self.collect_cps_callback_param_calls(body, param_indices, callbacks);
            }
            MExpr::Ensure { body, cleanup } => {
                self.collect_cps_callback_param_calls(body, param_indices, callbacks);
                self.collect_cps_callback_param_calls(cleanup, param_indices, callbacks);
            }
            MExpr::Pure(_)
            | MExpr::Yield { .. }
            | MExpr::Resume { .. }
            | MExpr::FieldAccess { .. }
            | MExpr::RecordUpdate { .. }
            | MExpr::DictMethodAccess { .. }
            | MExpr::ForeignCall { .. }
            | MExpr::BinOp { .. }
            | MExpr::UnaryMinus { .. }
            | MExpr::BitString { .. }
            | MExpr::Receive { .. }
            | MExpr::LetFun { .. }
            | MExpr::HandlerValue { .. } => {}
        }
    }
}

fn single_clause_function_names(program: &MProgram) -> HashSet<String> {
    let mut counts: HashMap<String, usize> = HashMap::new();
    for decl in program {
        if let MDecl::FunBinding(fb) = decl {
            *counts.entry(fb.name.clone()).or_default() += 1;
        }
    }
    counts
        .into_iter()
        .filter_map(|(name, count)| (count == 1).then_some(name))
        .collect()
}
