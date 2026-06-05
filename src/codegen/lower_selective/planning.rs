use super::*;

impl<'a, 'info> DirectLowerer<'a, 'info> {
    pub(super) fn imported_dict_constructors_for_module(
        &self,
        source_module_name: &str,
    ) -> HashMap<String, MDictConstructor> {
        if source_module_name.starts_with("Std.") {
            return HashMap::new();
        }
        let Some(source) = self.module_ctx.modules.get(source_module_name) else {
            return HashMap::new();
        };

        let mut imported_dict_constructors = HashMap::new();
        for (imported_module_name, compiled) in &self.module_ctx.modules {
            if imported_module_name == source_module_name
                || (!module_imports_module(&source.elaborated, imported_module_name)
                    && !resolution_references_source_module(
                        &source.resolution,
                        imported_module_name,
                    ))
            {
                continue;
            }

            let anf_imported = crate::codegen::anf::normalize(
                compiled.elaborated.clone(),
                Some(&compiled.resolution),
            );
            let (imported_monadic, _) = crate::codegen::monadic::translate::translate(
                &anf_imported,
                &compiled.resolution,
                self.effect_info,
            );
            let imported_private =
                super::imported_facts::collect_imported_private_helper_candidates(
                    imported_module_name,
                    &imported_monadic,
                    &compiled.resolution,
                    &compiled.codegen_info,
                );
            let imported_private_names = imported_private
                .values()
                .map(|binding| binding.name.clone())
                .collect::<HashSet<_>>();
            imported_dict_constructors.extend(
                super::imported_facts::collect_imported_dict_constructors(
                    imported_module_name,
                    &imported_monadic,
                    &compiled.resolution,
                    &compiled.codegen_info,
                    &imported_private_names,
                ),
            );
            crate::ast::drop_program_iterative(anf_imported);
        }
        imported_dict_constructors
    }

    pub(super) fn classify_program(&mut self, program: &MProgram) {
        self.callable_type_shapes.clear();
        self.callable_callback_param_arities.clear();
        self.local_fun_bindings.clear();
        self.local_fun_binding_counts.clear();
        self.direct_values.clear();
        self.function_plans.clear();
        self.local_dict_constructor_arities.clear();
        self.local_hof_direct_specializations.clear();
        self.local_dict_constructors.clear();
        self.local_external_functions.clear();
        self.direct_candidate_functions.clear();
        let signature_shapes = self.signature_function_shapes(program);
        for decl in program {
            match decl {
                MDecl::FunBinding(fb) => {
                    self.local_fun_bindings.insert(fb.name.clone(), fb.clone());
                    *self
                        .local_fun_binding_counts
                        .entry(fb.name.clone())
                        .or_default() += 1;
                    let function_type = self.function_type_for_binding(fb).cloned();
                    let shape = if is_native_variant_name(&fb.name) {
                        RuntimeFunctionShape::Pure
                    } else {
                        function_type
                            .as_ref()
                            .map(|ty| RuntimeFunctionShape::from_type(ty, |effects| effects))
                            .or_else(|| signature_shapes.get(&fb.name).cloned())
                            .unwrap_or_else(|| match self.effect_info.fun_effects.get(&fb.name) {
                                Some(effects) if effects.is_empty() => RuntimeFunctionShape::Pure,
                                Some(effects) => RuntimeFunctionShape::Cps(
                                    crate::codegen::runtime_shape::CpsShape {
                                        static_effects: effects.iter().cloned().collect(),
                                        is_open_row: false,
                                    },
                                ),
                                None => RuntimeFunctionShape::Cps(
                                    crate::codegen::runtime_shape::CpsShape {
                                        static_effects: vec![],
                                        is_open_row: true,
                                    },
                                ),
                            })
                    };
                    if let Some(ty) = function_type.as_ref() {
                        self.callable_callback_param_arities
                            .insert(fb.name.clone(), self.callback_param_arities_from_type(ty));
                    }
                    self.callable_type_shapes.insert(fb.name.clone(), shape);
                }
                MDecl::Val(v) => {
                    if self.expr_is_direct_subset(&v.value) {
                        self.direct_values.insert(v.name.clone());
                    }
                }
                MDecl::DictConstructor(dc) => {
                    self.local_dict_constructors
                        .insert(dc.name.clone(), dc.clone());
                    if self.can_lower_dict_constructor(dc) {
                        self.local_dict_constructor_arities
                            .insert(dc.name.clone(), dc.dict_params.len());
                    }
                }
                MDecl::Passthrough(crate::ast::Decl::FunSignature {
                    name,
                    params,
                    annotations,
                    ..
                }) => {
                    if let Some((target_erlang_mod, target_name)) =
                        crate::codegen::external::extract_external(annotations)
                    {
                        self.local_external_functions.insert(
                            name.clone(),
                            DirectCallable {
                                module: Some(target_erlang_mod),
                                name: target_name,
                                arity: params.len(),
                            },
                        );
                    }
                }
                MDecl::Passthrough(_) => {}
            }
        }
    }

    pub(super) fn compute_function_lowering_plans(&mut self, program: &MProgram) {
        self.compute_dict_constructor_plans(program);
        loop {
            let planned = self.function_plans.len();
            self.compute_direct_body_plans(program);
            self.compute_cps_body_plans(program);
            self.compute_direct_cps_island_body_plans(program);
            if self.function_plans.len() == planned {
                break;
            }
        }
        self.compute_hof_direct_specializations(program);
    }

    fn signature_function_shapes(
        &self,
        program: &MProgram,
    ) -> HashMap<String, RuntimeFunctionShape> {
        program
            .iter()
            .filter_map(|decl| {
                let MDecl::Passthrough(crate::ast::Decl::FunSignature {
                    name,
                    effects,
                    effect_row_var,
                    ..
                }) = decl
                else {
                    return None;
                };
                if effects.is_empty() && effect_row_var.is_none() {
                    return None;
                }
                let static_effects = self
                    .effect_info
                    .fun_effects
                    .get(name)
                    .map(|effects| effects.iter().cloned().collect())
                    .unwrap_or_else(|| effects.iter().map(|effect| effect.name.clone()).collect());
                Some((
                    name.clone(),
                    RuntimeFunctionShape::Cps(crate::codegen::runtime_shape::CpsShape {
                        static_effects,
                        is_open_row: effect_row_var.is_some(),
                    }),
                ))
            })
            .collect()
    }

    fn compute_dict_constructor_plans(&mut self, program: &MProgram) {
        self.local_dict_constructor_arities.clear();
        self.local_dict_constructors.clear();
        self.unsupported_local_dict_constructors.clear();
        for decl in program {
            let MDecl::DictConstructor(dc) = decl else {
                continue;
            };
            self.local_dict_constructors
                .insert(dc.name.clone(), dc.clone());
            if self.can_lower_dict_constructor(dc) {
                self.local_dict_constructor_arities
                    .insert(dc.name.clone(), dc.dict_params.len());
            } else {
                self.unsupported_local_dict_constructors
                    .insert(dc.name.clone());
            }
        }
    }

    fn compute_direct_body_plans(&mut self, program: &MProgram) {
        let groups = function_binding_groups(program);

        let mut changed = true;
        while changed {
            changed = false;
            for group in &groups {
                let name = &group[0].name;
                if self.function_plans.contains_key(name) {
                    continue;
                }
                if self.can_lower_fun_binding_group(group) {
                    self.function_plans
                        .insert(name.clone(), FunctionLoweringPlan::DirectBody);
                    changed = true;
                }
            }
        }

        let mut candidates: HashSet<String> = groups
            .iter()
            .filter_map(|group| {
                let name = &group[0].name;
                if self.function_plans.contains_key(name) {
                    return None;
                }
                matches!(
                    self.callable_type_shapes.get(name),
                    Some(RuntimeFunctionShape::Pure)
                )
                .then(|| name.clone())
            })
            .collect();

        while !candidates.is_empty() {
            let supported: HashSet<String> = groups
                .iter()
                .filter_map(|group| {
                    let name = &group[0].name;
                    if !candidates.contains(name) {
                        return None;
                    }
                    self.can_lower_fun_binding_group_with_candidates(group, &candidates)
                        .then(|| name.clone())
                })
                .collect();

            if supported == candidates {
                for name in supported {
                    self.function_plans
                        .insert(name, FunctionLoweringPlan::DirectBody);
                }
                break;
            }
            candidates = supported;
        }
    }

    fn can_lower_fun_binding_group(&mut self, group: &[&MFunBinding]) -> bool {
        group.iter().all(|fb| self.can_lower_fun_binding(fb))
    }

    fn can_lower_fun_binding_group_with_candidates(
        &mut self,
        group: &[&MFunBinding],
        candidates: &HashSet<String>,
    ) -> bool {
        let previous = std::mem::replace(&mut self.direct_candidate_functions, candidates.clone());
        let supported = self.can_lower_fun_binding_group(group);
        self.direct_candidate_functions = previous;
        supported
    }

    fn compute_cps_body_plans(&mut self, program: &MProgram) {
        for group in function_binding_groups(program) {
            let name = &group[0].name;
            if self.function_plans.contains_key(name) {
                continue;
            }
            if self.can_lower_cps_fun_binding_group(&group) {
                self.function_plans
                    .insert(name.clone(), FunctionLoweringPlan::CpsBody);
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
            if let Some(specialization) = self.hof_direct_specialization_for_fun_binding(fb) {
                self.local_hof_direct_specializations
                    .insert(fb.name.clone(), specialization);
            }
        }
    }

    fn compute_direct_cps_island_body_plans(&mut self, program: &MProgram) {
        let groups = function_binding_groups(program);
        for group in groups {
            let name = &group[0].name;
            if self.function_plans.contains_key(name) {
                continue;
            }
            if self.can_lower_direct_cps_island_fun_binding_group(&group) {
                self.function_plans
                    .insert(name.clone(), FunctionLoweringPlan::DirectBodyWithCpsIsland);
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
        self.imported_callback_param_arities.clear();
        self.imported_hof_direct_specializations.clear();
        for (source_module_name, compiled) in &self.module_ctx.modules {
            if source_module_name == &self.current_module
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
            let (monadic_imported, imported_handler_value_map) =
                crate::codegen::monadic::translate::translate_with_imports(
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
                &imported_handler_value_map,
                self.imported_dict_constructors_for_module(source_module_name),
                LoweringOptions::default(),
            );
            imported.current_module = source_module_name.clone();
            imported.classify_program(&monadic_imported);
            imported.compute_imported_direct_values();
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
            for (name, callback_arities) in imported.callable_callback_param_arities {
                self.imported_callback_param_arities.insert(
                    (erlang_module.clone(), name.clone()),
                    callback_arities.clone(),
                );
                self.imported_callback_param_arities
                    .insert((source_module_name.clone(), name), callback_arities);
            }
        }
    }

    pub(super) fn compute_imported_direct_values(&mut self) {
        self.imported_direct_values.clear();
        if self.current_module.starts_with("Std.") {
            debug_selective_subject("imported-value", &self.current_module, || {
                format!(
                    "{}: skip imported public value scan while compiling stdlib",
                    self.current_module
                )
            });
            return;
        }
        let mut visited = HashSet::new();
        visited.insert(self.current_module.clone());
        self.compute_imported_direct_values_transitive(&mut visited);
    }

    fn compute_imported_direct_values_transitive(&mut self, visited: &mut HashSet<String>) {
        for (source_module_name, compiled) in &self.module_ctx.modules {
            let skip_reason = if source_module_name == &self.current_module {
                Some("current module")
            } else if compiled.elaborated.is_empty() {
                Some("empty elaborated program")
            } else if !self.current_module_references_module(source_module_name) {
                Some("not referenced by current module")
            } else {
                None
            };
            if let Some(reason) = skip_reason {
                debug_selective_subject("imported-value", source_module_name, || {
                    format!(
                        "{}: skip module {source_module_name}: {reason}",
                        self.current_module
                    )
                });
                continue;
            }
            if !visited.insert(source_module_name.clone()) {
                debug_selective_subject("imported-value", source_module_name, || {
                    format!(
                        "{}: skip module {source_module_name}: already scanned in imported-value traversal",
                        self.current_module
                    )
                });
                continue;
            }
            debug_selective_subject("imported-value", source_module_name, || {
                format!("{}: scan module {source_module_name}", self.current_module)
            });

            let anf_imported = crate::codegen::anf::normalize(
                compiled.elaborated.clone(),
                Some(&compiled.resolution),
            );
            let imported_handler_decls = HashMap::new();
            let (monadic_imported, imported_handler_value_map) =
                crate::codegen::monadic::translate::translate_with_imports(
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
                &imported_handler_value_map,
                HashMap::new(),
                LoweringOptions::default(),
            );
            imported.current_module = source_module_name.clone();
            imported.classify_program(&monadic_imported);
            imported.compute_imported_direct_values_transitive(visited);
            self.merge_imported_direct_values_from(
                source_module_name,
                &imported.imported_direct_values,
            );

            let erlang_module = erlang_module_name(source_module_name);
            for decl in &monadic_imported {
                let MDecl::Val(value) = decl else {
                    continue;
                };
                let subject = format!("{source_module_name}.{}", value.name);
                if !value.public {
                    debug_selective_subject("imported-value", &subject, || {
                        format!(
                            "{}: skip {subject}: value is not public",
                            self.current_module
                        )
                    });
                    continue;
                }
                if !imported.direct_values.contains(&value.name) {
                    debug_selective_subject("imported-value", &subject, || {
                        format!(
                            "{}: skip {subject}: value is outside direct val subset",
                            self.current_module
                        )
                    });
                    continue;
                }
                let MExpr::Pure(atom) = &value.value else {
                    debug_selective_subject("imported-value", &subject, || {
                        format!(
                            "{}: skip {subject}: value is {} instead of pure atom",
                            self.current_module,
                            mexpr_debug_label(&value.value)
                        )
                    });
                    continue;
                };
                debug_selective_subject("imported-value", &subject, || {
                    format!(
                        "{}: collect {subject}: {}",
                        self.current_module,
                        atom_debug_label(atom)
                    )
                });
                self.imported_direct_values.insert(
                    (source_module_name.clone(), value.name.clone()),
                    atom.clone(),
                );
                self.imported_direct_values
                    .insert((erlang_module.clone(), value.name.clone()), atom.clone());
            }
        }
    }

    fn merge_imported_direct_values_from(
        &mut self,
        via_module_name: &str,
        values: &HashMap<(String, String), Atom>,
    ) {
        for ((module, name), atom) in values {
            debug_selective_subject("imported-value", &format!("{module}.{name}"), || {
                format!(
                    "{}: import transitive {module}.{name} via {via_module_name}: {}",
                    self.current_module,
                    atom_debug_label(atom)
                )
            });
            self.imported_direct_values
                .insert((module.clone(), name.clone()), atom.clone());
        }
    }

    fn current_module_references_module(&self, source_module_name: &str) -> bool {
        if let Some(current) = self.module_ctx.modules.get(&self.current_module) {
            return module_imports_module(&current.elaborated, source_module_name)
                || resolution_references_source_module(&current.resolution, source_module_name);
        }

        resolution_references_source_module(self.resolution, source_module_name)
    }

    pub(super) fn apply_codegen_info_function_shapes(
        &mut self,
        info: &crate::typechecker::ModuleCodegenInfo,
    ) {
        for (name, scheme) in &info.exports {
            self.callable_callback_param_arities.insert(
                name.clone(),
                self.callback_param_arities_from_type(&scheme.ty),
            );
            self.callable_type_shapes.insert(
                name.clone(),
                RuntimeFunctionShape::from_type(&scheme.ty, |effects| effects),
            );
        }
        for (name, effects) in &info.fun_effects {
            let shape = if effects.is_empty() {
                if matches!(
                    self.callable_type_shapes.get(name),
                    Some(RuntimeFunctionShape::Cps(_))
                ) {
                    continue;
                }
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
        if !dc.dict_params.is_empty()
            && !dc.name.contains("_Std_Generic_")
            && dict_constructor_mentions_generic_rep_traversal(dc)
        {
            debug_selective_subject("dict-plan", &dc.name, || {
                format!(
                    "reject {}: parameterized user Generic traversal bridge",
                    dc.name
                )
            });
            return false;
        }
        self.push_scope();
        for dict_param in &dc.dict_params {
            self.current_scope_mut().insert(dict_param.clone());
        }
        let mut supported = true;
        for (index, method) in dc.methods.iter().enumerate() {
            let effectful = dc
                .method_effects
                .get(index)
                .is_some_and(|effects| !effects.is_empty())
                || dc.method_open_rows.get(index).copied().unwrap_or(false);

            let MExpr::Pure(Atom::Lambda { params, body, .. }) = method else {
                let direct = !effectful && self.expr_is_direct_subset(method);
                if !direct {
                    debug_selective_subject("dict-plan", &dc.name, || {
                        format!(
                            "reject {} method {index}: non-lambda method is not direct subset",
                            dc.name
                        )
                    });
                    supported = false;
                    break;
                }
                continue;
            };
            if params.iter().any(|p| !direct_param_supported(p)) {
                debug_selective_subject("dict-plan", &dc.name, || {
                    format!(
                        "reject {} method {index}: unsupported method parameter pattern",
                        dc.name
                    )
                });
                supported = false;
                break;
            }

            self.push_scope();
            for pat in params {
                self.bind_pat_locals(pat);
            }
            let method_supported = if effectful {
                self.expr_is_cps_island_subset(body) || self.expr_is_direct_subset(body)
            } else {
                self.expr_is_direct_subset(body)
            };
            self.pop_scope();
            if !method_supported {
                debug_selective_subject("dict-plan", &dc.name, || {
                    let shape = if effectful { "cps/direct" } else { "direct" };
                    format!(
                        "reject {} method {index}: body is outside {shape} subset",
                        dc.name
                    )
                });
                supported = false;
                break;
            }
        }
        self.pop_scope();
        if supported {
            debug_selective_subject("dict-plan", &dc.name, || format!("accept {}", dc.name));
        }
        supported
    }

    fn can_lower_fun_binding(&mut self, fb: &MFunBinding) -> bool {
        if fb.params.iter().any(|p| !direct_param_supported(p)) {
            return false;
        }
        let prev_direct_candidate = self.direct_candidate_function.replace(fb.name.clone());
        self.push_scope();
        self.bind_fun_param_locals(fb);
        let supported = fb
            .guard
            .as_ref()
            .is_none_or(|guard| self.expr_is_direct_subset(guard))
            && self.expr_is_direct_subset(&fb.body);
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

        let prev_direct_candidate = self.direct_candidate_function.replace(fb.name.clone());
        self.push_scope();
        self.bind_cps_entry_param_locals(fb);
        let supported = self.expr_is_cps_island_subset(&fb.body);
        self.pop_scope();
        self.direct_candidate_function = prev_direct_candidate;
        supported
    }

    fn can_lower_cps_fun_binding_group(&mut self, group: &[&MFunBinding]) -> bool {
        group.iter().all(|fb| self.can_lower_cps_fun_binding(fb))
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

        let prev_direct_candidate = self.direct_candidate_function.replace(fb.name.clone());
        self.push_scope();
        self.bind_fun_param_locals(fb);
        let supported = self.expr_is_cps_island_subset(&fb.body);
        self.pop_scope();
        self.direct_candidate_function = prev_direct_candidate;
        supported
    }

    fn can_lower_direct_cps_island_fun_binding_group(&mut self, group: &[&MFunBinding]) -> bool {
        group
            .iter()
            .all(|fb| self.can_lower_direct_cps_island_fun_binding(fb))
    }

    fn hof_direct_specialization_for_fun_binding(
        &mut self,
        fb: &MFunBinding,
    ) -> Option<HofDirectSpecialization> {
        if fb.guard.is_some() || fb.params.iter().any(|p| !direct_param_supported(p)) {
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
        if let Some(callback_arities) = self.callable_callback_param_arities.get(&fb.name) {
            for (index, source_arity) in callback_arities.iter().enumerate() {
                let Some(source_arity) = source_arity else {
                    continue;
                };
                if index >= fb.params.len() {
                    continue;
                }
                if !callback_params.iter().any(|param| param.index == index) {
                    callback_params.push(HofCallbackParam {
                        index,
                        source_arity: *source_arity,
                    });
                }
                shapes[index] = Some(LocalValueShape::PureCallable {
                    arity: *source_arity,
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

    pub(super) fn cps_callback_params_called_in_body(
        &self,
        fb: &MFunBinding,
    ) -> Vec<HofCallbackParam> {
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

    pub(super) fn collect_cps_callback_param_calls(
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

fn module_imports_module(program: &crate::ast::Program, module_name: &str) -> bool {
    program.iter().any(|decl| {
        matches!(
            decl,
            crate::ast::Decl::Import { module_path, .. }
                if module_path.join(".") == module_name
        )
    })
}

fn resolution_references_source_module(
    resolution: &ResolutionMap,
    source_module_name: &str,
) -> bool {
    let erlang_module = erlang_module_name(source_module_name);
    resolution.values().any(|resolved| {
        resolved.source_module.as_deref() == Some(source_module_name)
            || matches!(
                &resolved.kind,
                ResolvedCodegenKind::BeamFunction {
                    erlang_mod: Some(module),
                    ..
                } if module == &erlang_module
            )
    })
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

fn dict_constructor_mentions_generic_rep_traversal(dc: &MDictConstructor) -> bool {
    generic_rep_traversal_name(&dc.name)
        || dc.methods.iter().any(expr_mentions_generic_rep_traversal)
}

fn expr_mentions_generic_rep_traversal(expr: &MExpr) -> bool {
    match expr {
        MExpr::Pure(atom) => atom_mentions_generic_rep_traversal(atom),
        MExpr::App { head, args, .. } => {
            atom_mentions_generic_rep_traversal(head)
                || args.iter().any(atom_mentions_generic_rep_traversal)
        }
        MExpr::Bind { value, body, .. } | MExpr::Let { value, body, .. } => {
            expr_mentions_generic_rep_traversal(value) || expr_mentions_generic_rep_traversal(body)
        }
        MExpr::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            atom_mentions_generic_rep_traversal(cond)
                || expr_mentions_generic_rep_traversal(then_branch)
                || expr_mentions_generic_rep_traversal(else_branch)
        }
        MExpr::Case {
            scrutinee, arms, ..
        } => {
            atom_mentions_generic_rep_traversal(scrutinee)
                || arms.iter().any(|arm| {
                    arm.guard
                        .as_ref()
                        .is_some_and(expr_mentions_generic_rep_traversal)
                        || expr_mentions_generic_rep_traversal(&arm.body)
                })
        }
        MExpr::With { handler, body, .. } => {
            handler_mentions_generic_rep_traversal(handler)
                || expr_mentions_generic_rep_traversal(body)
        }
        MExpr::Ensure { body, cleanup } => {
            expr_mentions_generic_rep_traversal(body)
                || expr_mentions_generic_rep_traversal(cleanup)
        }
        MExpr::Yield { args, .. } | MExpr::ForeignCall { args, .. } => {
            args.iter().any(atom_mentions_generic_rep_traversal)
        }
        MExpr::Resume { value, .. }
        | MExpr::FieldAccess { record: value, .. }
        | MExpr::UnaryMinus { value, .. }
        | MExpr::DictMethodAccess { dict: value, .. } => atom_mentions_generic_rep_traversal(value),
        MExpr::RecordUpdate { record, fields, .. } => {
            atom_mentions_generic_rep_traversal(record)
                || fields
                    .iter()
                    .any(|(_, atom)| atom_mentions_generic_rep_traversal(atom))
        }
        MExpr::BinOp { left, right, .. } => {
            atom_mentions_generic_rep_traversal(left) || atom_mentions_generic_rep_traversal(right)
        }
        MExpr::BitString { segments, .. } => segments
            .iter()
            .any(|segment| atom_mentions_generic_rep_traversal(&segment.value)),
        MExpr::Receive { arms, after, .. } => {
            arms.iter().any(|arm| {
                arm.guard
                    .as_ref()
                    .is_some_and(expr_mentions_generic_rep_traversal)
                    || expr_mentions_generic_rep_traversal(&arm.body)
            }) || after.as_ref().is_some_and(|(timeout, body)| {
                atom_mentions_generic_rep_traversal(timeout)
                    || expr_mentions_generic_rep_traversal(body)
            })
        }
        MExpr::LetFun { body, rest, .. } => {
            expr_mentions_generic_rep_traversal(body) || expr_mentions_generic_rep_traversal(rest)
        }
        MExpr::HandlerValue {
            arms,
            return_clause,
            ..
        } => {
            arms.iter().any(handler_arm_mentions_generic_rep_traversal)
                || return_clause
                    .as_ref()
                    .is_some_and(|arm| handler_arm_mentions_generic_rep_traversal(arm))
        }
    }
}

fn handler_mentions_generic_rep_traversal(handler: &MHandler) -> bool {
    match handler {
        MHandler::Static {
            arms,
            return_clause,
            ..
        } => {
            arms.iter().any(handler_arm_mentions_generic_rep_traversal)
                || return_clause
                    .as_ref()
                    .is_some_and(handler_arm_mentions_generic_rep_traversal)
        }
        MHandler::Composite { handlers, .. } => {
            handlers.iter().any(handler_mentions_generic_rep_traversal)
        }
        MHandler::Dynamic {
            op_tuple,
            return_lambda,
            ..
        } => {
            atom_mentions_generic_rep_traversal(op_tuple)
                || return_lambda
                    .as_ref()
                    .is_some_and(atom_mentions_generic_rep_traversal)
        }
        MHandler::Native { .. } => false,
    }
}

fn handler_arm_mentions_generic_rep_traversal(arm: &MHandlerArm) -> bool {
    expr_mentions_generic_rep_traversal(&arm.body)
        || arm
            .finally_block
            .as_ref()
            .is_some_and(|expr| expr_mentions_generic_rep_traversal(expr))
}

fn atom_mentions_generic_rep_traversal(atom: &Atom) -> bool {
    match atom {
        Atom::Var { .. } | Atom::Lit { .. } | Atom::Symbol { .. } | Atom::BackendAtom { .. } => {
            false
        }
        Atom::Ctor { name, args, .. } => {
            generic_rep_traversal_name(name) || args.iter().any(atom_mentions_generic_rep_traversal)
        }
        Atom::Tuple { elements, .. } => elements.iter().any(atom_mentions_generic_rep_traversal),
        Atom::AnonRecord { fields, .. } | Atom::Record { fields, .. } => fields
            .iter()
            .any(|(_, atom)| atom_mentions_generic_rep_traversal(atom)),
        Atom::Lambda { body, .. } => expr_mentions_generic_rep_traversal(body),
        Atom::DictRef { name, .. } => generic_rep_traversal_name(name),
        Atom::QualifiedRef { module, name, .. } => {
            generic_rep_traversal_name(module) || generic_rep_traversal_name(name)
        }
        Atom::BackendSpawnThunk { callback, .. } => atom_mentions_generic_rep_traversal(callback),
    }
}

fn generic_rep_traversal_name(name: &str) -> bool {
    name.contains("Std_Generic")
        || name.contains("Std.Generic")
        || name.contains("std_generic")
        || name.contains("_Rep__")
}

fn is_native_variant_name(name: &str) -> bool {
    name.starts_with("__saga_native_variant__")
}

fn function_binding_groups(program: &MProgram) -> Vec<Vec<&MFunBinding>> {
    let mut groups = Vec::new();
    let mut index = 0;
    while index < program.len() {
        let MDecl::FunBinding(first) = &program[index] else {
            index += 1;
            continue;
        };
        let mut group = vec![first];
        let mut next_index = index + 1;
        while next_index < program.len() {
            let MDecl::FunBinding(next) = &program[next_index] else {
                break;
            };
            if next.name != first.name {
                break;
            }
            group.push(next);
            next_index += 1;
        }
        groups.push(group);
        index = next_index;
    }
    groups
}
