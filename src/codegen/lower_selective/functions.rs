use super::*;

impl<'a, 'info> DirectLowerer<'a, 'info> {
    #[allow(clippy::too_many_arguments)]
    pub(super) fn new(
        resolution: &'a ResolutionMap,
        ctors: &'a ConstructorAtoms,
        module_ctx: &'a CodegenContext,
        handler_info: &'a HandlerAnalysis,
        effect_info: &'a EffectInfo<'info>,
        handler_value_map: &'a HandlerValueMap,
        imported_dict_constructors: HashMap<String, MDictConstructor>,
        options: LoweringOptions,
    ) -> Self {
        Self {
            resolution,
            ctors,
            module_ctx,
            handler_info,
            effect_info,
            handler_value_map,
            current_module: String::new(),
            callable_type_shapes: HashMap::new(),
            callable_callback_param_arities: HashMap::new(),
            local_fun_bindings: HashMap::new(),
            direct_values: HashSet::new(),
            function_plans: HashMap::new(),
            local_function_entries: HashMap::new(),
            local_dict_constructor_arities: HashMap::new(),
            local_hof_direct_specializations: HashMap::new(),
            local_dict_constructors: HashMap::new(),
            imported_dict_constructors,
            local_external_functions: HashMap::new(),
            imported_function_entries: HashMap::new(),
            imported_hof_direct_specializations: HashMap::new(),
            direct_candidate_function: None,
            direct_candidate_functions: HashSet::new(),
            static_handler_inline_stack: Vec::new(),
            direct_handler_stack: Vec::new(),
            result_delimiter_stack: Vec::new(),
            cps_temp_counter: 0,
            locals: vec![HashSet::new()],
            local_shapes: vec![HashMap::new()],
            local_known_direct_lambdas: vec![HashMap::new()],
            local_known_cps_lambdas: vec![HashMap::new()],
            local_known_dict_values: vec![HashMap::new()],
            local_known_direct_atoms: vec![HashMap::new()],
            local_known_direct_values: vec![HashMap::new()],
            active_known_dict_methods: HashSet::new(),
            imported_clone_source_module: None,
            options,
        }
    }

    pub(super) fn lower_module(
        &mut self,
        module_name: &str,
        program: &MProgram,
        entry_export: Option<&str>,
    ) -> CModule {
        self.current_module = module_name.to_string();
        self.classify_program(program);
        self.compute_imported_function_entries();
        self.compute_function_lowering_plans(program);
        self.compute_local_function_entries(program);

        let pub_names: Option<HashSet<String>> =
            self.module_ctx.modules.get(module_name).map(|m| {
                m.codegen_info
                    .exports
                    .iter()
                    .map(|(n, _)| n.clone())
                    .collect()
            });
        let is_public =
            |name: &str| -> bool { pub_names.as_ref().is_none_or(|s| s.contains(name)) };
        let is_entry = |name: &str| -> bool { entry_export.is_some_and(|entry| entry == name) };
        let exported_dict_names: HashSet<String> = self
            .module_ctx
            .modules
            .get(module_name)
            .map(|m| {
                m.codegen_info
                    .trait_impl_dicts
                    .iter()
                    .map(|dict| dict.dict_name.clone())
                    .collect()
            })
            .unwrap_or_default();
        let is_exported_dict = |name: &str| -> bool {
            exported_dict_names.is_empty() || exported_dict_names.contains(name)
        };

        if self.options.require_all_functions {
            self.assert_no_unlowered_direct_body_functions(program);
            self.assert_no_unlowered_public_cps_functions(program, &is_public, &is_entry);
            self.assert_all_declarations_have_selective_plans(program);
        }

        let mut exports = Vec::new();
        let mut funs = Vec::new();
        let native_variant_frames = self.native_variant_frames_in_program(program);
        let mut index = 0;
        while index < program.len() {
            match &program[index] {
                MDecl::FunBinding(fb) => {
                    let mut group = vec![fb];
                    let mut next_index = index + 1;
                    while next_index < program.len() {
                        let MDecl::FunBinding(next) = &program[next_index] else {
                            break;
                        };
                        if next.name != fb.name {
                            break;
                        }
                        group.push(next);
                        next_index += 1;
                    }

                    let Some(plan) = self.function_plans.get(&fb.name).copied() else {
                        index = next_index;
                        continue;
                    };
                    if fb.public || is_public(&fb.name) || is_entry(&fb.name) {
                        exports.extend(self.export_entries(&fb.name));
                    }
                    match plan {
                        FunctionLoweringPlan::DirectBody => {
                            funs.push(self.lower_direct_fun_binding_group(&group));
                            if self.needs_cps_adapter(&fb.name) {
                                funs.push(self.lower_cps_adapter_for(fb));
                            }
                        }
                        FunctionLoweringPlan::DirectBodyWithCpsIsland => {
                            funs.push(self.lower_direct_cps_island_fun_binding_group(&group));
                        }
                        FunctionLoweringPlan::CpsBody => {
                            funs.push(self.lower_cps_fun_binding_group(&group));
                            for frame in &native_variant_frames {
                                if let Some(variant_name) =
                                    self.native_variant_name_for_function(&fb.name, frame)
                                {
                                    funs.push(self.lower_cps_fun_binding_group_native_variant(
                                        &group,
                                        &variant_name,
                                        frame.clone(),
                                    ));
                                }
                            }
                        }
                    }
                    if group.len() == 1
                        && let Some(specialization) =
                            self.local_hof_direct_specializations.get(&fb.name).cloned()
                    {
                        if fb.public || is_public(&fb.name) || is_entry(&fb.name) {
                            exports.push((
                                specialization.entry_name.clone(),
                                specialization.source_arity,
                            ));
                        }
                        funs.push(
                            self.lower_hof_direct_specialized_fun_binding(fb, &specialization),
                        );
                    }
                    index = next_index;
                }
                MDecl::Val(v) => {
                    if !self.direct_values.contains(&v.name) {
                        index += 1;
                        continue;
                    }
                    if v.public {
                        exports.push((v.name.clone(), 0));
                    }
                    let body = self.lower_expr(&v.value);
                    funs.push(CFunDef {
                        name: v.name.clone(),
                        arity: 0,
                        body: CExpr::Fun(vec![], Box::new(body)),
                    });
                    index += 1;
                }
                MDecl::DictConstructor(dc) => {
                    if self.local_dict_constructor_arities.contains_key(&dc.name) {
                        if is_exported_dict(&dc.name) {
                            exports.push((dc.name.clone(), dc.dict_params.len()));
                        }
                        funs.push(self.lower_dict_constructor(dc));
                    }
                    index += 1;
                }
                MDecl::Passthrough(_) => {
                    index += 1;
                }
            }
        }

        CModule {
            name: module_name.to_string(),
            exports,
            funs,
        }
    }

    pub(super) fn lower_fun_binding(&mut self, fb: &MFunBinding) -> CFunDef {
        let params = lower_param_names(&fb.params);
        let pushed_native_frame = self.push_native_variant_frame_for_name(&fb.name);
        self.push_scope();
        self.bind_fun_param_locals(fb);
        let lowered_body = self.lower_expr(&fb.body);
        let body = self.wrap_param_match(&fb.params, &params, lowered_body);
        self.pop_scope();
        if pushed_native_frame {
            self.direct_handler_stack.pop();
        }
        CFunDef {
            name: self.direct_entry_name(&fb.name),
            arity: params.len(),
            body: CExpr::Fun(params, Box::new(body)),
        }
    }

    pub(super) fn lower_direct_fun_binding_group(&mut self, group: &[&MFunBinding]) -> CFunDef {
        assert!(
            !group.is_empty(),
            "lower_direct_fun_binding_group: empty group is impossible"
        );
        if group.len() == 1 && group[0].guard.is_none() {
            return self.lower_fun_binding(group[0]);
        }

        let name = &group[0].name;
        let source_arity = group[0].params.len();
        for fb in group {
            assert_eq!(
                fb.params.len(),
                source_arity,
                "lower_direct_fun_binding_group: clause arity mismatch for '{}'",
                name
            );
        }

        let params: Vec<String> = (0..source_arity)
            .map(|arg_index| format!("_Arg{arg_index}"))
            .collect();
        let scrutinee = CExpr::Tuple(params.iter().cloned().map(CExpr::Var).collect());
        let scrut_var = self.fresh_cps_temp("_FunScrut");
        let mut rest = self.case_clause_error();

        let pushed_native_frame = self.push_native_variant_frame_for_name(name);
        for fb in group.iter().rev() {
            let rest_var = self.fresh_cps_temp("_FunRest");
            let rest_ref = || CExpr::Apply(Box::new(CExpr::Var(rest_var.clone())), vec![]);
            self.push_scope();
            self.bind_fun_param_locals(fb);
            let body = self.lower_expr(&fb.body);
            let body = match fb.guard.as_ref() {
                Some(guard) => CExpr::Case(
                    Box::new(self.lower_expr(guard)),
                    vec![
                        CArm {
                            pat: CPat::Lit(CLit::Atom("true".to_string())),
                            guard: None,
                            body,
                        },
                        CArm {
                            pat: CPat::Wildcard,
                            guard: None,
                            body: rest_ref(),
                        },
                    ],
                ),
                None => body,
            };
            let pat = CPat::Tuple(fb.params.iter().map(|pat| self.lower_pat(pat)).collect());
            self.pop_scope();
            let current = CExpr::Case(
                Box::new(CExpr::Var(scrut_var.clone())),
                vec![
                    CArm {
                        pat,
                        guard: None,
                        body,
                    },
                    CArm {
                        pat: CPat::Wildcard,
                        guard: None,
                        body: rest_ref(),
                    },
                ],
            );
            rest = CExpr::Let(
                rest_var,
                Box::new(CExpr::Fun(vec![], Box::new(rest))),
                Box::new(current),
            );
        }
        if pushed_native_frame {
            self.direct_handler_stack.pop();
        }

        let body = CExpr::Let(scrut_var, Box::new(scrutinee), Box::new(rest));
        CFunDef {
            name: self.direct_entry_name(name),
            arity: params.len(),
            body: CExpr::Fun(params, Box::new(body)),
        }
    }

    pub(super) fn lower_hof_direct_specialized_fun_binding(
        &mut self,
        fb: &MFunBinding,
        specialization: &HofDirectSpecialization,
    ) -> CFunDef {
        let params = lower_param_names(&fb.params);
        let (param_shapes, _callback_params) = self
            .hof_direct_specialized_param_shapes(fb)
            .unwrap_or_else(|| (vec![None; fb.params.len()], Vec::new()));
        self.push_scope();
        for (index, pat) in fb.params.iter().enumerate() {
            self.bind_pat_locals_with_shape(pat, param_shapes.get(index).cloned().flatten());
        }
        let lowered_body = self.lower_expr(&fb.body);
        let body = self.wrap_param_match(&fb.params, &params, lowered_body);
        self.pop_scope();
        CFunDef {
            name: specialization.entry_name.clone(),
            arity: params.len(),
            body: CExpr::Fun(params, Box::new(body)),
        }
    }

    pub(super) fn lower_cps_adapter_for(&self, fb: &MFunBinding) -> CFunDef {
        let direct_params = lower_param_names(&fb.params);
        let mut params = direct_params.clone();
        params.push("_Evidence".to_string());
        params.push("_ReturnK".to_string());
        let direct_call_args = self.cps_adapter_direct_call_args(fb, &direct_params);
        let direct_call = CExpr::Apply(
            Box::new(CExpr::FunRef(
                self.direct_entry_name(&fb.name),
                direct_params.len(),
            )),
            direct_call_args,
        );
        let body = CExpr::Apply(
            Box::new(CExpr::Var("_ReturnK".to_string())),
            vec![direct_call],
        );
        CFunDef {
            name: fb.name.clone(),
            arity: params.len(),
            body: CExpr::Fun(params, Box::new(body)),
        }
    }

    pub(super) fn cps_adapter_direct_call_args(
        &self,
        fb: &MFunBinding,
        direct_params: &[String],
    ) -> Vec<CExpr> {
        let param_shapes = self.param_shapes_for_fun(fb);
        direct_params
            .iter()
            .enumerate()
            .map(
                |(index, name)| match param_shapes.get(index).and_then(|shape| shape.as_ref()) {
                    Some(LocalValueShape::PureCallableFromUseType) => {
                        let arity = self
                            .pure_callable_param_arity(fb, index)
                            .expect("pure callable param shape must have an arity");
                        self.cps_param_to_direct_closure(name, arity, index)
                    }
                    Some(LocalValueShape::PureCallable { arity }) => {
                        self.cps_param_to_direct_closure(name, *arity, index)
                    }
                    _ => CExpr::Var(name.clone()),
                },
            )
            .collect()
    }

    pub(super) fn pure_callable_param_arity(
        &self,
        fb: &MFunBinding,
        index: usize,
    ) -> Option<usize> {
        let mut current = self.effect_info.type_at_node.get(&fb.id)?;
        for current_index in 0..=index {
            let Type::Fun(param, ret, _) = current else {
                return None;
            };
            if current_index == index {
                return self.pure_function_arity_from_type(param);
            }
            current = ret;
        }
        None
    }

    pub(super) fn cps_param_to_direct_closure(
        &self,
        param_name: &str,
        arity: usize,
        index: usize,
    ) -> CExpr {
        let arg_names: Vec<String> = (0..arity)
            .map(|arg_index| format!("_CpsAdapterArg{index}_{arg_index}"))
            .collect();
        let k_name = format!("_CpsAdapterK{index}");
        let k_arg = format!("_CpsAdapterV{index}");
        let mut cps_args: Vec<CExpr> = arg_names.iter().cloned().map(CExpr::Var).collect();
        cps_args.push(CExpr::Var("_Evidence".to_string()));
        cps_args.push(CExpr::Var(k_name.clone()));
        let apply_cps = CExpr::Apply(Box::new(CExpr::Var(param_name.to_string())), cps_args);
        let identity_k = CExpr::Fun(vec![k_arg.clone()], Box::new(CExpr::Var(k_arg)));
        CExpr::Fun(
            arg_names,
            Box::new(CExpr::Let(
                k_name,
                Box::new(identity_k),
                Box::new(apply_cps),
            )),
        )
    }

    pub(super) fn lower_direct_cps_island_fun_binding(&mut self, fb: &MFunBinding) -> CFunDef {
        let params = lower_param_names(&fb.params);

        let prev_direct_candidate = self.direct_candidate_function.replace(fb.name.clone());
        let pushed_native_frame = self.push_native_variant_frame_for_name(&fb.name);
        self.push_scope();
        self.bind_fun_param_locals(fb);
        let return_k = self.identity_cps_continuation();
        let lowered_body = self.lower_cps_expr(&fb.body, CExpr::Tuple(vec![]), return_k);
        let body = self.wrap_param_match(&fb.params, &params, lowered_body);
        self.pop_scope();
        if pushed_native_frame {
            self.direct_handler_stack.pop();
        }
        self.direct_candidate_function = prev_direct_candidate;

        CFunDef {
            name: self.direct_entry_name(&fb.name),
            arity: params.len(),
            body: CExpr::Fun(params, Box::new(body)),
        }
    }

    pub(super) fn lower_direct_cps_island_fun_binding_group(
        &mut self,
        group: &[&MFunBinding],
    ) -> CFunDef {
        assert!(
            !group.is_empty(),
            "lower_direct_cps_island_fun_binding_group: empty group is impossible"
        );
        if group.len() == 1 && group[0].guard.is_none() {
            return self.lower_direct_cps_island_fun_binding(group[0]);
        }

        let name = &group[0].name;
        let source_arity = group[0].params.len();
        for fb in group {
            assert_eq!(
                fb.params.len(),
                source_arity,
                "lower_direct_cps_island_fun_binding_group: clause arity mismatch for '{}'",
                name
            );
        }

        let params: Vec<String> = (0..source_arity)
            .map(|arg_index| format!("_Arg{arg_index}"))
            .collect();
        let scrutinee = CExpr::Tuple(params.iter().cloned().map(CExpr::Var).collect());
        let scrut_var = self.fresh_cps_temp("_FunScrut");
        let mut rest = self.case_clause_error();

        let prev_direct_candidate = self.direct_candidate_function.replace(name.clone());
        let pushed_native_frame = self.push_native_variant_frame_for_name(name);
        for fb in group.iter().rev() {
            let rest_var = self.fresh_cps_temp("_FunRest");
            let rest_ref = || CExpr::Apply(Box::new(CExpr::Var(rest_var.clone())), vec![]);
            self.push_scope();
            self.bind_fun_param_locals(fb);
            let return_k = self.identity_cps_continuation();
            let body = self.lower_cps_expr(&fb.body, CExpr::Tuple(vec![]), return_k);
            let body = match fb.guard.as_ref() {
                Some(guard) => CExpr::Case(
                    Box::new(self.lower_expr(guard)),
                    vec![
                        CArm {
                            pat: CPat::Lit(CLit::Atom("true".to_string())),
                            guard: None,
                            body,
                        },
                        CArm {
                            pat: CPat::Wildcard,
                            guard: None,
                            body: rest_ref(),
                        },
                    ],
                ),
                None => body,
            };
            let pat = CPat::Tuple(fb.params.iter().map(|pat| self.lower_pat(pat)).collect());
            self.pop_scope();
            let current = CExpr::Case(
                Box::new(CExpr::Var(scrut_var.clone())),
                vec![
                    CArm {
                        pat,
                        guard: None,
                        body,
                    },
                    CArm {
                        pat: CPat::Wildcard,
                        guard: None,
                        body: rest_ref(),
                    },
                ],
            );
            rest = CExpr::Let(
                rest_var,
                Box::new(CExpr::Fun(vec![], Box::new(rest))),
                Box::new(current),
            );
        }
        if pushed_native_frame {
            self.direct_handler_stack.pop();
        }
        self.direct_candidate_function = prev_direct_candidate;

        let body = CExpr::Let(scrut_var, Box::new(scrutinee), Box::new(rest));
        CFunDef {
            name: self.direct_entry_name(name),
            arity: params.len(),
            body: CExpr::Fun(params, Box::new(body)),
        }
    }

    pub(super) fn identity_cps_continuation(&mut self) -> CExpr {
        let result = self.fresh_cps_temp("_CpsResult");
        CExpr::Fun(vec![result.clone()], Box::new(CExpr::Var(result)))
    }

    pub(super) fn lower_cps_fun_binding_named(
        &mut self,
        fb: &MFunBinding,
        output_name: &str,
        native_frame: Option<DirectHandlerFrame>,
    ) -> CFunDef {
        let direct_params = lower_param_names(&fb.params);
        let mut params = direct_params.clone();
        params.push("_Evidence".to_string());
        params.push("_ReturnK".to_string());

        let pushed_native_frame = self.push_native_variant_frame(output_name, native_frame);
        self.push_scope();
        self.bind_cps_entry_param_locals(fb);
        let lowered_body = self.lower_cps_expr(
            &fb.body,
            CExpr::Var("_Evidence".to_string()),
            CExpr::Var("_ReturnK".to_string()),
        );
        let body = self.wrap_param_match(&fb.params, &direct_params, lowered_body);
        self.pop_scope();
        if pushed_native_frame {
            self.direct_handler_stack.pop();
        }

        CFunDef {
            name: output_name.to_string(),
            arity: params.len(),
            body: CExpr::Fun(params, Box::new(body)),
        }
    }

    pub(super) fn lower_cps_fun_binding_group(&mut self, group: &[&MFunBinding]) -> CFunDef {
        self.lower_cps_fun_binding_group_named(group, &group[0].name, None)
    }

    pub(super) fn lower_cps_fun_binding_group_native_variant(
        &mut self,
        group: &[&MFunBinding],
        output_name: &str,
        native_frame: DirectHandlerFrame,
    ) -> CFunDef {
        self.lower_cps_fun_binding_group_named(group, output_name, Some(native_frame))
    }

    pub(super) fn lower_cps_fun_binding_group_named(
        &mut self,
        group: &[&MFunBinding],
        output_name: &str,
        native_frame: Option<DirectHandlerFrame>,
    ) -> CFunDef {
        assert!(
            !group.is_empty(),
            "lower_cps_fun_binding_group: empty group is impossible"
        );
        if group.len() == 1 && group[0].guard.is_none() {
            return self.lower_cps_fun_binding_named(group[0], output_name, native_frame);
        }

        let name = &group[0].name;
        let source_arity = group[0].params.len();
        for fb in group {
            assert_eq!(
                fb.params.len(),
                source_arity,
                "lower_cps_fun_binding_group: clause arity mismatch for '{}'",
                name
            );
        }

        let direct_params: Vec<String> = (0..source_arity)
            .map(|arg_index| format!("_Arg{arg_index}"))
            .collect();
        let mut params = direct_params.clone();
        params.push("_Evidence".to_string());
        params.push("_ReturnK".to_string());

        let scrutinee = CExpr::Tuple(direct_params.iter().cloned().map(CExpr::Var).collect());
        let scrut_var = self.fresh_cps_temp("_FunScrut");
        let mut rest = self.case_clause_error();

        let prev_direct_candidate = self.direct_candidate_function.replace(name.clone());
        let pushed_native_frame = self.push_native_variant_frame(output_name, native_frame);
        for fb in group.iter().rev() {
            let rest_var = self.fresh_cps_temp("_FunRest");
            let rest_ref = || CExpr::Apply(Box::new(CExpr::Var(rest_var.clone())), vec![]);
            self.push_scope();
            self.bind_cps_entry_param_locals(fb);
            let body = self.lower_cps_expr(
                &fb.body,
                CExpr::Var("_Evidence".to_string()),
                CExpr::Var("_ReturnK".to_string()),
            );
            let body = match fb.guard.as_ref() {
                Some(guard) => CExpr::Case(
                    Box::new(self.lower_expr(guard)),
                    vec![
                        CArm {
                            pat: CPat::Lit(CLit::Atom("true".to_string())),
                            guard: None,
                            body,
                        },
                        CArm {
                            pat: CPat::Wildcard,
                            guard: None,
                            body: rest_ref(),
                        },
                    ],
                ),
                None => body,
            };
            let pat = CPat::Tuple(fb.params.iter().map(|pat| self.lower_pat(pat)).collect());
            self.pop_scope();
            let current = CExpr::Case(
                Box::new(CExpr::Var(scrut_var.clone())),
                vec![
                    CArm {
                        pat,
                        guard: None,
                        body,
                    },
                    CArm {
                        pat: CPat::Wildcard,
                        guard: None,
                        body: rest_ref(),
                    },
                ],
            );
            rest = CExpr::Let(
                rest_var,
                Box::new(CExpr::Fun(vec![], Box::new(rest))),
                Box::new(current),
            );
        }
        if pushed_native_frame {
            self.direct_handler_stack.pop();
        }
        self.direct_candidate_function = prev_direct_candidate;

        let body = CExpr::Let(scrut_var, Box::new(scrutinee), Box::new(rest));
        CFunDef {
            name: output_name.to_string(),
            arity: params.len(),
            body: CExpr::Fun(params, Box::new(body)),
        }
    }

    pub(super) fn export_entries(&self, name: &str) -> Vec<(String, usize)> {
        let Some(entries) = self.local_function_entries.get(name) else {
            return vec![(name.to_string(), 0)];
        };
        let mut exports = Vec::new();
        if let Some(direct_entry_arity) = entries.direct_entry_arity {
            exports.push((
                self.direct_entry_name_for(name, entries),
                direct_entry_arity,
            ));
        }
        if let Some(cps_adapter_entry_arity) = entries.cps_adapter_entry_arity {
            exports.push((name.to_string(), cps_adapter_entry_arity));
        }
        if exports.is_empty() {
            exports.push((name.to_string(), entries.source_arity));
        }
        exports
    }

    pub(super) fn needs_cps_adapter(&self, name: &str) -> bool {
        self.local_function_entries
            .get(name)
            .is_some_and(|entries| {
                entries.direct_entry_arity.is_some() && entries.cps_adapter_entry_arity.is_some()
            })
    }

    pub(super) fn direct_entry_name(&self, name: &str) -> String {
        self.local_function_entries
            .get(name)
            .map(|entries| self.direct_entry_name_for(name, entries))
            .unwrap_or_else(|| name.to_string())
    }

    pub(super) fn direct_entry_name_for(&self, name: &str, entries: &FunctionEntryInfo) -> String {
        direct_entry_name_for(name, entries)
    }
}
