use super::*;

impl<'a, 'info> DirectLowerer<'a, 'info> {
    pub(super) fn lower_static_handler_specialized_local_cps_call(
        &mut self,
        function_name: &str,
        args: &[Atom],
        evidence: CExpr,
        return_k: CExpr,
    ) -> Option<CExpr> {
        let fb = self.local_fun_bindings.get(function_name)?.clone();
        if fb.guard.is_some() || fb.params.iter().any(|p| !direct_param_supported(p)) {
            return None;
        }
        let bindings = self.direct_call_param_bindings(&fb.params, args)?;
        let known_dict_aliases = self.known_dict_aliases_for_params(&fb.params, args);
        let known_atom_bindings =
            self.known_direct_atom_pattern_bindings_for_params(&fb.params, args);

        self.static_handler_inline_stack
            .push(function_name.to_string());
        self.push_scope();
        self.bind_fun_param_locals_with_arg_shapes(&fb, args);
        self.bind_known_dict_values(known_dict_aliases);
        self.bind_known_direct_atom_pattern_values(known_atom_bindings);
        let supported = self.expr_is_cps_island_subset(&fb.body);
        let lowered_body = supported.then(|| self.lower_cps_expr(&fb.body, evidence, return_k));
        self.pop_scope();
        self.static_handler_inline_stack.pop();

        lowered_body.map(|body| {
            bindings
                .into_iter()
                .rev()
                .fold(body, |body, (name, value)| {
                    if super::direct_core_refs::core_expr_mentions_core_var(&name, &body) {
                        CExpr::Let(name, Box::new(value), Box::new(body))
                    } else {
                        body
                    }
                })
        })
    }

    pub(super) fn static_handler_specialized_local_cps_call_candidate(
        &mut self,
        head: &Atom,
        args: &[Atom],
    ) -> Option<String> {
        if !self
            .direct_handler_stack
            .iter()
            .any(|frame| matches!(frame, DirectHandlerFrame::Static { .. }))
        {
            return None;
        }

        let local_name = match head {
            Atom::Var { name, .. } => name.name.clone(),
            _ => return None,
        };
        if self.static_handler_inline_stack.contains(&local_name) {
            return None;
        }

        let CallShape::Cps {
            module: None,
            source_arity,
            adapter_arity,
            effects,
            ..
        } = self.call_shape(head)?
        else {
            return None;
        };
        if effects.is_empty()
            || source_arity != args.len()
            || adapter_arity != args.len() + 2
            || !self.active_static_handlers_cover_effects(&effects)
            || !args.iter().all(|arg| self.atom_is_direct_subset(arg))
        {
            return None;
        }

        let fb = self.local_fun_bindings.get(&local_name)?;
        if fb.guard.is_some() || fb.params.iter().any(|p| !direct_param_supported(p)) {
            return None;
        }
        Some(local_name)
    }

    pub(super) fn lower_static_handler_specialized_imported_cps_call(
        &mut self,
        candidate: ImportedStaticHandlerCall,
        args: &[Atom],
        evidence: CExpr,
        return_k: CExpr,
    ) -> Option<CExpr> {
        let ImportedStaticHandlerCall {
            source_module_name,
            erlang_module,
            function_name,
            program,
        } = candidate;
        let key = format!("{erlang_module}:{function_name}");
        if self.static_handler_inline_stack.contains(&key) {
            return None;
        }

        let fb = program.iter().find_map(|decl| match decl {
            MDecl::FunBinding(fb) if fb.name == function_name => Some(fb.clone()),
            _ => None,
        })?;
        if fb.guard.is_some() || fb.params.iter().any(|p| !direct_param_supported(p)) {
            return None;
        }
        let bindings = self.direct_call_param_bindings(&fb.params, args)?;
        let known_dict_aliases = self.known_dict_aliases_for_params(&fb.params, args);
        let known_atom_bindings =
            self.known_direct_atom_pattern_bindings_for_params(&fb.params, args);

        let compiled = self.module_ctx.modules.get(&source_module_name)?;
        let mut imported = DirectLowerer::new(
            &compiled.resolution,
            self.ctors,
            self.module_ctx,
            self.handler_info,
            self.effect_info,
            self.handler_value_map,
            self.imported_dict_constructors.clone(),
            self.options,
        );
        imported.current_module = source_module_name.clone();
        imported.classify_program(&program);
        imported.apply_codegen_info_function_shapes(&compiled.codegen_info);
        imported.compute_function_lowering_plans(&program);
        imported.compute_local_function_entries(&program);
        for (name, constructor) in &self.local_dict_constructors {
            imported
                .local_dict_constructors
                .entry(name.clone())
                .or_insert_with(|| constructor.clone());
        }
        imported.current_module = self.current_module.clone();
        imported.imported_clone_source_module = Some(source_module_name);
        imported.locals = self.locals.clone();
        imported.local_shapes = self.local_shapes.clone();
        imported.direct_handler_stack = self.direct_handler_stack.clone();
        imported.result_delimiter_stack = self.result_delimiter_stack.clone();
        imported.static_handler_inline_stack = self.static_handler_inline_stack.clone();
        imported.static_handler_inline_stack.push(key);
        imported.cps_temp_counter = self.cps_temp_counter;

        imported.push_scope();
        imported.bind_fun_param_locals(&fb);
        imported.bind_known_dict_values(known_dict_aliases);
        imported.bind_known_direct_atom_pattern_values(known_atom_bindings);
        let lowered_body = imported
            .expr_is_cps_island_subset(&fb.body)
            .then(|| imported.lower_cps_expr(&fb.body, evidence, return_k));
        imported.pop_scope();

        self.cps_temp_counter = imported.cps_temp_counter;
        let source_public_names: HashSet<String> = compiled
            .codegen_info
            .exports
            .iter()
            .map(|(name, _)| name.clone())
            .chain(
                compiled
                    .codegen_info
                    .trait_impl_dicts
                    .iter()
                    .map(|dict| dict.dict_name.clone()),
            )
            .collect();
        lowered_body.and_then(|body| {
            if core_expr_has_private_remote_source_call(&body, &erlang_module, &source_public_names)
            {
                return None;
            }
            bindings
                .into_iter()
                .rev()
                .fold(body, |body, (name, value)| {
                    CExpr::Let(name, Box::new(value), Box::new(body))
                })
                .into()
        })
    }

    pub(super) fn imported_static_handler_call_candidate(
        &mut self,
        head: &Atom,
        args: &[Atom],
    ) -> Option<ImportedStaticHandlerCall> {
        if !self
            .direct_handler_stack
            .iter()
            .any(|frame| matches!(frame, DirectHandlerFrame::Static { .. }))
        {
            return None;
        }
        let CallShape::Cps {
            module: Some(erlang_module),
            name,
            source_arity,
            adapter_arity,
            effects,
        } = self.call_shape(head)?
        else {
            return None;
        };
        if effects.is_empty()
            || source_arity != args.len()
            || adapter_arity != args.len() + 2
            || !self.active_static_handlers_cover_effects(&effects)
            || !args.iter().all(|arg| self.atom_is_direct_subset(arg))
        {
            return None;
        }

        let (source_module_name, compiled) =
            self.compiled_module_for_erlang_module(&erlang_module)?;
        let program = self.monadic_program_for_compiled_module(compiled);
        if !program
            .iter()
            .any(|decl| matches!(decl, MDecl::FunBinding(fb) if fb.name == name))
        {
            return None;
        }
        Some(ImportedStaticHandlerCall {
            source_module_name,
            erlang_module,
            function_name: name,
            program,
        })
    }

    pub(super) fn compiled_module_for_erlang_module(
        &self,
        erlang_module: &str,
    ) -> Option<(String, &crate::codegen::CompiledModule)> {
        self.module_ctx
            .modules
            .iter()
            .find_map(|(module_name, compiled)| {
                (erlang_module_name(module_name) == erlang_module)
                    .then(|| (module_name.clone(), compiled))
            })
    }

    pub(super) fn monadic_program_for_compiled_module(
        &self,
        compiled: &crate::codegen::CompiledModule,
    ) -> MProgram {
        let anf_imported =
            crate::codegen::anf::normalize(compiled.elaborated.clone(), Some(&compiled.resolution));
        let imported_handler_decls = HashMap::new();
        let (program, _) = crate::codegen::monadic::translate::translate_with_imports(
            &anf_imported,
            &compiled.resolution,
            self.effect_info,
            &imported_handler_decls,
        );
        program
    }

    pub(super) fn active_static_handlers_cover_effects(&self, effects: &[String]) -> bool {
        effects
            .iter()
            .all(|effect| self.active_static_handler_handles_effect(effect))
    }

    pub(super) fn active_static_handler_handles_effect(&self, effect: &str) -> bool {
        self.direct_handler_stack.iter().rev().any(|frame| {
            let DirectHandlerFrame::Static { arms } = frame else {
                return false;
            };
            arms.iter()
                .any(|arm| Self::effect_names_match(&arm.op.effect, effect))
        })
    }
}

fn core_expr_has_private_remote_source_call(
    expr: &CExpr,
    source_erlang_module: &str,
    public_names: &HashSet<String>,
) -> bool {
    match expr {
        CExpr::Lit(_) | CExpr::Var(_) | CExpr::Nil | CExpr::FunRef(_, _) => false,
        CExpr::Fun(_, body) | CExpr::Annotated { expr: body, .. } => {
            core_expr_has_private_remote_source_call(body, source_erlang_module, public_names)
        }
        CExpr::Let(_, value, body) => {
            core_expr_has_private_remote_source_call(value, source_erlang_module, public_names)
                || core_expr_has_private_remote_source_call(
                    body,
                    source_erlang_module,
                    public_names,
                )
        }
        CExpr::Apply(head, args) => {
            core_expr_has_private_remote_source_call(head, source_erlang_module, public_names)
                || args.iter().any(|arg| {
                    core_expr_has_private_remote_source_call(
                        arg,
                        source_erlang_module,
                        public_names,
                    )
                })
        }
        CExpr::Call(module, name, args) => {
            (module == source_erlang_module && !public_names.contains(name))
                || args.iter().any(|arg| {
                    core_expr_has_private_remote_source_call(
                        arg,
                        source_erlang_module,
                        public_names,
                    )
                })
        }
        CExpr::Case(scrutinee, arms) => {
            core_expr_has_private_remote_source_call(scrutinee, source_erlang_module, public_names)
                || arms.iter().any(|arm| {
                    arm.guard.as_ref().is_some_and(|guard| {
                        core_expr_has_private_remote_source_call(
                            guard,
                            source_erlang_module,
                            public_names,
                        )
                    }) || core_expr_has_private_remote_source_call(
                        &arm.body,
                        source_erlang_module,
                        public_names,
                    )
                })
        }
        CExpr::Tuple(items) | CExpr::Values(items) => items.iter().any(|item| {
            core_expr_has_private_remote_source_call(item, source_erlang_module, public_names)
        }),
        CExpr::Cons(head, tail) => {
            core_expr_has_private_remote_source_call(head, source_erlang_module, public_names)
                || core_expr_has_private_remote_source_call(tail, source_erlang_module, public_names)
        }
        CExpr::LetRec(bindings, body) => {
            bindings.iter().any(|(_, _, binding_body)| {
                core_expr_has_private_remote_source_call(
                    binding_body,
                    source_erlang_module,
                    public_names,
                )
            }) || core_expr_has_private_remote_source_call(
                body,
                source_erlang_module,
                public_names,
            )
        }
        CExpr::Receive(arms, timeout, after_body) => {
            arms.iter().any(|arm| {
                arm.guard.as_ref().is_some_and(|guard| {
                    core_expr_has_private_remote_source_call(
                        guard,
                        source_erlang_module,
                        public_names,
                    )
                }) || core_expr_has_private_remote_source_call(
                    &arm.body,
                    source_erlang_module,
                    public_names,
                )
            }) || core_expr_has_private_remote_source_call(
                timeout,
                source_erlang_module,
                public_names,
            ) || core_expr_has_private_remote_source_call(
                after_body,
                source_erlang_module,
                public_names,
            )
        }
        CExpr::Try {
            expr,
            ok_body,
            catch_body,
            ..
        } => {
            core_expr_has_private_remote_source_call(expr, source_erlang_module, public_names)
                || core_expr_has_private_remote_source_call(
                    ok_body,
                    source_erlang_module,
                    public_names,
                )
                || core_expr_has_private_remote_source_call(
                    catch_body,
                    source_erlang_module,
                    public_names,
                )
        }
        CExpr::Binary(segments) => segments.iter().any(|segment| match segment {
            CBinSeg::Byte(_) => false,
            CBinSeg::BinaryAll(value) | CBinSeg::Segment { value, .. } => {
                core_expr_has_private_remote_source_call(
                    value,
                    source_erlang_module,
                    public_names,
                )
            }
        }),
    }
}
