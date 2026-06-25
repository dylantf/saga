use super::*;

impl Elaborator {
    pub(crate) fn elaborate_program(&mut self, program: &Program) -> Program {
        // Pass 1: Collect trait method info and function where clauses
        for decl in program {
            match decl {
                Decl::TraitDef {
                    id, name, methods, ..
                } => {
                    let resolved_name = self.resolved_trait_name(*id, name);
                    for (idx, ann) in methods.iter().enumerate() {
                        let method = &ann.node;
                        if let Some((existing_trait, _)) = self.trait_methods.get(&method.name) {
                            panic!(
                                "trait method `{}` is defined in both `{}` and `{}`",
                                method.name, existing_trait, resolved_name
                            );
                        }
                        self.trait_methods
                            .insert(method.name.clone(), (resolved_name.clone(), idx));
                    }
                }
                Decl::FunSignature {
                    name, where_clause, ..
                } => {
                    let dict_params = self.dict_params_from_where(where_clause);
                    if !dict_params.is_empty() {
                        self.fun_dict_params.insert(name.clone(), dict_params);
                    }
                }
                Decl::ImplDef {
                    id,
                    trait_name,
                    trait_type_args,
                    target_type,
                    target_type_expr,
                    type_params,
                    where_clause,
                    where_apps,
                    ..
                } => {
                    let canonical_trait = self.resolved_impl_trait_name(*id, trait_name);
                    let canonical_trait_type_args = self.resolved_trait_type_args(trait_type_args);
                    let canonical_target_type = self.resolved_impl_target_type(*id, target_type);
                    // Tuples are arity-distinguished: `(a, b)` and `(a, b, c)`
                    // both canonicalize to "Std.Base.Tuple", so suffix arity to
                    // keep their dict names and lookup keys distinct.
                    let canonical_target_type = self.impl_target_key(
                        &canonical_target_type,
                        target_type_expr.as_ref(),
                        type_params,
                    );
                    let dict_name = crate::typechecker::make_dict_name(
                        &canonical_trait,
                        &canonical_trait_type_args,
                        &self.erlang_module,
                        &canonical_target_type,
                    );
                    self.dict_names.insert(
                        (
                            canonical_trait.clone(),
                            canonical_trait_type_args.clone(),
                            canonical_target_type.clone(),
                        ),
                        dict_name,
                    );
                    // Capture where-clause constraints as (trait, param_index) pairs.
                    // This tells dict_for_type which sub-dicts to pass for parameterized impls.
                    // Always insert (even empty) so dict_for_type doesn't fall back to
                    // guessing one sub-dict per type arg (which breaks phantom type params).
                    let var_to_idx: HashMap<&str, usize> = type_params
                        .iter()
                        .enumerate()
                        .map(|(i, tp)| (tp.name.as_str(), i))
                        .collect();
                    let mut params: Vec<(String, usize)> = Vec::new();
                    for bound in where_clause {
                        let idx = var_to_idx
                            .get(bound.type_var.as_str())
                            .copied()
                            .unwrap_or(0);
                        for tr in &bound.traits {
                            let resolved = self
                                .resolution
                                .trait_ref(tr.id)
                                .unwrap_or(&tr.name)
                                .to_string();
                            params.push((resolved, idx));
                        }
                    }
                    let key = (
                        canonical_trait,
                        canonical_trait_type_args,
                        canonical_target_type,
                    );
                    let where_app_params =
                        self.where_app_dict_params_for_impl(where_apps, type_params);
                    self.impl_dict_params.insert(key.clone(), params);
                    // Insert unconditionally (even when empty): a present key
                    // marks this impl as local, so `dict_for_type` trusts this
                    // computation and only falls back to the typechecker-
                    // resolved `ImplInfo.where_app_dict_params` for imported
                    // impls (whose AST this module never sees).
                    self.impl_where_app_dict_params
                        .insert(key, where_app_params);
                }
                Decl::HandlerDef { name, body, .. } => {
                    let dict_params = self.dict_params_from_where(&body.where_clause);
                    if !dict_params.is_empty() {
                        self.handler_dict_params.insert(name.clone(), dict_params);
                    }
                }
                _ => {}
            }
        }

        // Register trait methods from checker's trait info (for traits not
        // defined in the current program, e.g. Show in Std modules).
        // Register under both bare name and canonical name so lookups work
        // before and after the resolve pass rewrites Var nodes.
        for (trait_name, info) in &self.traits {
            for (idx, method) in info.methods.iter().enumerate() {
                self.trait_methods
                    .entry(method.name.clone())
                    .or_insert_with(|| (trait_name.clone(), idx));
            }
        }
        // Add canonical-name entries from scope_map: if "show" -> "Std.Base.Show.show",
        // register "Std.Base.Show.show" -> ("Show", idx) too.
        for (bare_name, canonical) in &self.scope_map_values {
            if bare_name != canonical
                && let Some(entry) = self.trait_methods.get(bare_name).cloned()
            {
                self.trait_methods.entry(canonical.clone()).or_insert(entry);
            }
        }

        // Pass 2: Emit new program with dict constructors and elaborated functions
        let mut output = Vec::new();

        for decl in program {
            match decl {
                // Emit DictConstructor for each impl
                Decl::ImplDef {
                    id,
                    trait_name,
                    trait_type_args,
                    target_type,
                    target_type_expr,
                    type_params,
                    where_clause,
                    where_apps,
                    methods,
                    needs,
                    routed_derive_info,
                    span,
                    ..
                } => {
                    let canonical_trait = self.resolved_impl_trait_name(*id, trait_name);
                    let canonical_trait_type_args = self.resolved_trait_type_args(trait_type_args);
                    let canonical_target_base = self.resolved_impl_target_type(*id, target_type);
                    let canonical_target_type = self.impl_target_key(
                        &canonical_target_base,
                        target_type_expr.as_ref(),
                        type_params,
                    );
                    let dict_name = self
                        .dict_names
                        .get(&(
                            canonical_trait.clone(),
                            canonical_trait_type_args.clone(),
                            canonical_target_type.clone(),
                        ))
                        .cloned()
                        .unwrap();

                    let trait_info = self.traits.get(&canonical_trait).cloned();

                    // Build dict_params for conditional impls. The where-clause
                    // bounds must follow the call site's apply order (with-args
                    // bounds before no-args bounds) so the constructor's params
                    // line up positionally with the sub-dicts passed in by
                    // `dict_for_type`. See `dict_params_from_where_call_order`.
                    let mut dict_param_pairs = self.dict_params_from_where_apps(where_apps);
                    dict_param_pairs.extend(self.dict_params_from_where_call_order(where_clause));
                    let dict_params: Vec<String> = dict_param_pairs
                        .iter()
                        .map(|(trait_name, type_var)| {
                            let bare = trait_name.rsplit('.').next().unwrap_or(trait_name);
                            format!("__dict_{}_{}", bare, type_var)
                        })
                        .collect();

                    // Set up current dict params for elaborating method bodies
                    let saved = self.setup_dict_params_from_pairs(&dict_param_pairs);

                    let mut super_dicts = Vec::new();
                    if let Some(ref info) = trait_info {
                        let mut saved_param_names = Vec::new();
                        let target_args: Vec<Type> = type_params
                            .iter()
                            .enumerate()
                            .map(|(idx, param)| {
                                let var_id = u32::MAX - idx as u32;
                                saved_param_names.push((
                                    var_id,
                                    self.where_bound_var_names
                                        .insert(var_id, param.name.clone()),
                                ));
                                Type::Var(var_id)
                            })
                            .collect();
                        let target_ty = Type::Con(canonical_target_base.clone(), target_args);
                        for supertrait in &info.supertraits {
                            if let Some(super_dict) =
                                self.dict_for_type(supertrait, &[], &target_ty, *span)
                            {
                                super_dicts.push(super_dict);
                            }
                        }
                        for (var_id, previous) in saved_param_names {
                            if let Some(previous) = previous {
                                self.where_bound_var_names.insert(var_id, previous);
                            } else {
                                self.where_bound_var_names.remove(&var_id);
                            }
                        }
                    }

                    // Order methods by trait declaration order
                    let mut ordered_methods = Vec::new();
                    let mut method_effects = Vec::new();
                    let mut method_open_rows = Vec::new();
                    let saved_impl_trait = self.current_impl_trait.replace(canonical_trait.clone());
                    if let Some(ref info) = trait_info {
                        for trait_method in &info.methods {
                            if let Some(ann) = methods
                                .iter()
                                .find(|ann| ann.node.name == trait_method.name)
                            {
                                let ImplMethod { params, body, .. } = &ann.node;
                                let elab_body = self.elaborate_expr(body);
                                ordered_methods.push(Expr::synth(
                                    *span,
                                    ExprKind::Lambda {
                                        params: params.clone(),
                                        body: Box::new(elab_body),
                                    },
                                ));
                                method_effects.push(trait_method.effect_sig.effects.clone());
                                method_open_rows.push(trait_method.effect_sig.is_open_row);
                            }
                        }
                    }
                    self.current_impl_trait = saved_impl_trait;

                    self.restore_dict_params(saved);

                    // For parameterized types, if there are type_params but no where_clause,
                    // no dict params are needed. The dict is still nullary.
                    let _ = type_params; // acknowledge but don't use for now

                    let mut impl_effects: Vec<String> = needs
                        .iter()
                        .map(|e| {
                            self.scope_map_effects
                                .get(&e.name)
                                .cloned()
                                .unwrap_or_else(|| e.name.clone())
                        })
                        .collect();
                    // Routed-derive impls are synthesized with `needs: vec![]`.
                    // Source the impl's effect set from the trait method
                    // signatures' canonical effect_sigs instead — same
                    // rationale as in register_impl.
                    if routed_derive_info.is_some()
                        && let Some(ref info) = trait_info
                    {
                        for trait_method in &info.methods {
                            if methods.iter().any(|m| m.node.name == trait_method.name) {
                                impl_effects
                                    .extend(trait_method.effect_sig.effects.iter().cloned());
                            }
                        }
                    }
                    impl_effects.sort();
                    impl_effects.dedup();
                    output.push(Decl::DictConstructor {
                        id: NodeId::fresh(),
                        name: dict_name,
                        dict_params,
                        super_dicts,
                        methods: ordered_methods,
                        method_effects,
                        method_open_rows,
                        impl_effects,
                        span: *span,
                    });
                }

                // TraitDef and FunAnnotation are consumed (not emitted)
                Decl::TraitDef { .. } => {}
                Decl::FunSignature { .. } => {
                    // Keep annotations for the lowerer (it uses them for arity).
                    output.push(decl.clone());
                }

                // Elaborate function bodies
                Decl::FunBinding {
                    name,
                    params,
                    guard,
                    body,
                    span,
                    ..
                } => {
                    self.current_fun = Some(name.clone());

                    // Set up dict params for this function
                    let saved = (
                        std::mem::take(&mut self.current_dict_params),
                        std::mem::take(&mut self.current_dict_params_by_var),
                    );
                    let mut extra_params = Vec::new();

                    if let Some(dict_param_info) = self.fun_dict_params.get(name).cloned() {
                        for (trait_name, type_var) in dict_param_info {
                            // Use bare trait name in param name to avoid dots in Erlang identifiers
                            let bare = trait_name.rsplit('.').next().unwrap_or(&trait_name);
                            let param_name = format!("__dict_{}_{}", bare, type_var);
                            self.current_dict_params
                                .insert(trait_name.clone(), param_name.clone());
                            self.current_dict_params_by_var
                                .insert((trait_name.clone(), type_var.clone()), param_name.clone());
                            extra_params.push(Pat::Var {
                                id: NodeId::fresh(),
                                name: param_name,
                                span: *span,
                            });
                        }
                    }

                    let elab_body = self.elaborate_expr(body);
                    let elab_guard = guard.as_ref().map(|g| Box::new(self.elaborate_expr(g)));

                    // Prepend dict params to the function's params
                    let mut full_params = extra_params;
                    full_params.extend(params.clone());

                    self.restore_dict_params(saved);
                    self.current_fun = None;

                    output.push(Decl::FunBinding {
                        id: NodeId::fresh(),
                        name: name.clone(),
                        name_span: *span, // elaborated binding, reuse span
                        params: full_params,
                        guard: elab_guard,
                        body: elab_body,
                        span: *span,
                    });
                }

                // Elaborate handler arm bodies (so print/show get dicts inserted)
                Decl::HandlerDef {
                    doc,
                    public,
                    name,
                    name_span,
                    body,
                    span,
                    ..
                } => {
                    // Set up dict params from where clause so arm bodies can
                    // reference trait dicts (e.g. `show entity` -> `__dict_Show_a`).
                    // Each arm additionally gets the dict params from its own
                    // operation's `where` clause, threaded per call.
                    let handler_pairs = self.dict_params_from_where(&body.where_clause);
                    let saved = self.setup_dict_params(&body.where_clause);

                    let elab_arms: Vec<Annotated<HandlerArm>> = body
                        .arms
                        .iter()
                        .map(|ann| {
                            let arm = &ann.node;
                            let mut arm_pairs = handler_pairs.clone();
                            arm_pairs.extend(self.op_dict_params_for_arm(arm));
                            let arm_saved = self.setup_dict_params_from_pairs(&arm_pairs);
                            let elab = Annotated::bare(HandlerArm {
                                id: arm.id,
                                op_name: arm.op_name.clone(),
                                qualifier: arm.qualifier.clone(),
                                params: arm.params.clone(),
                                body: Box::new(self.elaborate_expr(&arm.body)),
                                finally_block: arm
                                    .finally_block
                                    .as_ref()
                                    .map(|fb| Box::new(self.elaborate_expr(fb))),
                                span: arm.span,
                            });
                            self.restore_dict_params(arm_saved);
                            elab
                        })
                        .collect();
                    let elab_return = body.return_clause.as_ref().map(|rc| {
                        Box::new(HandlerArm {
                            id: rc.id,
                            op_name: rc.op_name.clone(),
                            qualifier: rc.qualifier.clone(),
                            params: rc.params.clone(),
                            body: Box::new(self.elaborate_expr(&rc.body)),
                            finally_block: None,
                            span: rc.span,
                        })
                    });

                    self.restore_dict_params(saved);

                    output.push(Decl::HandlerDef {
                        id: NodeId::fresh(),
                        doc: doc.clone(),
                        public: *public,
                        name: name.clone(),
                        name_span: *name_span,
                        body: HandlerBody {
                            effects: body.effects.clone(),
                            needs: body.needs.clone(),
                            where_clause: body.where_clause.clone(),
                            arms: elab_arms,
                            return_clause: elab_return,
                        },
                        recovered_arms: vec![],
                        span: *span,
                        dangling_trivia: vec![],
                    });
                }

                // Pass through everything else
                _ => output.push(decl.clone()),
            }
        }

        output
    }

    /// Resolve the record type name from a node's inferred type.
    pub(crate) fn resolve_record_name(&self, node_id: crate::ast::NodeId) -> Option<String> {
        let ty = self.type_at_node.get(&node_id)?;
        match ty {
            Type::Con(name, _) => Some(name.clone()),
            Type::Record(fields) => {
                let names: Vec<&str> = fields.iter().map(|(n, _)| n.as_str()).collect();
                Some(crate::ast::anon_record_tag(&names))
            }
            _ => None,
        }
    }
}
