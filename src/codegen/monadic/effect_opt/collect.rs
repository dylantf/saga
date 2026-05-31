use super::*;

pub(super) const INLINE_HELPER_BODY_BUDGET: usize = 30;
pub(super) const FUNCTION_VARIANT_BODY_BUDGET: usize = 220;
pub(super) const NATIVE_VARIANT_PREFIX: &str = "__saga_native_variant";
pub(super) const STATIC_VARIANT_PREFIX: &str = "__saga_static_variant";

pub(super) fn collect_inline_candidates(program: &MProgram) -> HashMap<String, InlineCandidate> {
    let mut counts: HashMap<String, usize> = HashMap::new();
    let mut same_module_names = HashSet::new();
    for decl in program {
        if let MDecl::FunBinding(f) = decl {
            *counts.entry(f.name.clone()).or_default() += 1;
            same_module_names.insert(f.name.clone());
        }
    }

    let mut candidates = HashMap::new();
    for decl in program {
        let MDecl::FunBinding(f) = decl else {
            continue;
        };
        if counts.get(&f.name) != Some(&1) {
            continue;
        }
        if f.guard.is_some()
            || !helper_params_are_supported(&f.params)
            || expr_node_count(&f.body) > INLINE_HELPER_BODY_BUDGET
            || expr_yield_count(&f.body) != 1
            || expr_contains_inline_forbidden_shape(&f.body)
            || expr_calls_any(&f.body, &same_module_names)
        {
            continue;
        }
        candidates.insert(
            f.name.clone(),
            InlineCandidate {
                params: f.params.clone(),
                body: f.body.clone(),
            },
        );
    }
    candidates
}

pub(super) fn collect_handler_factory_candidates(
    program: &MProgram,
) -> HashMap<String, InlineCandidate> {
    let mut counts: HashMap<String, usize> = HashMap::new();
    for decl in program {
        if let MDecl::FunBinding(f) = decl {
            *counts.entry(f.name.clone()).or_default() += 1;
        }
    }

    let mut candidates = HashMap::new();
    for decl in program {
        let MDecl::FunBinding(f) = decl else {
            continue;
        };
        if counts.get(&f.name) != Some(&1) {
            continue;
        }
        if f.guard.is_some()
            || !helper_params_are_supported(&f.params)
            || expr_node_count(&f.body) > INLINE_HELPER_BODY_BUDGET
            || !expr_ends_in_handler_value(&f.body)
        {
            continue;
        }
        candidates.insert(
            f.name.clone(),
            InlineCandidate {
                params: f.params.clone(),
                body: f.body.clone(),
            },
        );
    }
    candidates
}

pub(super) fn collect_dict_constructors(program: &MProgram) -> HashMap<String, MDictConstructor> {
    program
        .iter()
        .filter_map(|decl| match decl {
            MDecl::DictConstructor(dc) => Some((dc.name.clone(), dc.clone())),
            _ => None,
        })
        .collect()
}

pub fn collect_imported_handler_factory_candidates(
    source_module: &str,
    program: &MProgram,
    resolution: &ResolutionMap,
    codegen_info: &ModuleCodegenInfo,
) -> HashMap<String, ImportedHandlerFactoryCandidate> {
    let public_names: HashSet<String> = codegen_info
        .exports
        .iter()
        .map(|(name, _)| name.clone())
        .collect();
    let external_names: HashSet<String> = codegen_info
        .external_funs
        .iter()
        .map(|(name, _, _, _)| name.clone())
        .collect();
    let public_pure_vals = collect_public_pure_vals(program);

    let mut counts: HashMap<String, usize> = HashMap::new();
    for decl in program {
        if let MDecl::FunBinding(f) = decl
            && f.public
            && !is_generated_variant_name(&f.name)
        {
            *counts.entry(f.name.clone()).or_default() += 1;
        }
    }

    let mut candidates = HashMap::new();
    for decl in program {
        let MDecl::FunBinding(f) = decl else {
            continue;
        };
        if !f.public
            || is_generated_variant_name(&f.name)
            || counts.get(&f.name) != Some(&1)
            || external_names.contains(&f.name)
            || f.guard.is_some()
            || !helper_params_are_supported(&f.params)
            || expr_node_count(&f.body) > INLINE_HELPER_BODY_BUDGET
            || expr_contains_imported_handler_factory_forbidden_shape(&f.body)
            || expr_has_private_same_module_refs(
                &f.body,
                source_module,
                &f.name,
                &public_names,
                resolution,
            )
        {
            continue;
        }

        let Some(body) = inline_public_pure_vals(f.body.clone(), &public_pure_vals) else {
            continue;
        };
        if !expr_ends_in_handler_value(&body) {
            continue;
        }

        candidates.insert(
            format!("{source_module}.{}", f.name),
            ImportedHandlerFactoryCandidate {
                source_module: source_module.to_string(),
                params: f.params.clone(),
                body,
            },
        );
    }

    candidates
}

pub(super) fn collect_public_pure_vals(program: &MProgram) -> HashMap<String, Atom> {
    let mut vals = HashMap::new();
    for decl in program {
        let MDecl::Val(v) = decl else {
            continue;
        };
        if !v.public {
            continue;
        }
        let MExpr::Pure(atom) = &v.value else {
            continue;
        };
        vals.insert(v.name.clone(), atom.clone());
    }
    vals
}

pub(super) fn inline_public_pure_vals(expr: MExpr, vals: &HashMap<String, Atom>) -> Option<MExpr> {
    let mut expr = expr;
    for (name, atom) in vals {
        let target = MVar {
            name: name.clone(),
            id: 0,
        };
        let free_names = free_atom_names(atom);
        let substituted = subst_expr(expr, &target, atom, &free_names);
        if substituted.blocked {
            return None;
        }
        expr = substituted.value;
    }
    Some(expr)
}

pub(super) fn collect_variant_candidates(program: &MProgram) -> HashMap<String, VariantCandidate> {
    let mut counts: HashMap<String, usize> = HashMap::new();
    for decl in program {
        if let MDecl::FunBinding(f) = decl
            && !is_generated_variant_name(&f.name)
        {
            *counts.entry(f.name.clone()).or_default() += 1;
        }
    }

    let mut candidates = HashMap::new();
    for decl in program {
        let MDecl::FunBinding(f) = decl else {
            continue;
        };
        if is_generated_variant_name(&f.name) || counts.get(&f.name) != Some(&1) {
            continue;
        }
        if f.guard.is_some()
            || !helper_params_are_supported(&f.params)
            || expr_node_count(&f.body) > FUNCTION_VARIANT_BODY_BUDGET
        {
            continue;
        }
        candidates.insert(f.name.clone(), VariantCandidate { binding: f.clone() });
    }
    candidates
}

pub fn collect_imported_function_variant_candidates(
    source_module: &str,
    program: &MProgram,
    resolution: &ResolutionMap,
    codegen_info: &ModuleCodegenInfo,
) -> HashMap<String, ImportedFunctionVariantCandidate> {
    let public_names: HashSet<String> = codegen_info
        .exports
        .iter()
        .map(|(name, _)| name.clone())
        .collect();
    let external_names: HashSet<String> = codegen_info
        .external_funs
        .iter()
        .map(|(name, _, _, _)| name.clone())
        .collect();

    let mut counts: HashMap<String, usize> = HashMap::new();
    for decl in program {
        if let MDecl::FunBinding(f) = decl
            && f.public
            && !is_generated_variant_name(&f.name)
        {
            *counts.entry(f.name.clone()).or_default() += 1;
        }
    }

    let mut candidates = HashMap::new();
    for decl in program {
        let MDecl::FunBinding(f) = decl else {
            continue;
        };
        if !f.public
            || is_generated_variant_name(&f.name)
            || counts.get(&f.name) != Some(&1)
            || external_names.contains(&f.name)
            || f.guard.is_some()
            || !helper_params_are_supported(&f.params)
            || expr_node_count(&f.body) > FUNCTION_VARIANT_BODY_BUDGET
            || expr_contains_xmod_variant_forbidden_shape_with_resolution(&f.body, resolution)
            || expr_has_private_same_module_refs(
                &f.body,
                source_module,
                &f.name,
                &public_names,
                resolution,
            )
        {
            continue;
        }

        let candidate = ImportedFunctionVariantCandidate {
            source_module: source_module.to_string(),
            binding: f.clone(),
            public_names: public_names.clone(),
        };
        candidates.insert(format!("{source_module}.{}", f.name), candidate);
    }

    candidates
}

pub fn collect_imported_dict_constructors(
    source_module: &str,
    program: &MProgram,
    resolution: &ResolutionMap,
    codegen_info: &ModuleCodegenInfo,
    cloneable_private_helpers: &HashSet<String>,
) -> HashMap<String, MDictConstructor> {
    // Debugging cross-module dictionary admission is otherwise opaque: a
    // skipped constructor just leaves residual effect calls later. Empty value
    // logs every imported dict; a non-empty value filters by module/name.
    let debug_filter = std::env::var("SAGA_DEBUG_IMPORTED_DICTS").ok();
    let public_names: HashSet<String> = codegen_info
        .exports
        .iter()
        .map(|(name, _)| name.clone())
        .collect();

    let mut candidates = HashMap::new();
    for decl in program {
        let MDecl::DictConstructor(dc) = decl else {
            continue;
        };
        // Dict constructors are compiler-generated implementation details.
        // The source export table is not a reliable visibility filter for
        // them, and imported optimized bodies may legitimately reference
        // private impl dictionaries. Private helper calls are admitted here:
        // the optimizer rewrites them to caller-local generated helper clones
        // before lowering, so the generated body never needs a remote call to
        // an unexported function.
        if let Some(reason) = imported_dict_constructor_unsupported_reason(dc, resolution) {
            if debug_imported_dict_enabled(debug_filter.as_deref(), source_module, &dc.name) {
                eprintln!(
                    "xmod dict reject unsupported: {source_module}.{}: {reason}",
                    dc.name
                );
            }
            continue;
        }
        if dc.methods.iter().any(|method| {
            expr_has_private_same_module_refs_except(
                method,
                source_module,
                &dc.name,
                &public_names,
                resolution,
                cloneable_private_helpers,
            )
        }) {
            if debug_imported_dict_enabled(debug_filter.as_deref(), source_module, &dc.name) {
                eprintln!("xmod dict reject private refs: {source_module}.{}", dc.name);
            }
            continue;
        }
        if debug_imported_dict_enabled(debug_filter.as_deref(), source_module, &dc.name) {
            eprintln!("xmod dict accept: {source_module}.{}", dc.name);
        }
        candidates.insert(dc.name.clone(), dc.clone());
    }

    candidates
}

pub fn collect_imported_private_helper_candidates(
    source_module: &str,
    program: &MProgram,
    resolution: &ResolutionMap,
    codegen_info: &ModuleCodegenInfo,
) -> HashMap<String, ImportedPrivateHelperCandidate> {
    let public_names: HashSet<String> = codegen_info
        .exports
        .iter()
        .map(|(name, _)| name.clone())
        .collect();
    let external_names: HashSet<String> = codegen_info
        .external_funs
        .iter()
        .map(|(name, _, _, _)| name.clone())
        .collect();

    let mut counts: HashMap<String, usize> = HashMap::new();
    for decl in program {
        if let MDecl::FunBinding(f) = decl
            && !f.public
            && !is_generated_variant_name(&f.name)
        {
            *counts.entry(f.name.clone()).or_default() += 1;
        }
    }

    let mut raw_candidates: HashMap<String, MFunBinding> = HashMap::new();
    for decl in program {
        let MDecl::FunBinding(f) = decl else {
            continue;
        };
        if f.public
            || public_names.contains(&f.name)
            || is_generated_variant_name(&f.name)
            || counts.get(&f.name) != Some(&1)
            || external_names.contains(&f.name)
            || f.guard.is_some()
            || expr_node_count(&f.body) > FUNCTION_VARIANT_BODY_BUDGET
            || expr_contains_xmod_variant_forbidden_shape_with_resolution(&f.body, resolution)
        {
            continue;
        }
        raw_candidates.insert(f.name.clone(), f.clone());
    }

    let mut cloneable = HashSet::new();
    let mut changed = true;
    while changed {
        changed = false;
        for (name, f) in &raw_candidates {
            if cloneable.contains(name) {
                continue;
            }
            if expr_has_private_same_module_refs_except(
                &f.body,
                source_module,
                name,
                &public_names,
                resolution,
                &cloneable,
            ) {
                continue;
            }
            cloneable.insert(name.clone());
            changed = true;
        }
    }

    let mut candidates = HashMap::new();
    for name in cloneable {
        let Some(binding) = raw_candidates.get(&name).cloned() else {
            continue;
        };
        candidates.insert(
            format!("{source_module}.{name}"),
            ImportedPrivateHelperCandidate {
                source_module: source_module.to_string(),
                binding,
            },
        );
    }

    candidates
}

pub(super) fn imported_dict_constructor_unsupported_reason(
    dc: &MDictConstructor,
    resolution: &ResolutionMap,
) -> Option<String> {
    for (index, method) in dc.methods.iter().enumerate() {
        let MExpr::Pure(Atom::Lambda { body, .. }) = method else {
            return Some(format!("method {index} is not a pure lambda"));
        };
        let node_count = expr_node_count(body);
        if node_count > FUNCTION_VARIANT_BODY_BUDGET {
            return Some(format!(
                "method {index} body has {node_count} nodes, budget is {FUNCTION_VARIANT_BODY_BUDGET}"
            ));
        }
        if let Some(reason) = imported_dict_constructor_forbidden_shape_reason(body, resolution) {
            return Some(format!(
                "method {index} contains a forbidden xmod shape: {reason}"
            ));
        }
    }
    None
}

pub(super) fn imported_dict_constructor_forbidden_shape_reason(
    expr: &MExpr,
    resolution: &ResolutionMap,
) -> Option<String> {
    xmod_forbidden_shape_reason(expr, "body", Some(resolution))
}

pub(super) fn xmod_forbidden_shape_reason(
    expr: &MExpr,
    path: &str,
    resolution: Option<&ResolutionMap>,
) -> Option<String> {
    match expr {
        MExpr::LetFun { .. } => Some(format!("{path}: let-fun")),
        MExpr::HandlerValue { .. } => Some(format!("{path}: handler value")),
        MExpr::Pure(atom) => xmod_forbidden_atom_reason(atom, &format!("{path}.pure")),
        MExpr::Yield { args, .. } | MExpr::ForeignCall { args, .. } => args
            .iter()
            .enumerate()
            .find_map(|(i, atom)| xmod_forbidden_atom_reason(atom, &format!("{path}.arg{i}"))),
        MExpr::Bind { value, body, .. } | MExpr::Let { value, body, .. } => {
            xmod_forbidden_shape_reason(value, &format!("{path}.value"), resolution)
                .or_else(|| xmod_forbidden_shape_reason(body, &format!("{path}.body"), resolution))
        }
        MExpr::Ensure { body, cleanup } => {
            xmod_forbidden_shape_reason(body, &format!("{path}.body"), resolution).or_else(|| {
                xmod_forbidden_shape_reason(cleanup, &format!("{path}.cleanup"), resolution)
            })
        }
        MExpr::Case {
            scrutinee, arms, ..
        } => xmod_forbidden_atom_reason(scrutinee, &format!("{path}.scrutinee")).or_else(|| {
            arms.iter().enumerate().find_map(|(i, arm)| {
                arm.guard
                    .as_ref()
                    .and_then(|guard| {
                        xmod_forbidden_shape_reason(
                            guard,
                            &format!("{path}.arm{i}.guard"),
                            resolution,
                        )
                    })
                    .or_else(|| {
                        xmod_forbidden_shape_reason(
                            &arm.body,
                            &format!("{path}.arm{i}.body"),
                            resolution,
                        )
                    })
            })
        }),
        MExpr::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => xmod_forbidden_atom_reason(cond, &format!("{path}.cond"))
            .or_else(|| {
                xmod_forbidden_shape_reason(then_branch, &format!("{path}.then"), resolution)
            })
            .or_else(|| {
                xmod_forbidden_shape_reason(else_branch, &format!("{path}.else"), resolution)
            }),
        MExpr::App { head, args, .. } => match head {
            Atom::Lambda { params, body, .. }
                if immediate_lambda_app_is_supported(params, body, args.len()) =>
            {
                args.iter()
                    .enumerate()
                    .find_map(|(i, atom)| {
                        xmod_forbidden_atom_reason(atom, &format!("{path}.arg{i}"))
                    })
                    .or_else(|| {
                        xmod_forbidden_shape_reason(
                            body,
                            &format!("{path}.lambda_body"),
                            resolution,
                        )
                    })
            }
            _ => xmod_forbidden_atom_reason(head, &format!("{path}.head")).or_else(|| {
                args.iter().enumerate().find_map(|(i, atom)| {
                    if app_head_allows_lambda_arg(head, resolution)
                        && matches!(atom, Atom::Lambda { .. })
                    {
                        None
                    } else {
                        xmod_forbidden_atom_reason(atom, &format!("{path}.arg{i}"))
                    }
                })
            }),
        },
        MExpr::Resume { value, .. }
        | MExpr::FieldAccess { record: value, .. }
        | MExpr::DictMethodAccess { dict: value, .. }
        | MExpr::UnaryMinus { value, .. } => xmod_forbidden_atom_reason(value, path),
        MExpr::RecordUpdate { record, fields, .. } => {
            xmod_forbidden_atom_reason(record, &format!("{path}.record")).or_else(|| {
                fields.iter().enumerate().find_map(|(i, (_, atom))| {
                    xmod_forbidden_atom_reason(atom, &format!("{path}.field{i}"))
                })
            })
        }
        MExpr::BinOp { left, right, .. } => {
            xmod_forbidden_atom_reason(left, &format!("{path}.left"))
                .or_else(|| xmod_forbidden_atom_reason(right, &format!("{path}.right")))
        }
        MExpr::BitString { segments, .. } => segments.iter().enumerate().find_map(|(i, seg)| {
            xmod_forbidden_atom_reason(&seg.value, &format!("{path}.segment{i}.value")).or_else(
                || {
                    seg.size.as_ref().and_then(|size| {
                        xmod_forbidden_atom_reason(size, &format!("{path}.segment{i}.size"))
                    })
                },
            )
        }),
        MExpr::Receive { arms, after, .. } => {
            arms.iter()
                .enumerate()
                .find_map(|(i, arm)| {
                    arm.guard
                        .as_ref()
                        .and_then(|guard| {
                            xmod_forbidden_shape_reason(
                                guard,
                                &format!("{path}.arm{i}.guard"),
                                resolution,
                            )
                        })
                        .or_else(|| {
                            xmod_forbidden_shape_reason(
                                &arm.body,
                                &format!("{path}.arm{i}.body"),
                                resolution,
                            )
                        })
                })
                .or_else(|| {
                    after.as_ref().and_then(|(timeout, body)| {
                        xmod_forbidden_atom_reason(timeout, &format!("{path}.after.timeout"))
                            .or_else(|| {
                                xmod_forbidden_shape_reason(
                                    body,
                                    &format!("{path}.after.body"),
                                    resolution,
                                )
                            })
                    })
                })
        }
        MExpr::With { handler, body, .. } => {
            xmod_forbidden_handler_reason(handler, &format!("{path}.handler"), resolution)
                .or_else(|| xmod_forbidden_shape_reason(body, &format!("{path}.body"), resolution))
        }
    }
}

pub(super) fn xmod_forbidden_handler_reason(
    handler: &MHandler,
    path: &str,
    resolution: Option<&ResolutionMap>,
) -> Option<String> {
    match handler {
        MHandler::Static {
            arms,
            return_clause,
            ..
        } => arms
            .iter()
            .enumerate()
            .find_map(|(i, arm)| {
                xmod_forbidden_handler_arm_reason(arm, &format!("{path}.arm{i}"), resolution)
            })
            .or_else(|| {
                return_clause.as_ref().and_then(|arm| {
                    xmod_forbidden_handler_arm_reason(arm, &format!("{path}.return"), resolution)
                })
            }),
        MHandler::Dynamic { .. } => Some(format!("{path}: dynamic handler")),
        MHandler::Native { .. } => Some(format!("{path}: native handler")),
        MHandler::Composite { .. } => Some(format!("{path}: composite handler")),
    }
}

pub(super) fn xmod_forbidden_handler_arm_reason(
    arm: &MHandlerArm,
    path: &str,
    resolution: Option<&ResolutionMap>,
) -> Option<String> {
    if arm.finally_block.is_some() {
        return Some(format!("{path}: finally"));
    }
    xmod_forbidden_shape_reason(&arm.body, &format!("{path}.body"), resolution)
}

pub(super) fn xmod_forbidden_atom_reason(atom: &Atom, path: &str) -> Option<String> {
    match atom {
        Atom::Lambda { .. } => Some(format!("{path}: lambda atom")),
        Atom::Ctor { args, .. } => args
            .iter()
            .enumerate()
            .find_map(|(i, arg)| xmod_forbidden_atom_reason(arg, &format!("{path}.ctor_arg{i}"))),
        Atom::Tuple { elements, .. } => elements
            .iter()
            .enumerate()
            .find_map(|(i, arg)| xmod_forbidden_atom_reason(arg, &format!("{path}.tuple_arg{i}"))),
        Atom::AnonRecord { fields, .. } | Atom::Record { fields, .. } => {
            fields.iter().enumerate().find_map(|(i, (_, atom))| {
                xmod_forbidden_atom_reason(atom, &format!("{path}.field{i}"))
            })
        }
        Atom::BackendSpawnThunk { callback, .. } => {
            xmod_forbidden_atom_reason(callback, &format!("{path}.spawn_callback"))
        }
        Atom::Var { .. }
        | Atom::Lit { .. }
        | Atom::DictRef { .. }
        | Atom::QualifiedRef { .. }
        | Atom::Symbol { .. }
        | Atom::BackendAtom { .. } => None,
    }
}

pub(super) fn app_head_allows_lambda_arg(head: &Atom, resolution: Option<&ResolutionMap>) -> bool {
    let Some(resolution) = resolution else {
        return false;
    };
    let source = match head {
        Atom::Var { source, .. } | Atom::QualifiedRef { source, .. } => *source,
        _ => return false,
    };
    resolution
        .get(&source)
        .is_some_and(|resolved| matches!(resolved.kind, ResolvedCodegenKind::BeamFunction { .. }))
}

pub(super) fn debug_imported_dict_enabled(
    filter: Option<&str>,
    source_module: &str,
    name: &str,
) -> bool {
    let Some(filter) = filter else {
        return false;
    };
    filter.is_empty()
        || source_module.contains(filter)
        || name.contains(filter)
        || format!("{source_module}.{name}").contains(filter)
}

pub(super) fn imported_variant_head_info(atom: &Atom) -> Option<(String, u32, crate::ast::NodeId)> {
    match atom {
        Atom::Var { name, source } => Some((name.name.clone(), name.id, *source)),
        Atom::QualifiedRef { name, source, .. } => Some((name.clone(), source.0, *source)),
        _ => None,
    }
}

pub(super) fn remove_dead_variant_sources(program: MProgram) -> MProgram {
    let reachable = reachable_decl_names(&program);
    let generated_source_ids = generated_variant_source_ids(&program, &reachable);
    if generated_source_ids.is_empty() {
        return program;
    }

    program
        .into_iter()
        .filter(|decl| match decl {
            MDecl::FunBinding(f)
                if !f.public
                    && !is_generated_variant_name(&f.name)
                    && generated_source_ids.contains(&f.id) =>
            {
                reachable.contains(&f.name)
            }
            _ => true,
        })
        .collect()
}

pub(super) fn generated_variant_source_ids(
    program: &MProgram,
    reachable: &HashSet<String>,
) -> HashSet<crate::ast::NodeId> {
    program
        .iter()
        .filter_map(|decl| match decl {
            MDecl::FunBinding(f)
                if is_generated_variant_name(&f.name) && reachable.contains(&f.name) =>
            {
                Some(f.id)
            }
            _ => None,
        })
        .collect()
}

pub(super) fn reachable_decl_names(program: &MProgram) -> HashSet<String> {
    let decl_names: HashSet<String> = program
        .iter()
        .filter_map(|decl| match decl {
            MDecl::FunBinding(f) => Some(f.name.clone()),
            MDecl::Val(v) => Some(v.name.clone()),
            MDecl::DictConstructor(d) => Some(d.name.clone()),
            MDecl::Passthrough(_) => None,
        })
        .collect();

    let mut reachable = HashSet::new();
    let mut worklist = program
        .iter()
        .filter_map(|decl| match decl {
            MDecl::FunBinding(f) if f.public || f.name == "main" || f.name == "tests" => {
                Some(f.name.clone())
            }
            MDecl::Val(v) if v.public || v.name == "main" || v.name == "tests" => {
                Some(v.name.clone())
            }
            MDecl::DictConstructor(d) => Some(d.name.clone()),
            MDecl::Passthrough(_) | MDecl::FunBinding(_) | MDecl::Val(_) => None,
        })
        .collect::<Vec<_>>();

    while let Some(name) = worklist.pop() {
        if !reachable.insert(name.clone()) {
            continue;
        }
        let Some(decl) = program
            .iter()
            .find(|decl| decl_name(decl) == Some(name.as_str()))
        else {
            continue;
        };
        let mut refs = HashSet::new();
        collect_decl_name_refs(decl, &mut refs);
        for reference in refs {
            if decl_names.contains(&reference) && !reachable.contains(&reference) {
                worklist.push(reference);
            }
        }
    }

    reachable
}

pub(super) fn decl_name(decl: &MDecl) -> Option<&str> {
    match decl {
        MDecl::FunBinding(f) => Some(&f.name),
        MDecl::Val(v) => Some(&v.name),
        MDecl::DictConstructor(d) => Some(&d.name),
        MDecl::Passthrough(_) => None,
    }
}

pub(super) fn collect_decl_name_refs(decl: &MDecl, out: &mut HashSet<String>) {
    match decl {
        MDecl::FunBinding(f) => {
            if let Some(guard) = &f.guard {
                collect_expr_var_names(guard, out);
            }
            collect_expr_var_names(&f.body, out);
        }
        MDecl::Val(v) => collect_expr_var_names(&v.value, out),
        MDecl::DictConstructor(d) => {
            for method in &d.methods {
                collect_expr_var_names(method, out);
            }
        }
        MDecl::Passthrough(_) => {}
    }
}
