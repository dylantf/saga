use super::*;

fn typecheck_trace_enabled() -> bool {
    std::env::var_os("SAGA_TYPECHECK_TRACE").is_some()
}

fn trace_typecheck_phase(module: Option<&str>, phase: &str, duration: std::time::Duration) {
    if !typecheck_trace_enabled() {
        return;
    }

    let line = format!(
        "[saga-typecheck] module={} phase={} elapsed={:.1}ms",
        module.unwrap_or("<unknown>"),
        phase,
        duration.as_secs_f64() * 1000.0,
    );
    if let Some(path) = std::env::var_os("SAGA_TYPECHECK_TRACE_FILE") {
        use std::io::Write;
        if let Ok(mut file) = std::fs::OpenOptions::new()
            .create(true)
            .append(true)
            .open(path)
        {
            let _ = writeln!(file, "{line}");
        }
    } else {
        eprintln!("{line}");
    }
}

fn timed_typecheck_phase<T>(module: Option<&str>, phase: &str, f: impl FnOnce() -> T) -> T {
    if !typecheck_trace_enabled() {
        return f();
    }
    let start = std::time::Instant::now();
    let result = f();
    trace_typecheck_phase(module, phase, start.elapsed());
    result
}

impl Checker {
    pub(crate) fn build_effect_row_from_refs(
        &mut self,
        effects: &[ast::EffectRef],
        effect_row_var: &[(String, Span)],
        params_list: &mut Vec<(String, u32)>,
    ) -> Result<EffectRow, Diagnostic> {
        if effects.is_empty() && effect_row_var.is_empty() {
            return Ok(EffectRow::closed(vec![]));
        }

        let mut seen_effects: HashMap<String, Vec<Type>> = HashMap::new();
        let mut effect_refs = Vec::new();
        for e in effects {
            let args: Vec<Type> = self.convert_effect_ref_args(e, params_list);
            let current_display = self.prettify_type(&Type::Con(
                e.name.rsplit('.').next().unwrap_or(&e.name).to_string(),
                args.clone(),
            ));
            let name = self.resolved_effect_name(e.id, &e.name);
            if !self.effects.contains_key(&name) {
                self.collected_diagnostics.push(Diagnostic::error_at(
                    e.span,
                    format!("undefined effect: {}", e.name),
                ));
            }
            if let Some(prev_args) = seen_effects.get(&name) {
                if prev_args != &args {
                    let previous_display = self.prettify_type(&Type::Con(
                        e.name.rsplit('.').next().unwrap_or(&e.name).to_string(),
                        prev_args.clone(),
                    ));
                    return Err(Diagnostic::error_at(
                        e.span,
                        format!(
                            "conflicting effect requirements in `needs`: `{}` and `{}` both refer to `{}`, but with different type arguments",
                            previous_display,
                            current_display,
                            e.name.rsplit('.').next().unwrap_or(&e.name),
                        ),
                    ));
                }
                continue;
            }
            seen_effects.insert(name.clone(), args.clone());
            effect_refs.push(EffectEntry::unnamed(name, args));
        }
        let tails: Vec<Type> = effect_row_var
            .iter()
            .map(|(rv_name, _)| {
                let id = if let Some((_, id)) = params_list.iter().find(|(n, _)| n == rv_name) {
                    *id
                } else {
                    let id = self.next_var;
                    self.next_var += 1;
                    params_list.push((rv_name.clone(), id));
                    id
                };
                Type::Var(id)
            })
            .collect();
        Ok(EffectRow {
            effects: effect_refs,
            tails,
        })
    }

    pub(crate) fn function_type_with_innermost_effects(
        &self,
        param_types: &[Type],
        return_type: Type,
        effect_row: EffectRow,
    ) -> Type {
        let mut fun_ty = return_type;
        let mut first_arrow = true;
        for param_ty in param_types.iter().rev() {
            if first_arrow {
                fun_ty = Type::Fun(
                    Box::new(param_ty.clone()),
                    Box::new(fun_ty),
                    effect_row.clone(),
                );
            } else {
                fun_ty = Type::arrow(param_ty.clone(), fun_ty);
            }
            first_arrow = false;
        }
        fun_ty
    }

    // --- Top-level declarations ---

    /// Typecheck a program and return the public result.
    /// This is the main entry point for external callers.
    pub fn check_program(&mut self, program: &mut [Decl]) -> CheckResult {
        self.check_program_with_result(program, Checker::to_result)
    }

    /// Typecheck a program and return a result optimized for editor use.
    pub fn check_program_lsp(&mut self, program: &mut [Decl]) -> CheckResult {
        self.check_program_with_result(program, Checker::to_lsp_result)
    }

    fn check_program_with_result(
        &mut self,
        program: &mut [Decl],
        build_result: fn(&Checker) -> CheckResult,
    ) -> CheckResult {
        let total_start = typecheck_trace_enabled().then(std::time::Instant::now);
        if let Err(errors) = self.check_program_inner(program) {
            for e in errors {
                self.collected_diagnostics.push(e);
            }
        }
        let module = self.current_module.clone();
        timed_typecheck_phase(module.as_deref(), "check_unused_functions", || {
            self.check_unused_functions()
        });
        timed_typecheck_phase(module.as_deref(), "check_unused_variables", || {
            self.check_unused_variables()
        });
        timed_typecheck_phase(module.as_deref(), "zonk_warnings", || self.zonk_warnings());
        let result = timed_typecheck_phase(module.as_deref(), "to_result", || build_result(self));
        if let Some(start) = total_start {
            trace_typecheck_phase(module.as_deref(), "check_program_total", start.elapsed());
        }
        result
    }

    /// Internal implementation of check_program.
    /// Returns Err for fatal errors that prevent further checking.
    /// Non-fatal diagnostics are accumulated in collected_diagnostics.
    pub(crate) fn check_program_inner(
        &mut self,
        program: &mut [Decl],
    ) -> std::result::Result<(), Vec<Diagnostic>> {
        let initial_module = self.current_module.clone();
        timed_typecheck_phase(initial_module.as_deref(), "infer_current_module", || {
            // Infer current_module from the program's module declaration if not
            // already set by the caller. This ensures type name canonicalization
            // works regardless of which entry point invoked the checker.
            if self.current_module.is_none() {
                for decl in program.iter() {
                    if let Decl::ModuleDecl { path, .. } = decl {
                        self.current_module = Some(path.join("."));
                        break;
                    }
                }
            }
        });
        let module = self.current_module.clone();

        timed_typecheck_phase(module.as_deref(), "seed_local_type_names", || {
            // Add local type names to scope_map BEFORE register_definitions, so that
            // convert_type_expr can resolve local types during declaration registration.
            // Local types shadow imported types (use `insert`, not `or_insert`).
            for decl in program.iter() {
                let type_name = match decl {
                    Decl::TypeDef { name, .. }
                    | Decl::RecordDef { name, .. }
                    | Decl::TypeAlias { name, .. } => Some(name),
                    _ => None,
                };
                if let Some(name) = type_name {
                    let canonical = match &self.current_module {
                        Some(module) => format!("{}.{}", module, name),
                        None => name.clone(),
                    };
                    self.scope_map.types.insert(name.clone(), canonical);
                }
            }
        });
        timed_typecheck_phase(module.as_deref(), "register_active_scc_headers", || {
            self.register_active_scc_headers()
        })
        .map_err(|msg| {
            vec![Diagnostic::error_at(
                Span { start: 0, end: 0 },
                format!("module header error: {msg}"),
            )]
        })?;
        timed_typecheck_phase(module.as_deref(), "process_imports", || {
            self.process_imports(program)
        })?;
        timed_typecheck_phase(module.as_deref(), "auto_load_referenced_modules", || {
            self.auto_load_referenced_modules(program)
        });
        self.resolution = timed_typecheck_phase(module.as_deref(), "resolve_names", || {
            crate::typechecker::resolve::resolve_names(
                program,
                &self.scope_map,
                self.current_module.as_deref(),
            )
        });
        timed_typecheck_phase(module.as_deref(), "register_definitions", || {
            self.register_definitions(program)
        })?;
        timed_typecheck_phase(module.as_deref(), "register_externals", || {
            self.register_externals(program)
        })?;
        let (annotations, annotation_constraints) =
            timed_typecheck_phase(module.as_deref(), "collect_annotations", || {
                self.collect_annotations(program)
            })?;
        let fun_vars = timed_typecheck_phase(module.as_deref(), "pre_bind_functions", || {
            self.pre_bind_functions(program, &annotations)
        });
        if let Err(errors) = timed_typecheck_phase(module.as_deref(), "register_all_impls", || {
            self.register_all_impls(program)
        }) {
            self.collected_diagnostics.extend(errors);
        }
        if let Err(e) = timed_typecheck_phase(module.as_deref(), "check_supertrait_impls", || {
            self.check_supertrait_impls()
        }) {
            self.collected_diagnostics.push(e);
        }

        // Main pass: group multi-clause function bindings, then check everything.
        // Collect errors instead of failing on the first one.
        let mut errors: Vec<Diagnostic> = Vec::new();
        timed_typecheck_phase(module.as_deref(), "body_pass", || {
            let mut i = 0;
            while i < program.len() {
                if let Decl::FunBinding { name, .. } = &program[i] {
                    // Collect all consecutive clauses with the same name
                    let name = name.clone();
                    let start = i;
                    while i < program.len() {
                        if let Decl::FunBinding { name: n, .. } = &program[i]
                            && *n == name
                        {
                            i += 1;
                            continue;
                        }
                        break;
                    }
                    let clauses: Vec<&Decl> = program[start..i].iter().collect();
                    let fun_var = fun_vars[&name].clone();
                    let annotation = match annotations.get(&name) {
                        Some((ty, span, row)) => FunctionAnnotation {
                            ty: Some(ty),
                            span: Some(*span),
                            effect_row: Some(row),
                        },
                        None => FunctionAnnotation {
                            ty: None,
                            span: None,
                            effect_row: None,
                        },
                    };
                    let where_cons = annotation_constraints
                        .get(&name)
                        .map(|v| v.as_slice())
                        .unwrap_or(&[]);
                    if let Err(e) =
                        self.check_fun_clauses(&name, &clauses, &fun_var, annotation, where_cons)
                    {
                        errors.push(e);
                        // Clear pending constraints for this function -- they may reference
                        // unresolved types from the error site and would produce cascading errors
                        self.trait_state.pending_constraints.clear();
                    }
                    // Drain any additional errors collected during block inference
                    let has_errors = self
                        .collected_diagnostics
                        .iter()
                        .any(|d| matches!(d.severity, crate::typechecker::Severity::Error));
                    if has_errors {
                        self.trait_state.pending_constraints.clear();
                    }
                    errors.extend(self.drain_errors());
                } else {
                    if let Err(e) = self.check_decl(&program[i]) {
                        errors.push(e);
                    }
                    errors.extend(self.drain_errors());
                    i += 1;
                }
            }
        });

        // Validate that `main` does not declare effects (it's the top of the call stack,
        // there is no caller above to provide handlers)
        timed_typecheck_phase(module.as_deref(), "validate_main", || {
            let main_effects: Vec<String> = self
                .env
                .get("main")
                .and_then(|s| innermost_effect_row(&self.sub.apply(&s.ty)))
                .map(|r| r.effects.iter().map(|e| e.name.clone()).collect())
                .unwrap_or_default();
            if !main_effects.is_empty() {
                // Prefer the signature's span, but `main` often has no explicit
                // signature (`main () = ...`); fall back to the binding's span so
                // the error lands on `main` rather than the module header.
                let span = program
                    .iter()
                    .find_map(|d| match d {
                        Decl::FunSignature { name, span, .. } if name == "main" => Some(*span),
                        _ => None,
                    })
                    .or_else(|| {
                        program.iter().find_map(|d| match d {
                            Decl::FunBinding { name, span, .. } if name == "main" => Some(*span),
                            _ => None,
                        })
                    });
                errors.push(Diagnostic::error_at(
                    span.unwrap_or(crate::token::Span { start: 0, end: 0 }),
                    format!(
                        "`main` cannot use `needs` -- it is the entry point and there is no caller to provide handlers for {{{}}}. Handle effects inside `main` using `with` instead.",
                        main_effects.join(", ")
                    ),
                ));
            }

            // Validate that `main` does not have unresolved trait constraints
            // (it is the entry point -- there is no caller to supply dictionaries)
            if let Some(scheme) = self.env.get("main")
                && !scheme.constraints.is_empty()
            {
                let traits: Vec<_> = scheme
                    .constraints
                    .iter()
                    .map(|(t, _, _)| t.as_str())
                    .collect();
                let span = program
                    .iter()
                    .find_map(|d| {
                        if let Decl::FunBinding { name, span, .. } = d
                            && name == "main"
                        {
                            Some(*span)
                        } else {
                            None
                        }
                    })
                    .unwrap_or(crate::token::Span { start: 0, end: 0 });
                errors.push(Diagnostic::error_at(
                    span,
                    format!(
                        "`main` cannot have unresolved trait constraints [{}] -- it is the entry point and there is no caller to supply dictionaries",
                        traits.join(", ")
                    ),
                ));
            }
        });

        // Check for annotations without a matching function binding
        // (skip @external and other bodyless annotations)
        timed_typecheck_phase(module.as_deref(), "check_bodyless_annotations", || {
            if !self.allow_bodyless_annotations {
                let bound_names: std::collections::HashSet<&str> = program
                    .iter()
                    .filter_map(|d| match d {
                        Decl::FunBinding { name, .. } => Some(name.as_str()),
                        _ => None,
                    })
                    .collect();
                let bodyless_names: std::collections::HashSet<&str> = program
                    .iter()
                    .filter_map(|d| match d {
                        Decl::FunSignature {
                            name,
                            annotations: ann,
                            ..
                        } if ann
                            .iter()
                            .any(|a| a.name == "external" || a.name == "builtin") =>
                        {
                            Some(name.as_str())
                        }
                        _ => None,
                    })
                    .collect();
                for (name, (_, span, _)) in &annotations {
                    if !bound_names.contains(name.as_str())
                        && !bodyless_names.contains(name.as_str())
                    {
                        errors.push(Diagnostic::error_at(
                            *span,
                            format!(
                                "type annotation for `{name}` has no matching function definition"
                            ),
                        ));
                    }
                }
            }
        });

        // Check all accumulated trait constraints now that types are resolved
        if let Err(e) =
            timed_typecheck_phase(module.as_deref(), "check_pending_constraints", || {
                self.check_pending_constraints()
            })
        {
            errors.push(e);
        }

        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors)
        }
    }

    pub(crate) fn check_decl(&mut self, decl: &Decl) -> Result<(), Diagnostic> {
        match decl {
            Decl::Let {
                id,
                name,
                name_span,
                annotation,
                value,
                span,
                ..
            } => {
                let ty = self.infer_expr(value)?;
                if let Some(ann) = annotation {
                    let ann_ty = self.convert_user_type_expr(ann, &mut vec![]);
                    self.unify_at(&ty, &ann_ty, *span)?;
                }
                let scheme = self.generalize(&ty);
                self.env.insert_with_def(name.clone(), scheme, *id);
                self.lsp.node_spans.insert(*id, *name_span);
                Ok(())
            }

            Decl::FunBinding { .. } => {
                // Multi-clause functions are handled in check_program
                Ok(())
            }

            Decl::HandlerDef { .. } => {
                self.register_handler(decl)?;
                Ok(())
            }

            // Imports are already processed in the early import pass
            Decl::Import { .. } => Ok(()),

            // Type annotations, type defs (already registered), effects, traits, impls,
            // module declarations -- skip
            _ => Ok(()),
        }
    }

    // --- check_program_inner passes ---

    /// Pass 1: Register type, record, effect, and trait definitions.
    /// Effects are registered in two sub-passes: stubs first (name + type params),
    /// then op signatures. This allows forward references between effects
    /// (e.g. Process referencing Actor in Std.Actor).
    pub(crate) fn register_definitions(
        &mut self,
        program: &[Decl],
    ) -> std::result::Result<(), Vec<Diagnostic>> {
        // Sub-pass 1a: types, records, effect stubs, traits
        for decl in program {
            match decl {
                Decl::TypeDef {
                    name,
                    type_params,
                    variants,
                    ..
                } => {
                    let plain_variants: Vec<_> = variants.iter().map(|a| &a.node).collect();
                    self.register_type_def(name, type_params, &plain_variants)
                        .map_err(|e| vec![e])?;
                }
                Decl::RecordDef {
                    id,
                    name,
                    type_params,
                    fields,
                    ..
                } => {
                    let plain_fields: Vec<_> = fields.iter().map(|a| &a.node).collect();
                    self.register_record_def(name, type_params, &plain_fields, *id)
                        .map_err(|e| vec![e])?;
                }
                Decl::EffectDef {
                    name, type_params, ..
                } => {
                    self.register_effect_stub(name, type_params);
                }
                Decl::TraitDef {
                    name,
                    type_params,
                    functional_dependency,
                    supertraits,
                    methods,
                    ..
                } => {
                    let plain_methods: Vec<_> = methods.iter().map(|a| &a.node).collect();
                    self.register_trait_def(
                        name,
                        type_params,
                        functional_dependency.as_ref(),
                        supertraits,
                        &plain_methods,
                    )
                    .map_err(|e| vec![e])?;
                }
                _ => {}
            }
        }
        // Sub-pass 1a': register type aliases — first pre-register their
        // arity and parameter kinds (so cross-alias references can
        // type-check), then cycle-check, then convert their bodies in
        // declaration order. `try_unfold_alias` chases transitively so
        // forward references between aliases resolve at use-sites.
        let aliases: Vec<&Decl> = program
            .iter()
            .filter(|d| matches!(d, Decl::TypeAlias { .. }))
            .collect();
        if !aliases.is_empty() {
            // Pre-register arity + kinds.
            for decl in &aliases {
                if let Decl::TypeAlias {
                    name, type_params, ..
                } = decl
                {
                    let canonical_name = match &self.current_module {
                        Some(module) => format!("{}.{}", module, name),
                        None => name.to_string(),
                    };
                    self.type_arity
                        .insert(canonical_name.clone(), type_params.len());
                    self.type_param_kinds
                        .insert(canonical_name, type_params.iter().map(|p| p.kind).collect());
                }
            }
            // Cycle check across the set of aliases in this module.
            self.detect_alias_cycles(&aliases)?;
            // Convert bodies.
            for decl in &aliases {
                if let Decl::TypeAlias {
                    name,
                    type_params,
                    body,
                    span,
                    ..
                } = decl
                {
                    self.register_type_alias(name, type_params, body, *span)
                        .map_err(|e| vec![e])?;
                }
            }
        }
        // Sub-pass 1b: fill in effect op signatures (all effect names now known)
        for decl in program {
            if let Decl::EffectDef {
                name,
                type_params,
                operations,
                ..
            } = decl
            {
                let plain_ops: Vec<_> = operations.iter().map(|a| &a.node).collect();
                self.register_effect_ops(name, type_params, &plain_ops)
                    .map_err(|e| vec![e])?;
            }
        }
        Ok(())
    }

    /// Pass 2: Process imports (before impls so imported traits are available).
    pub(crate) fn process_imports(
        &mut self,
        program: &[Decl],
    ) -> std::result::Result<(), Vec<Diagnostic>> {
        for decl in program {
            if let Decl::Import {
                module_path,
                alias,
                exposing,
                span,
                ..
            } = decl
            {
                let phase = format!("process_import:{}", module_path.join("."));
                let current_module = self.current_module.clone();
                timed_typecheck_phase(current_module.as_deref(), &phase, || {
                    self.typecheck_import(module_path, alias.as_deref(), exposing.as_ref(), *span)
                })
                .map_err(|e| vec![e])?;
            }
        }
        Ok(())
    }

    /// For every module referenced via `Module.name` (canonical form) without
    /// an explicit `import`, load the module's exports so its canonical keys
    /// are registered in `self.env`/`self.constructors`/etc. Bare and aliased
    /// scope entries are *not* injected — only the canonical form resolves.
    ///
    /// Unknown modules (typos, refs to nonexistent modules) are skipped here
    /// and fail at resolve/infer time with the existing diagnostic. Failures
    /// from loading a known module surface as collected diagnostics, with the
    /// span pointing at the user's first reference site.
    pub(crate) fn auto_load_referenced_modules(&mut self, program: &[Decl]) {
        let referenced = crate::typechecker::resolve::referenced_qualified_modules(program);
        for (module_name, ref_span) in &referenced {
            if self.modules.registered_canonical.contains(module_name) {
                continue;
            }
            let path: Vec<String> = module_name.split('.').map(str::to_string).collect();
            let known = crate::typechecker::check_module::builtin_module_source(&path).is_some()
                || self
                    .modules
                    .map
                    .as_ref()
                    .is_some_and(|m| m.contains_key(module_name));
            if !known {
                continue;
            }
            // load_module is idempotent — returns cached exports if already loaded.
            // register_module_canonical_exports uses entry().or_insert so it's
            // idempotent on the canonical-key side too.
            match self.load_module(&path, *ref_span) {
                Ok(exports) => {
                    self.register_module_canonical_exports(&exports, module_name, None, None);
                }
                Err(d) => self.collected_diagnostics.push(d),
            }
        }
    }

    /// Pass 3: Register external functions so they're available in impl bodies.
    pub(crate) fn register_externals(
        &mut self,
        program: &[Decl],
    ) -> std::result::Result<(), Vec<Diagnostic>> {
        for decl in program {
            if let Decl::FunSignature {
                name,
                params,
                return_type,
                effects,
                where_clause,
                annotations,
                span,
                ..
            } = decl
            {
                if !annotations.iter().any(|a| a.name == "external") {
                    continue;
                }
                let mut params_list: Vec<(String, u32)> = vec![];
                let mut fun_ty = self.convert_user_type_expr(return_type, &mut params_list);
                for (_, texpr) in params.iter().rev() {
                    let param_ty = self.convert_user_type_expr(texpr, &mut params_list);
                    fun_ty = Type::arrow(param_ty, fun_ty);
                }

                if !effects.is_empty() {
                    return Err(vec![Diagnostic::error_at(
                        *span,
                        format!(
                            "external function '{}' cannot declare effects with `needs` -- wrap it in a local function instead",
                            name
                        ),
                    )]);
                }

                let mut scheme_constraints = Vec::new();
                if !where_clause.is_empty() {
                    for bound in where_clause {
                        for tr in &bound.traits {
                            let resolved = self.resolved_trait_name_at(tr.id, &tr.name);
                            self.lsp.type_references.push((tr.span, resolved));
                        }
                        if let Some(var_id) = params_list
                            .iter()
                            .find(|(n, _)| *n == bound.type_var)
                            .map(|(_, id)| *id)
                        {
                            for tr in &bound.traits {
                                let resolved_trait = self.resolved_trait_name_at(tr.id, &tr.name);
                                self.validate_trait_bound_kind(
                                    &resolved_trait,
                                    &bound.type_var,
                                    var_id,
                                    tr.span,
                                )
                                .map_err(|e| vec![e])?;
                                let extra_types: Vec<Type> = tr
                                    .type_args
                                    .iter()
                                    .map(|te| self.convert_user_type_expr(te, &mut params_list))
                                    .collect();
                                scheme_constraints.push((resolved_trait, var_id, extra_types));
                            }
                        } else {
                            return Err(vec![Diagnostic::error_at(
                                *span,
                                format!(
                                    "where clause references unknown type variable '{}'",
                                    bound.type_var
                                ),
                            )]);
                        }
                    }
                }

                let mut scheme = self.generalize(&fun_ty);
                scheme.constraints = scheme_constraints;
                self.env.insert(name.clone(), scheme);
            }
        }
        Ok(())
    }

    /// Pass 4: Collect function annotations and their where clause constraints.
    /// Returns (annotations, annotation_constraints) maps.
    pub(crate) fn collect_annotations(
        &mut self,
        program: &[Decl],
    ) -> std::result::Result<Annotations, Vec<Diagnostic>> {
        let mut annotations: HashMap<String, (Type, Span, EffectRow)> = HashMap::new();
        let mut annotation_constraints: HashMap<String, Vec<(String, u32, Vec<Type>)>> =
            HashMap::new();

        for decl in program {
            if let Decl::FunSignature {
                id,
                public,
                name,
                name_span,
                params,
                return_type,
                effects,
                effect_row_var,
                where_clause,
                span,
                ..
            } = decl
            {
                let mut params_list: Vec<(String, u32)> = vec![];
                let return_ty = self.convert_user_type_expr(return_type, &mut params_list);
                let fun_effect_row = self
                    .build_effect_row_from_refs(effects, effect_row_var, &mut params_list)
                    .map_err(|e| vec![e])?;
                let param_types: Vec<Type> = params
                    .iter()
                    .map(|(_, texpr)| self.convert_user_type_expr(texpr, &mut params_list))
                    .collect();
                let fun_ty = self.function_type_with_innermost_effects(
                    &param_types,
                    return_ty,
                    fun_effect_row.clone(),
                );
                annotations.insert(
                    name.clone(),
                    (fun_ty.clone(), *span, fun_effect_row.clone()),
                );

                // Always register in known_funs (even pure functions) so the
                // `with` validation can distinguish local declarations
                // from imports/parameters.
                self.effect_meta.known_funs.insert(name.clone());
                if !effects.is_empty() {
                    let mut constraints = Vec::new();
                    for eff in effects {
                        self.record_effect_ref(eff);
                        if !eff.type_args.is_empty() {
                            let concrete_types: Vec<Type> =
                                self.convert_effect_ref_args(eff, &mut params_list);
                            // Use canonical effect name so lookups against
                            // canonical-only self.effects succeed later.
                            let canonical = self.resolved_effect_name(eff.id, &eff.name);
                            constraints.push((canonical, concrete_types));
                        }
                    }
                    if !constraints.is_empty() {
                        self.effect_meta
                            .fun_type_constraints
                            .insert(name.clone(), constraints);
                    }
                }

                if !where_clause.is_empty() {
                    let mut constraints = Vec::new();
                    for bound in where_clause {
                        for tr in &bound.traits {
                            let resolved = self.resolved_trait_name_at(tr.id, &tr.name);
                            self.lsp.type_references.push((tr.span, resolved));
                        }
                        if let Some(var_id) = params_list
                            .iter()
                            .find(|(n, _)| *n == bound.type_var)
                            .map(|(_, id)| *id)
                        {
                            self.trait_state
                                .where_bound_var_names
                                .insert(var_id, bound.type_var.clone());
                            for tr in &bound.traits {
                                let resolved_trait = self.resolved_trait_name_at(tr.id, &tr.name);
                                self.validate_trait_bound_kind(
                                    &resolved_trait,
                                    &bound.type_var,
                                    var_id,
                                    tr.span,
                                )
                                .map_err(|e| vec![e])?;
                                let extra_types: Vec<Type> = tr
                                    .type_args
                                    .iter()
                                    .map(|te| self.convert_user_type_expr(te, &mut params_list))
                                    .collect();
                                constraints.push((resolved_trait, var_id, extra_types));
                            }
                        } else {
                            return Err(vec![Diagnostic::error_at(
                                *span,
                                format!(
                                    "where clause references unknown type variable '{}'",
                                    bound.type_var
                                ),
                            )]);
                        }
                    }
                    annotation_constraints.insert(name.clone(), constraints);
                }

                let mut scheme = self.generalize(&fun_ty);
                if let Some(c) = annotation_constraints.get(name) {
                    scheme.constraints = c.clone();
                }
                self.env.insert_with_def(name.clone(), scheme, *id);
                self.lsp.node_spans.insert(*id, *name_span);
                self.lsp
                    .fun_definitions
                    .push((*id, name.clone(), *name_span, *public));

                // Stash the signature's named type vars so `check_fun_clauses`
                // can put them in scope for inline ascriptions inside the body.
                // Mirrors the impl-side fix in `register_impl`.
                if !params_list.is_empty() {
                    self.fun_type_param_vars
                        .insert(name.clone(), params_list.clone());
                }
            }
        }

        Ok((annotations, annotation_constraints))
    }

    /// Pass 5: Pre-bind all function names with fresh vars. This enables
    /// mutual recursion and lets trait/impl method bodies (checked in Pass 6)
    /// reference top-level zero-arity bindings declared anywhere in the module.
    pub(crate) fn pre_bind_functions(
        &mut self,
        program: &[Decl],
        annotations: &HashMap<String, (Type, Span, EffectRow)>,
    ) -> HashMap<String, Type> {
        let mut fun_vars: HashMap<String, Type> = HashMap::new();
        for decl in program {
            if let Decl::FunBinding {
                id,
                name,
                name_span,
                ..
            } = decl
            {
                // Link every FunBinding name to the FunSignature def_id so
                // LSP rename/references can find the implementation site(s).
                if let Some(sig_def_id) = self.env.def_id(name) {
                    self.record_reference(*id, *name_span, sig_def_id);
                }

                if fun_vars.contains_key(name) {
                    continue;
                }
                // Register all functions in known_funs (annotated ones are
                // already registered; un-annotated ones are added here).
                // This lets `with` validation distinguish local functions from imports.
                self.effect_meta.known_funs.insert(name.clone());
                if annotations.contains_key(name) {
                    let var = self.fresh_var();
                    fun_vars.insert(name.clone(), var);
                    continue;
                }
                let var = self.fresh_var();
                fun_vars.insert(name.clone(), var.clone());
                self.env.insert_with_def(
                    name.clone(),
                    Scheme {
                        forall: vec![],
                        constraints: vec![],
                        ty: var,
                    },
                    *id,
                );
                self.lsp.node_spans.insert(*id, *name_span);
                self.lsp
                    .fun_definitions
                    .push((*id, name.clone(), *name_span, false));
            }
        }
        fun_vars
    }

    /// Pass 6: Register trait impls.
    pub(crate) fn register_all_impls(
        &mut self,
        program: &[Decl],
    ) -> std::result::Result<(), Vec<Diagnostic>> {
        let mut errors: Vec<Diagnostic> = Vec::new();
        for decl in program {
            if let Decl::ImplDef {
                id,
                trait_name,
                trait_name_span,
                trait_type_args,
                target_type,
                target_type_span,
                target_type_expr,
                type_params,
                where_clause,
                where_apps,
                needs,
                methods,
                routed_derive_info,
                span,
                ..
            } = decl
            {
                // Record type references for the trait and target type names
                self.lsp
                    .type_references
                    .push((*trait_name_span, trait_name.clone()));
                self.lsp
                    .type_references
                    .push((*target_type_span, target_type.clone()));
                for eff in needs {
                    self.record_effect_ref(eff);
                }
                let plain_methods: Vec<_> = methods.iter().map(|a| a.node.clone()).collect();
                // Snapshot pending-constraint length before this impl's body
                // is checked. Anything added during the call belongs to this
                // impl; if it's a synthesized routed-derive impl, tag those
                // new constraints with the marker so failure diagnostics can
                // point back at the user's deriving clause.
                let before = self.trait_state.pending_constraints.len();
                let result = self.register_impl(
                    *id,
                    trait_name,
                    trait_type_args,
                    target_type,
                    type_params,
                    target_type_expr.as_ref(),
                    where_clause,
                    where_apps,
                    needs,
                    &plain_methods,
                    routed_derive_info.is_some(),
                    *span,
                );
                if let Some(info) = routed_derive_info {
                    let added: Vec<crate::ast::NodeId> = self
                        .trait_state
                        .pending_constraints
                        .iter()
                        .skip(before)
                        .map(|(_, _, _, _, nid)| *nid)
                        .collect();
                    for nid in added {
                        self.trait_state
                            .routed_constraint_origins
                            .insert(nid, info.clone());
                    }
                }
                if let Err(e) = result {
                    errors.push(e);
                }
            }
        }
        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors)
        }
    }
}
