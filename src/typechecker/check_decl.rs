use std::collections::HashMap;

use crate::ast::{self, Decl, ExprKind, Lit};

use super::result::CheckResult;
use super::{
    Checker, Diagnostic, EffectDefInfo, EffectEntry, EffectOpSig, EffectRow, HandlerInfo,
    RecordInfo, Scheme, Span, Type, find_effect_call,
};

/// Check if an expression is a compile-time inlineable value:
/// scalar literals, lists/tuples of inlineable values, constructors, or refs to other vals.
/// Note: list literals [1, 2, 3] are desugared to Cons/Nil chains before typechecking,
/// so we also accept Constructor and App(Constructor, ...) forms.
fn is_inlineable_expr(expr: &ast::Expr) -> bool {
    match &expr.kind {
        ExprKind::Lit { value, .. } => matches!(
            value,
            Lit::Int(..) | Lit::Float(..) | Lit::String(..) | Lit::Bool(..)
        ),
        ExprKind::ListLit { elements, .. } => elements.iter().all(is_inlineable_expr),
        ExprKind::Tuple { elements, .. } => elements.iter().all(is_inlineable_expr),
        ExprKind::Constructor { .. } => true, // Nil, True, etc.
        ExprKind::App { func, arg, .. } => is_inlineable_expr(func) && is_inlineable_expr(arg),
        ExprKind::Var { .. } => true, // reference to another val (validated at use site)
        ExprKind::UnaryMinus { expr: inner, .. } => is_inlineable_expr(inner),
        _ => false,
    }
}

/// Walk an arrow chain and return the EffectRow from the innermost Fun.
fn innermost_effect_row(ty: &Type) -> Option<EffectRow> {
    match ty {
        Type::Fun(_, ret, row) => innermost_effect_row(ret).or_else(|| Some(row.clone())),
        _ => None,
    }
}

/// Annotations collected from FunAnnotation declarations:
/// (name -> (type, span)) and (name -> where clause constraints).
type Annotations = (
    HashMap<String, (Type, Span)>,
    HashMap<String, Vec<(String, u32, Vec<Type>)>>,
);

impl Checker {
    // --- Top-level declarations ---

    /// Typecheck a program and return the public result.
    /// This is the main entry point for external callers.
    pub fn check_program(&mut self, program: &mut [Decl]) -> CheckResult {
        if let Err(errors) = self.check_program_inner(program) {
            for e in errors {
                self.collected_diagnostics.push(e);
            }
        }
        self.check_unused_functions();
        self.check_unused_variables();
        self.zonk_warnings();
        self.to_result()
    }

    /// Internal implementation of check_program.
    /// Returns Err for fatal errors that prevent further checking.
    /// Non-fatal diagnostics are accumulated in collected_diagnostics.
    pub(crate) fn check_program_inner(
        &mut self,
        program: &mut [Decl],
    ) -> std::result::Result<(), Vec<Diagnostic>> {
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

        // Add local type names to scope_map BEFORE register_definitions, so that
        // convert_type_expr can resolve local types during declaration registration.
        // Local types shadow imported types (use `insert`, not `or_insert`).
        for decl in program.iter() {
            let type_name = match decl {
                Decl::TypeDef { name, .. } | Decl::RecordDef { name, .. } => Some(name),
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
        self.process_imports(program)?;
        self.resolution =
            super::resolve::resolve_names(program, &self.scope_map, self.current_module.as_deref());
        self.register_definitions(program)?;
        self.register_externals(program)?;
        let (annotations, annotation_constraints) = self.collect_annotations(program)?;
        let fun_vars = self.pre_bind_functions(program, &annotations);
        if let Err(errors) = self.register_all_impls(program) {
            self.collected_diagnostics.extend(errors);
        }
        if let Err(e) = self.check_supertrait_impls() {
            self.collected_diagnostics.push(e);
        }

        // Main pass: group multi-clause function bindings, then check everything.
        // Collect errors instead of failing on the first one.
        let mut errors: Vec<Diagnostic> = Vec::new();
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
                let (annotation, annotation_span) = match annotations.get(&name).cloned() {
                    Some((ty, span)) => (Some(ty), Some(span)),
                    None => (None, None),
                };
                let where_cons = annotation_constraints
                    .get(&name)
                    .map(|v| v.as_slice())
                    .unwrap_or(&[]);
                if let Err(e) = self.check_fun_clauses(
                    &name,
                    &clauses,
                    &fun_var,
                    annotation.as_ref(),
                    annotation_span,
                    where_cons,
                ) {
                    errors.push(e);
                    // Clear pending constraints for this function -- they may reference
                    // unresolved types from the error site and would produce cascading errors
                    self.trait_state.pending_constraints.clear();
                }
                // Drain any additional errors collected during block inference
                let has_errors = self
                    .collected_diagnostics
                    .iter()
                    .any(|d| matches!(d.severity, super::Severity::Error));
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

        // Validate that `main` does not declare effects (it's the top of the call stack,
        // there is no caller above to provide handlers)
        let main_effects: Vec<String> = self
            .env
            .get("main")
            .and_then(|s| innermost_effect_row(&self.sub.apply(&s.ty)))
            .map(|r| r.effects.iter().map(|e| e.name.clone()).collect())
            .unwrap_or_default();
        if !main_effects.is_empty() {
            let span = program.iter().find_map(|d| {
                if let Decl::FunSignature { name, span, .. } = d
                    && name == "main"
                {
                    Some(*span)
                } else {
                    None
                }
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

        // Check for annotations without a matching function binding
        // (skip @external and other bodyless annotations)
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
            for (name, (_, span)) in &annotations {
                if !bound_names.contains(name.as_str()) && !bodyless_names.contains(name.as_str()) {
                    errors.push(Diagnostic::error_at(
                        *span,
                        format!("type annotation for `{name}` has no matching function definition"),
                    ));
                }
            }
        }

        // Check all accumulated trait constraints now that types are resolved
        if let Err(e) = self.check_pending_constraints() {
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

            Decl::Val {
                id,
                name,
                name_span,
                annotations,
                value,
                span,
                ..
            } => {
                let saved = self.save_effects();
                let ty = self.infer_expr(value)?;
                let accumulated = self.restore_effects(saved);

                // Val bindings must be pure (no effects)
                if !accumulated.is_empty() {
                    let err_span = find_effect_call(value).unwrap_or(*span);
                    return Err(Diagnostic::error_at(
                        err_span,
                        format!(
                            "'val' bindings must be pure (no effects), but '{}' uses effects",
                            name
                        ),
                    ));
                }

                // Val bindings cannot have function type
                let resolved = self.sub.apply(&ty);
                if matches!(resolved, Type::Fun(..)) {
                    return Err(Diagnostic::error_at(
                        *span,
                        "'val' bindings cannot have function type; use 'fun' to define functions instead".to_string(),
                    ));
                }

                // @inline vals must have compile-time inlineable RHS
                if annotations.iter().any(|a| a.name == "inline") && !is_inlineable_expr(value) {
                    return Err(Diagnostic::error_at(
                        *span,
                        format!(
                            "@inline val '{}' must have a compile-time literal value (scalar, list, or tuple of literals)",
                            name
                        ),
                    ));
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
    fn register_definitions(
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
                    supertraits,
                    methods,
                    ..
                } => {
                    let plain_methods: Vec<_> = methods.iter().map(|a| &a.node).collect();
                    self.register_trait_def(name, type_params, supertraits, &plain_methods)
                        .map_err(|e| vec![e])?;
                }
                _ => {}
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
    fn process_imports(&mut self, program: &[Decl]) -> std::result::Result<(), Vec<Diagnostic>> {
        for decl in program {
            if let Decl::Import {
                module_path,
                alias,
                exposing,
                span,
                ..
            } = decl
            {
                self.typecheck_import(module_path, alias.as_deref(), exposing.as_deref(), *span)
                    .map_err(|e| vec![e])?;
            }
        }
        Ok(())
    }

    /// Pass 3: Register external functions so they're available in impl bodies.
    fn register_externals(&mut self, program: &[Decl]) -> std::result::Result<(), Vec<Diagnostic>> {
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
    fn collect_annotations(
        &mut self,
        program: &[Decl],
    ) -> std::result::Result<Annotations, Vec<Diagnostic>> {
        let mut annotations: HashMap<String, (Type, Span)> = HashMap::new();
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
                let mut fun_ty = self.convert_user_type_expr(return_type, &mut params_list);

                // Build effect row from the function's `needs` clause.
                let fun_effect_row = if !effects.is_empty() || effect_row_var.is_some() {
                    let mut seen_effects: HashMap<String, Vec<Type>> = HashMap::new();
                    let mut effect_refs = Vec::new();
                    for e in effects {
                        let args: Vec<Type> = e
                            .type_args
                            .iter()
                            .map(|te| self.convert_user_type_expr(te, &mut params_list))
                            .collect();
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
                                return Err(vec![Diagnostic::error_at(
                                    e.span,
                                    format!(
                                        "conflicting effect requirements in `needs`: `{}` and `{}` both refer to `{}`, but with different type arguments",
                                        previous_display,
                                        current_display,
                                        e.name.rsplit('.').next().unwrap_or(&e.name),
                                    ),
                                )]);
                            }
                            continue;
                        }
                        seen_effects.insert(name.clone(), args.clone());
                        effect_refs.push(EffectEntry::unnamed(name, args));
                    }
                    let tail = effect_row_var.as_ref().map(|(rv_name, _)| {
                        let id =
                            if let Some((_, id)) = params_list.iter().find(|(n, _)| n == rv_name) {
                                *id
                            } else {
                                let id = self.next_var;
                                self.next_var += 1;
                                params_list.push((rv_name.clone(), id));
                                id
                            };
                        Box::new(Type::Var(id))
                    });
                    EffectRow {
                        effects: effect_refs,
                        tail,
                    }
                } else {
                    EffectRow::closed(vec![])
                };

                // Place effect row on the innermost arrow.
                let mut first_arrow = true;
                for (_, texpr) in params.iter().rev() {
                    let param_ty = self.convert_user_type_expr(texpr, &mut params_list);
                    if first_arrow {
                        fun_ty =
                            Type::Fun(Box::new(param_ty), Box::new(fun_ty), fun_effect_row.clone());
                    } else {
                        fun_ty = Type::arrow(param_ty, fun_ty);
                    }
                    first_arrow = false;
                }
                annotations.insert(name.clone(), (fun_ty.clone(), *span));

                // Always register in known_funs (even pure functions) so the
                // `with` validation can distinguish local declarations
                // from imports/parameters.
                self.effect_meta.known_funs.insert(name.clone());
                if !effects.is_empty() {
                    let mut constraints = Vec::new();
                    for eff in effects {
                        self.record_effect_ref(eff);
                        if !eff.type_args.is_empty() {
                            let concrete_types: Vec<Type> = eff
                                .type_args
                                .iter()
                                .map(|ta| self.convert_user_type_expr(ta, &mut params_list))
                                .collect();
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
            }
        }

        Ok((annotations, annotation_constraints))
    }

    /// Pass 5: Pre-bind all function names with fresh vars (enables mutual recursion).
    fn pre_bind_functions(
        &mut self,
        program: &[Decl],
        annotations: &HashMap<String, (Type, Span)>,
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
    fn register_all_impls(&mut self, program: &[Decl]) -> std::result::Result<(), Vec<Diagnostic>> {
        let mut errors: Vec<Diagnostic> = Vec::new();
        for decl in program {
            if let Decl::ImplDef {
                id,
                trait_name,
                trait_name_span,
                trait_type_args,
                target_type,
                target_type_span,
                type_params,
                where_clause,
                needs,
                methods,
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
                let resolved_trait_type_args: Vec<String> = trait_type_args
                    .iter()
                    .map(|te| self.resolved_type_name(te.id(), te.simple_name()))
                    .collect();
                if let Err(e) = self.register_impl(
                    *id,
                    trait_name,
                    &resolved_trait_type_args,
                    target_type,
                    type_params,
                    where_clause,
                    needs,
                    &plain_methods,
                    *span,
                ) {
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

    /// Check a group of function clauses that share the same name.
    /// Handles recursion (pre-binds name) and multi-clause pattern matching.
    pub(crate) fn check_fun_clauses(
        &mut self,
        name: &str,
        clauses: &[&Decl],
        fun_var: &Type,
        annotation: Option<&Type>,
        annotation_span: Option<Span>,
        where_constraints: &[(String, u32, Vec<Type>)],
    ) -> Result<(), Diagnostic> {
        // All clauses must have the same arity
        let arity = match clauses[0] {
            Decl::FunBinding { params, .. } => params.len(),
            _ => unreachable!(),
        };

        let result_ty = self.fresh_var();
        let param_types: Vec<Type> = (0..arity).map(|_| self.fresh_var()).collect();

        // If there's a type annotation, unify param/result types with it upfront
        // so annotation constraints guide inference (important for polymorphic recursion).
        // Also unify the pre-bound var so recursive calls see the correct type.
        if let Some(ann_ty) = annotation {
            let mut ann_current = ann_ty.clone();
            // Collect effect rows from each arrow in the annotation so we can
            // preserve them in the pre-type (including row variables like ..e).
            let mut ann_effect_rows = Vec::new();
            for param_ty in &param_types {
                match ann_current {
                    Type::Fun(ann_param, ann_ret, ann_row) => {
                        self.unify(param_ty, &ann_param)?;
                        ann_effect_rows.push(ann_row);
                        ann_current = *ann_ret;
                    }
                    _ => break,
                }
            }
            self.unify(&result_ty, &ann_current)?;

            // Build the function type from annotation-constrained params and unify
            // with pre-bound var. Use the annotation's effect rows to preserve row
            // variables (..e) instead of creating pure arrows that would cause the
            // row variable to be bound to empty during later unification.
            let mut pre_ty = result_ty.clone();
            for (i, param_ty) in param_types.iter().rev().enumerate() {
                let row_idx = param_types.len() - 1 - i;
                if let Some(row) = ann_effect_rows.get(row_idx) {
                    pre_ty = Type::Fun(Box::new(param_ty.clone()), Box::new(pre_ty), row.clone());
                } else {
                    pre_ty = Type::arrow(param_ty.clone(), pre_ty);
                }
            }
            self.unify(fun_var, &pre_ty)?;
        }

        // Register where clause bounds on type variable IDs
        for (trait_name, var_id, _extra_var_ids) in where_constraints {
            self.trait_state
                .where_bounds
                .entry(*var_id)
                .or_default()
                .insert(trait_name.clone());
        }

        // Snapshot pending constraints so we can partition new ones after body checking
        let constraints_before = self.trait_state.pending_constraints.len();
        let mut returned_handler_info: Option<super::HandlerInfo> = None;

        // Save and clear effect tracking and field candidate tracking for this function body
        let body_scope = self.enter_scope();

        // Pre-populate effect type param cache from annotation constraints (e.g. needs {State Int})
        if let Some(constraints) = self.effect_meta.fun_type_constraints.get(name).cloned() {
            for (effect_name, concrete_types) in &constraints {
                if let Some(info) = self.effects.get(effect_name).cloned() {
                    let mapping: std::collections::HashMap<u32, Type> = info
                        .type_params
                        .iter()
                        .zip(concrete_types.iter())
                        .map(|(&param_id, ty)| (param_id, ty.clone()))
                        .collect();
                    self.effect_meta
                        .type_param_cache
                        .insert(effect_name.clone(), mapping);
                }
            }
        }

        // Save effects and start fresh for this function body
        let saved_absorbed = std::mem::take(&mut self.call_site_absorbed);
        let saved_effs = self.save_effects();
        for clause in clauses {
            let Decl::FunBinding {
                params,
                guard,
                body,
                span,
                ..
            } = clause
            else {
                unreachable!()
            };

            if params.len() != arity {
                return Err(Diagnostic::error_at(
                    *span,
                    format!(
                        "clause for '{}' has {} params, expected {}",
                        name,
                        params.len(),
                        arity
                    ),
                ));
            }

            let saved_env = self.env.clone();
            let saved_handlers = self.handlers.clone();

            for (pat, ty) in params.iter().zip(param_types.iter()) {
                self.bind_pattern(pat, ty)?;
            }

            if let Some(guard) = guard {
                if let Some(span) = super::find_effect_call(guard) {
                    return Err(Diagnostic::error_at(
                        span,
                        "Effect calls are not allowed in guard expressions".to_string(),
                    ));
                }
                let guard_saved = self.save_effects();
                let guard_ty = self.infer_expr(guard)?;
                self.restore_effects(guard_saved);
                self.unify_at(&guard_ty, &Type::bool(), guard.span)?;
            }

            let body_ty = if annotation.is_some() {
                self.infer_expr_against(body, &result_ty)?
            } else {
                self.infer_expr(body)?
            };
            if returned_handler_info.is_none() {
                returned_handler_info = self.extract_handler_info(body);
            }
            self.unify_at(&result_ty, &body_ty, body.span)?;

            self.env = saved_env;
            self.handlers = saved_handlers;
        }
        // Collect accumulated effects and restore outer scope
        let raw_all_body_effs = self.restore_effects(saved_effs);
        let all_body_effs = self.sub.apply_effect_row(&raw_all_body_effs);

        // Absorption (boundary half): when a function directly calls a callback
        // parameter like `f ()` in `run_state init f = (f (), init)`, the callee's
        // effect row is emitted to the accumulator. But those effects belong to the
        // *caller* of run_state, not run_state itself. We subtract effects declared
        // on any callback parameter types.
        //
        // There is a second absorption site in infer.rs App (call-site half) that
        // handles the inverse case: passing a lambda to a HOF like `try_it (fun () -> ...)`.
        // Both are needed because they fire at different points in inference:
        // - Call-site: lambda effects propagate immediately during lambda inference,
        //   before the boundary runs. Only the App knows the HOF's parameter type.
        // - Boundary: direct callback calls emit effects from the callee's type.
        //   Only the boundary knows which params are callback parameters.
        let mut absorbed = std::collections::HashSet::new();
        for pt in &param_types {
            let resolved = self.sub.apply(pt);
            super::collect_callback_effects(&resolved, &mut absorbed);
        }
        // Collect row variable IDs from callback parameters' open effect rows.
        // These represent unknown effects that must be propagated via `needs`.
        let mut callback_row_vars = std::collections::HashSet::new();
        for pt in &param_types {
            let resolved = self.sub.apply(pt);
            fn collect_row_vars(ty: &Type, out: &mut std::collections::HashSet<u32>) {
                if let Type::Fun(_, ret, row) = ty {
                    if let Some(tail) = &row.tail
                        && let Type::Var(id) = tail.as_ref()
                    {
                        out.insert(*id);
                    }
                    collect_row_vars(ret, out);
                }
            }
            collect_row_vars(&resolved, &mut callback_row_vars);
        }
        // Effects declared on a callback parameter must be handled by the HOF:
        // either via an internal `with` block (in which case they were already
        // subtracted from `all_body_effs` during `with` inference) or by
        // declaring them in the function's own `needs` row (forward to caller).
        // Without either, the lowerer has no source for the handler at the
        // point the callback is invoked. Detect this here so the user gets a
        // typechecker error instead of a codegen ICE.
        if let Some(ann) = annotation {
            let declared_row_for_check =
                innermost_effect_row(&self.sub.apply(ann)).unwrap_or_else(EffectRow::empty);
            let declared_names: std::collections::HashSet<String> = declared_row_for_check
                .effects
                .iter()
                .map(|e| e.name.clone())
                .collect();
            let mut unhandled: Vec<String> = absorbed
                .iter()
                .filter(|eff| {
                    all_body_effs.effects.iter().any(|e| &e.name == *eff)
                        && !declared_names.contains(*eff)
                })
                .cloned()
                .collect();
            if !unhandled.is_empty() {
                unhandled.sort();
                let err_span = annotation_span.unwrap_or_else(|| match clauses[0] {
                    Decl::FunBinding { span, .. } => *span,
                    _ => unreachable!(),
                });
                return Err(Diagnostic::error_at(
                    err_span,
                    format!(
                        "`{}` calls a callback parameter whose declared effect{} {{{}}} {} not handled; \
                         either wrap the callback call in `with`, or add `needs {{{}}}` to the annotation \
                         to forward the effect{} to the caller",
                        name,
                        if unhandled.len() == 1 { "" } else { "s" },
                        unhandled.join(", "),
                        if unhandled.len() == 1 { "is" } else { "are" },
                        unhandled.join(", "),
                        if unhandled.len() == 1 { "" } else { "s" },
                    ),
                ));
            }
        }

        let all_body_effs = if absorbed.is_empty() {
            all_body_effs
        } else {
            self.call_site_absorbed.extend(absorbed.iter().cloned());
            all_body_effs.subtract(&absorbed)
        };

        // Check exhaustiveness of function clause patterns (multi-column Maranget)
        if clauses.len() > 1
            || clauses.iter().any(|c| {
                if let Decl::FunBinding { params, .. } = c {
                    params.iter().any(|p| {
                        !matches!(
                            p,
                            crate::ast::Pat::Var { .. } | crate::ast::Pat::Wildcard { .. }
                        )
                    })
                } else {
                    false
                }
            })
        {
            self.check_fun_exhaustiveness(name, clauses, &param_types)?;
        }

        // Check effect requirements against declared needs via row comparison.
        // all_body_effs was accumulated on self.effect_row during body inference.
        let scope_result = self.exit_scope(body_scope);
        let body_field_candidates = scope_result.field_candidates;

        let declared_row = annotation
            .and_then(|ann| innermost_effect_row(&self.sub.apply(ann)))
            .unwrap_or_else(EffectRow::empty);

        // A callback parameter with an open effect row (..e) represents
        // unknown effects that can't be handled with `with` — they must be
        // propagated via `needs {..e}` on the function's own annotation,
        // and the row variable must be the SAME one (connected).
        if annotation.is_some() && !callback_row_vars.is_empty() {
            // Check: the declared row must have an open tail whose variable
            // resolves to the same root as one of the callback row variables.
            let propagates = declared_row.tail.as_ref().is_some_and(|t| {
                let decl_resolved = self.sub.apply(t);
                callback_row_vars.iter().any(|&cb_id| {
                    let cb_resolved = self.sub.apply(&Type::Var(cb_id));
                    decl_resolved == cb_resolved
                })
            });
            if !propagates {
                let err_span = annotation_span.unwrap_or_else(|| match clauses[0] {
                    Decl::FunBinding { span, .. } => *span,
                    _ => unreachable!(),
                });
                return Err(Diagnostic::error_at(
                    err_span,
                    format!(
                        "`{}` accepts callback with open effect row but does not propagate effects; \
                         add `needs {{..e}}` to the annotation",
                        name,
                    ),
                ));
            }
        }

        if !all_body_effs.is_empty() || !declared_row.is_empty() {
            let err_span = match clauses[0] {
                Decl::FunBinding { span, .. } => *span,
                _ => unreachable!(),
            };
            self.check_effects_via_row(
                &all_body_effs,
                &declared_row,
                &format!("function '{}'", name),
                err_span,
            )?;

            // Check for effects declared but never used.
            // Effects that were absorbed during call-site HOF absorption (e.g. Actor
            // on spawn!) are excluded: absorption proves the effect was needed in scope
            // even though it no longer appears in the accumulator.
            let body_effect_names: std::collections::HashSet<String> = all_body_effs
                .effects
                .iter()
                .map(|e| e.name.clone())
                .collect();
            let declared_effects: std::collections::HashSet<String> = declared_row
                .effects
                .iter()
                .map(|e| e.name.clone())
                .collect();
            let unused: Vec<_> = declared_effects
                .difference(&body_effect_names)
                .filter(|name| !self.call_site_absorbed.contains(*name))
                .collect();
            if !unused.is_empty() {
                let span = annotation_span.expect("unused effects implies annotation exists");
                let mut effects: Vec<_> = unused.into_iter().cloned().collect();
                effects.sort();
                self.pending_warnings
                    .push(super::PendingWarning::UnusedEffects {
                        span,
                        fun_name: name.to_string(),
                        effects,
                    });
            }
        }

        // Restore call_site_absorbed for outer scope
        self.call_site_absorbed = saved_absorbed;

        // Check for unresolved ambiguous field accesses. Any var still in field_candidates
        // after the full body was checked is genuinely ambiguous -- the programmer needs
        // to add a type annotation to disambiguate.
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

        if let Some(info) = returned_handler_info {
            self.handler_funs.insert(name.to_string(), info);
        } else {
            self.handler_funs.remove(name);
        }

        // Build curried function type. Effect row comes from:
        // 1. The annotation's EffectRow (for annotated functions)
        // 2. The inferred body effects (for unannotated functions)
        // 3. Empty row (for pure functions)
        let mut fun_ty = result_ty;
        let effect_row = annotation
            .and_then(|ann| innermost_effect_row(&self.sub.apply(ann)))
            .or_else(|| {
                if all_body_effs.is_empty() {
                    None
                } else {
                    Some(all_body_effs.clone())
                }
            });
        let mut first_arrow = true;
        for param_ty in param_types.into_iter().rev() {
            if first_arrow {
                if let Some(ref row) = effect_row {
                    fun_ty = Type::Fun(Box::new(param_ty), Box::new(fun_ty), row.clone());
                } else {
                    fun_ty = Type::arrow(param_ty, fun_ty);
                }
            } else {
                fun_ty = Type::arrow(param_ty, fun_ty);
            }
            first_arrow = false;
        }

        // Unify with the pre-bound variable (resolves recursive uses)
        self.unify(fun_var, &fun_ty)?;

        // Check against type annotation if present
        if let Some(ann_ty) = annotation {
            self.unify(&fun_ty, ann_ty).map_err(|e| {
                let span = match clauses[0] {
                    Decl::FunBinding { span, .. } => *span,
                    _ => unreachable!(),
                };
                Diagnostic::error_at(
                    span,
                    format!("type annotation mismatch for '{}': {}", name, e.message),
                )
            })?;
        }

        // Zero-param bindings only make sense as eta-reduced function values
        // (e.g. `add_five = add 5` where the body has type `Int -> Int`). When
        // the body is a non-function value, the user wrote a constant under
        // `fun`-binding syntax and should use `val` instead. The parser cannot
        // distinguish these cases up-front because the body is typechecked here.
        if arity == 0 && !matches!(self.sub.apply(&fun_ty), Type::Fun(_, _, _)) {
            let span = match clauses[0] {
                Decl::FunBinding { span, .. } => *span,
                _ => unreachable!(),
            };
            return Err(Diagnostic::error_at(
                span,
                format!(
                    "`{name}` has no parameters and its body is not a function; use `val {name} = ...` for constants"
                ),
            ));
        }

        let scheme = self.build_fun_scheme(
            name,
            fun_ty,
            constraints_before,
            annotation.is_some(),
            where_constraints,
        )?;
        self.env.insert(name.into(), scheme);
        Ok(())
    }

    /// Look up the source-level type variable name for a resolved type var ID.
    /// `where_bound_var_names` is keyed by original (pre-substitution) var IDs,
    /// so we resolve each bound ID through substitution to find the match.
    fn resolve_where_var_name(&self, trait_name: &str, resolved_id: u32) -> Option<String> {
        self.trait_state
            .where_bounds
            .iter()
            .find_map(|(bound_id, traits)| {
                if traits.contains(trait_name) {
                    match self.sub.apply(&Type::Var(*bound_id)) {
                        Type::Var(r) if r == resolved_id => self
                            .trait_state
                            .where_bound_var_names
                            .get(bound_id)
                            .cloned(),
                        _ => None,
                    }
                } else {
                    None
                }
            })
            .or_else(|| {
                self.trait_state
                    .where_bound_var_names
                    .get(&resolved_id)
                    .cloned()
            })
    }

    /// Partition pending constraints into scheme-level (polymorphic) vs global
    /// (concrete), then generalize the function type into a scheme with constraints.
    fn build_fun_scheme(
        &mut self,
        name: &str,
        fun_ty: Type,
        constraints_before: usize,
        has_annotation: bool,
        where_constraints: &[(String, u32, Vec<Type>)],
    ) -> Result<Scheme, Diagnostic> {
        let new_constraints = self
            .trait_state
            .pending_constraints
            .split_off(constraints_before);

        // Collect type vars that appear in the function's type (used for
        // phantom detection and ambiguous-variable checks below).
        let mut type_vars = Vec::new();
        super::collect_free_vars(&self.sub.apply(&fun_ty), &mut type_vars);

        let mut scheme_constraints: Vec<(String, u32, Span)> = Vec::new();
        for (trait_name, trait_type_arg_types, ty, span, node_id) in new_constraints {
            let resolved = self.sub.apply(&ty);
            match resolved {
                Type::Var(id) => {
                    // Check where_bounds, resolving bound var IDs through
                    // substitution so they match after annotation unification.
                    let in_where =
                        self.trait_state
                            .where_bounds
                            .iter()
                            .any(|(bound_id, traits)| {
                                traits.contains(&trait_name)
                                    && match self.sub.apply(&Type::Var(*bound_id)) {
                                        Type::Var(resolved) => resolved == id,
                                        _ => false,
                                    }
                            });
                    if in_where {
                        let var_name = self.resolve_where_var_name(&trait_name, id);
                        self.evidence.push(super::TraitEvidence {
                            node_id,
                            trait_name: trait_name.clone(),
                            resolved_type: None,
                            type_var_name: var_name,
                            trait_type_args: trait_type_arg_types.clone(),
                        });
                        continue;
                    }

                    // Phantom constraint matching: if the constraint var doesn't
                    // appear in the function's type, it's from a trait method with
                    // phantom type params. Match against the function's own
                    // where-constraints (local, not global where_bounds) to connect
                    // the phantom var to the caller's type system.
                    if !type_vars.contains(&id) {
                        let matched = where_constraints
                            .iter()
                            .find(|(wc_trait, _, _)| *wc_trait == trait_name);
                        if let Some((_, wc_var_id, wc_extras)) = matched {
                            let wc_resolved = self.sub.apply(&Type::Var(*wc_var_id));
                            self.unify_at(&Type::Var(id), &wc_resolved, span)?;
                            // Unify extra type args pairwise
                            for (phantom_extra, where_extra) in
                                trait_type_arg_types.iter().zip(wc_extras.iter())
                            {
                                let pe = self.sub.apply(phantom_extra);
                                let we = self.sub.apply(where_extra);
                                self.unify_at(&pe, &we, span)?;
                            }
                            let resolved_id = match self.sub.apply(&Type::Var(id)) {
                                Type::Var(rid) => rid,
                                _ => id,
                            };
                            let var_name = self.resolve_where_var_name(&trait_name, resolved_id);
                            self.evidence.push(super::TraitEvidence {
                                node_id,
                                trait_name: trait_name.clone(),
                                resolved_type: None,
                                type_var_name: var_name,
                                trait_type_args: trait_type_arg_types.clone(),
                            });
                            continue;
                        }
                    }

                    if has_annotation {
                        return Err(Diagnostic::error_at(
                            span,
                            format!(
                                "trait {} required but not declared in where clause for '{}'",
                                trait_name, name
                            ),
                        ));
                    }
                    // Record evidence for inferred constraints too, so the
                    // elaborator can resolve trait method calls (DictMethodAccess).
                    let var_name = self.resolve_where_var_name(&trait_name, id);
                    self.evidence.push(super::TraitEvidence {
                        node_id,
                        trait_name: trait_name.clone(),
                        resolved_type: None,
                        type_var_name: var_name,
                        trait_type_args: trait_type_arg_types.clone(),
                    });
                    scheme_constraints.push((trait_name, id, span));
                }
                _ => {
                    self.trait_state.pending_constraints.push((
                        trait_name,
                        trait_type_arg_types,
                        ty,
                        span,
                        node_id,
                    ));
                }
            }
        }

        self.env.remove(name);
        let mut scheme = self.generalize(&fun_ty);

        for (trait_name, var_id, extra_types) in where_constraints {
            let resolved_id = match self.sub.apply(&Type::Var(*var_id)) {
                Type::Var(id) => id,
                _ => continue,
            };
            if scheme.forall.contains(&resolved_id) {
                let resolved_extras: Vec<Type> =
                    extra_types.iter().map(|ty| self.sub.apply(ty)).collect();
                scheme
                    .constraints
                    .push((trait_name.clone(), resolved_id, resolved_extras));
            }
        }

        for (trait_name, var_id, span) in scheme_constraints {
            if !type_vars.contains(&var_id) {
                let display = trait_name.rsplit('.').next().unwrap_or(&trait_name);
                return Err(Diagnostic::error_at(
                    span,
                    format!(
                        "ambiguous type variable requires {} but has no concrete type in '{}'",
                        display, name
                    ),
                ));
            }
            if scheme.forall.contains(&var_id)
                && !scheme
                    .constraints
                    .iter()
                    .any(|(t, v, _)| t == &trait_name && *v == var_id)
            {
                // Inferred constraints (from operators) are always single-param traits.
                // Multi-param constraints only enter through where clauses (handled above).
                scheme.constraints.push((trait_name, var_id, vec![]));
            }
        }

        Ok(scheme)
    }

    /// Check exhaustiveness of multi-clause function patterns using Maranget.
    fn check_fun_exhaustiveness(
        &self,
        name: &str,
        clauses: &[&Decl],
        param_types: &[Type],
    ) -> Result<(), Diagnostic> {
        use super::exhaustiveness::{self as exh, ExhaustivenessCtx, SPat};

        // Only check if at least one param resolves to a known ADT or Tuple
        let resolved_types: Vec<_> = param_types.iter().map(|t| self.sub.apply(t)).collect();
        let has_adt_param = resolved_types.iter().any(|t| match t {
            Type::Con(name, _) => {
                self.adt_variants.contains_key(name)
                    || name == super::canonicalize_type_name("Tuple")
            }
            _ => false,
        });
        if !has_adt_param {
            return Ok(());
        }

        let ctx = ExhaustivenessCtx {
            adt_variants: &self.adt_variants,
        };
        let sctx = self.simplify_ctx();

        // Build pattern matrix: one row per clause, one column per param
        let mut matrix: Vec<Vec<SPat>> = Vec::new();

        for clause in clauses {
            let Decl::FunBinding {
                params,
                guard,
                span,
                ..
            } = clause
            else {
                unreachable!()
            };

            let row: Vec<SPat> = params
                .iter()
                .enumerate()
                .map(|(i, p)| exh::simplify_pat(p, resolved_types.get(i), &sctx))
                .collect();

            // Redundancy check
            if guard.is_none() && !exh::useful(&ctx, &matrix, &row) {
                return Err(Diagnostic::error_at(
                    *span,
                    format!(
                        "unreachable clause for '{}': all cases already covered",
                        name
                    ),
                ));
            }

            if guard.is_none() {
                matrix.push(row);
            }
        }

        // Exhaustiveness check
        let wildcard_row: Vec<SPat> = (0..param_types.len()).map(|_| SPat::Wildcard).collect();
        if exh::useful(&ctx, &matrix, &wildcard_row) {
            let witnesses = exh::find_all_witnesses(&ctx, &matrix, param_types.len());
            let span = match clauses[0] {
                Decl::FunBinding { span, .. } => *span,
                _ => unreachable!(),
            };
            if !witnesses.is_empty() {
                let formatted: Vec<String> =
                    witnesses.iter().map(|w| exh::format_witness(w)).collect();
                return Err(Diagnostic::error_at(
                    span,
                    format!(
                        "non-exhaustive clauses for '{}': missing {}",
                        name,
                        formatted.join(", ")
                    ),
                ));
            }
            return Err(Diagnostic::error_at(
                span,
                format!("non-exhaustive clauses for '{}'", name),
            ));
        }

        Ok(())
    }

    // --- Registration helpers ---

    pub(crate) fn register_type_def(
        &mut self,
        name: &str,
        type_params: &[String],
        variants: &[&ast::TypeConstructor],
    ) -> Result<(), Diagnostic> {
        // Create fresh type variables for the type parameters
        let mut param_vars: Vec<(String, u32)> = type_params
            .iter()
            .map(|p| {
                let var = self.next_var;
                self.next_var += 1;
                (p.clone(), var)
            })
            .collect();

        // Canonical type name: "Module.TypeName" for module types, bare for non-module.
        // Don't apply builtin canonicalization here — a locally-defined "Maybe" is NOT
        // the stdlib Std.Maybe.Maybe.
        let canonical_name = match &self.current_module {
            Some(module) => format!("{}.{}", module, name),
            None => name.to_string(),
        };

        let result_type = Type::Con(
            canonical_name.clone(),
            param_vars.iter().map(|(_, id)| Type::Var(*id)).collect(),
        );

        let forall: Vec<u32> = param_vars.iter().map(|(_, id)| *id).collect();

        for variant in variants {
            let ctor_ty = if variant.fields.is_empty() {
                result_type.clone()
            } else {
                // Build: field1 -> field2 -> ... -> ResultType
                let mut ty = result_type.clone();
                for (_, field) in variant.fields.iter().rev() {
                    let field_ty = self.convert_user_type_expr(field, &mut param_vars);
                    ty = Type::arrow(field_ty, ty);
                }
                ty
            };

            self.constructors.insert(
                variant.name.clone(),
                Scheme {
                    forall: forall.clone(),
                    constraints: vec![],
                    ty: ctor_ty,
                },
            );
            self.lsp
                .constructor_def_ids
                .insert(variant.name.clone(), variant.id);
            self.lsp.node_spans.insert(variant.id, variant.span);
        }

        self.adt_variants.insert(
            canonical_name.clone(),
            variants
                .iter()
                .map(|v| (v.name.clone(), v.fields.len()))
                .collect(),
        );

        self.type_arity.insert(canonical_name, type_params.len());

        Ok(())
    }

    pub(crate) fn register_record_def(
        &mut self,
        name: &str,
        type_params: &[String],
        fields: &[&(String, ast::TypeExpr)],
        def_id: crate::ast::NodeId,
    ) -> Result<(), Diagnostic> {
        // Create fresh type variables for declared type parameters (same as register_type_def)
        let mut param_vars: Vec<(String, u32)> = type_params
            .iter()
            .map(|p| {
                let var = self.next_var;
                self.next_var += 1;
                (p.clone(), var)
            })
            .collect();

        let field_types: Vec<(String, Type)> = fields
            .iter()
            .map(|(fname, texpr)| {
                (
                    fname.clone(),
                    self.convert_user_type_expr(texpr, &mut param_vars),
                )
            })
            .collect();

        let forall: Vec<u32> = param_vars.iter().map(|(_, id)| *id).collect();

        // Canonical type name: "Module.TypeName" for module types, bare for non-module.
        let canonical_name = match &self.current_module {
            Some(module) => format!("{}.{}", module, name),
            None => name.to_string(),
        };

        // Build result type: e.g. Box a -> Con("MyMod.Box", [Var(a_id)])
        let result_type = Type::Con(
            canonical_name.clone(),
            forall.iter().map(|&id| Type::Var(id)).collect(),
        );

        // Register record constructor scheme: e.g. Box : forall a. a -> Box a
        // Constructor takes fields in order, returns the record type.
        let mut ctor_ty = result_type;
        for (_, field_ty) in field_types.iter().rev() {
            ctor_ty = Type::arrow(field_ty.clone(), ctor_ty);
        }
        self.constructors.insert(
            name.into(),
            Scheme {
                forall: forall.clone(),
                constraints: vec![],
                ty: ctor_ty,
            },
        );
        self.lsp.constructor_def_ids.insert(name.into(), def_id);

        let num_fields = field_types.len();
        self.records.insert(
            canonical_name.clone(),
            RecordInfo {
                type_params: forall,
                fields: field_types,
            },
        );
        // Register as a single-constructor ADT for exhaustiveness checking
        self.adt_variants
            .insert(canonical_name.clone(), vec![(name.into(), num_fields)]);
        self.type_arity.insert(canonical_name, type_params.len());
        Ok(())
    }

    /// Phase 1: Register effect name and type params (stub with empty ops).
    /// Called first for ALL effects so that forward references between effects
    /// (e.g. Process referencing Actor) resolve during op signature processing.
    pub(crate) fn register_effect_stub(&mut self, name: &str, effect_type_params: &[String]) {
        let mut type_param_ids = Vec::new();
        for _tp in effect_type_params {
            let var = self.fresh_var();
            let id = match &var {
                Type::Var(id) => *id,
                _ => unreachable!(),
            };
            type_param_ids.push(id);
        }
        let key = if let Some(module) = &self.current_module {
            format!("{}.{}", module, name)
        } else {
            name.into()
        };
        self.effects.insert(
            key,
            EffectDefInfo {
                type_params: type_param_ids,
                ops: vec![],
                op_spans: std::collections::HashMap::new(),
                source_module: self.current_module.clone(),
            },
        );
        self.type_arity
            .insert(name.into(), effect_type_params.len());
        if let Some(module) = &self.current_module {
            self.type_arity
                .insert(format!("{}.{}", module, name), effect_type_params.len());
        }
    }

    /// Phase 2: Fill in effect op signatures (after all effect stubs are registered).
    pub(crate) fn register_effect_ops(
        &mut self,
        name: &str,
        effect_type_params: &[String],
        operations: &[&ast::EffectOp],
    ) -> Result<(), Diagnostic> {
        let key = if let Some(module) = &self.current_module {
            format!("{}.{}", module, name)
        } else {
            name.to_string()
        };
        // Retrieve the type param IDs created during stub registration.
        let type_param_ids = self
            .effects
            .get(&key)
            .map(|info| info.type_params.clone())
            .unwrap_or_default();

        let shared_params: Vec<(String, u32)> = effect_type_params
            .iter()
            .zip(type_param_ids.iter())
            .map(|(tp, &id)| (tp.clone(), id))
            .collect();

        let mut ops = Vec::new();
        let mut op_spans = std::collections::HashMap::new();
        for op in operations {
            let mut params_list = shared_params.clone();
            let param_types: Vec<(String, Type)> = op
                .params
                .iter()
                .map(|(label, texpr)| {
                    (
                        label.clone(),
                        self.convert_user_type_expr(texpr, &mut params_list),
                    )
                })
                .collect();
            let return_type = self.convert_user_type_expr(&op.return_type, &mut params_list);
            // Convert the op's own `needs` clause to an EffectRow
            let needs = if !op.effects.is_empty() || op.effect_row_var.is_some() {
                let effect_refs: Vec<EffectEntry> = op
                    .effects
                    .iter()
                    .map(|e| {
                        let args = e
                            .type_args
                            .iter()
                            .map(|te| self.convert_user_type_expr(te, &mut params_list))
                            .collect();
                        let resolved_name = self.resolved_effect_name(e.id, &e.name);
                        EffectEntry::unnamed(resolved_name, args)
                    })
                    .collect();
                let tail = op.effect_row_var.as_ref().map(|(rv_name, _)| {
                    let id = if let Some((_, id)) = params_list.iter().find(|(n, _)| n == rv_name) {
                        *id
                    } else {
                        let id = self.next_var;
                        self.next_var += 1;
                        params_list.push((rv_name.clone(), id));
                        id
                    };
                    Box::new(Type::Var(id))
                });
                EffectRow {
                    effects: effect_refs,
                    tail,
                }
            } else {
                EffectRow::empty()
            };
            op_spans.insert(op.name.clone(), op.span);
            ops.push(EffectOpSig {
                name: op.name.clone(),
                effect_name: name.to_string(),
                params: param_types,
                return_type,
                needs,
            });
        }
        self.scope_map
            .register_effect_ops(&key, ops.iter().map(|op| op.name.as_str()));
        if let Some(info) = self.effects.get_mut(&key) {
            info.ops = ops;
            info.op_spans = op_spans;
        }
        Ok(())
    }

    pub(crate) fn register_handler(&mut self, decl: &ast::Decl) -> Result<(), Diagnostic> {
        let ast::Decl::HandlerDef {
            id: def_id,
            name,
            name_span,
            body,
            span,
            ..
        } = decl
        else {
            unreachable!("register_handler called with non-HandlerDef");
        };
        let ast::HandlerBody {
            effects: effect_names,
            needs,
            where_clause,
            arms,
            return_clause,
        } = body;
        let return_clause = return_clause.as_deref();
        // Save and clear effect/field tracking for this handler body
        let body_scope = self.enter_scope();

        // Build type param bindings from handler's effect refs.
        // E.g. `handler counter for State Int` with effect State s:
        //   creates mapping {s_var_id -> Int}
        // Also track type variable names -> var IDs for where clause binding.
        let mut handler_type_mapping: std::collections::HashMap<u32, Type> =
            std::collections::HashMap::new();
        let mut type_var_params: Vec<(String, u32)> = Vec::new();
        for effect_ref in effect_names {
            self.record_effect_ref(effect_ref);
            let resolved_effect_name = self.resolved_effect_name(effect_ref.id, &effect_ref.name);
            if let Some(info) = self.effects.get(&resolved_effect_name) {
                let info = info.clone();
                for (i, &param_id) in info.type_params.iter().enumerate() {
                    if let Some(type_arg_expr) = effect_ref.type_args.get(i) {
                        let concrete_ty =
                            self.convert_user_type_expr(type_arg_expr, &mut type_var_params);
                        handler_type_mapping.insert(param_id, concrete_ty);
                    }
                }
            } else {
                self.collected_diagnostics.push(Diagnostic::error_at(
                    effect_ref.span,
                    format!("undefined effect: {}", effect_ref.name),
                ));
            }
        }

        // Register where clause bounds on handler type params.
        // E.g. `handler show_store for Store a where {a: Show}` registers Show bound on `a`'s var.
        for bound in where_clause {
            if let Some((_, var_id)) = type_var_params.iter().find(|(n, _)| n == &bound.type_var) {
                self.trait_state
                    .where_bound_var_names
                    .insert(*var_id, bound.type_var.clone());
                for tr in &bound.traits {
                    let resolved_req = self.resolved_trait_name_at(tr.id, &tr.name);
                    self.lsp
                        .type_references
                        .push((tr.span, resolved_req.clone()));
                    self.trait_state
                        .where_bounds
                        .entry(*var_id)
                        .or_default()
                        .insert(resolved_req);
                }
            } else {
                self.collected_diagnostics.push(Diagnostic::error_at(
                    *span,
                    format!(
                        "where clause references unknown type variable '{}' in handler '{}'",
                        bound.type_var, name
                    ),
                ));
            }
        }

        // Fresh type variable for the handler's answer type.
        // Arms unify against this; the return clause (if any) constrains it later.
        let answer_ty = self.fresh_var();

        // Save effects and start fresh for handler body checking
        let handler_saved_effs = self.save_effects();

        // Build effect row from handler's `needs` clause so `finally` blocks can
        // use these effects (they're already provided by the handler's caller).
        let needs_row = self.effect_row_from_refs(needs);

        // Validate that each arm's operation belongs to the handler's declared effects
        let mut seen_ops: std::collections::HashSet<String> = std::collections::HashSet::new();
        let mut arm_spans: std::collections::HashMap<String, Span> =
            std::collections::HashMap::new();
        for arm_ann in arms {
            let arm = &arm_ann.node;
            if !seen_ops.insert(arm.op_name.clone()) {
                return Err(Diagnostic::error_at(
                    arm.span,
                    format!("duplicate handler arm for operation '{}'", arm.op_name),
                ));
            }
            let mut belongs_to_declared = false;
            let mut matched_op: Option<EffectOpSig> = None;
            for effect_ref in effect_names {
                let resolved_effect_name =
                    self.resolved_effect_name(effect_ref.id, &effect_ref.name);
                if let Some(info) = self.effects.get(&resolved_effect_name)
                    && let Some(op) = info.ops.iter().find(|o| o.name == arm.op_name)
                {
                    if belongs_to_declared {
                        return Err(Diagnostic::error_at(
                            arm.span,
                            format!(
                                "ambiguous handler arm '{}': operation exists in multiple effects",
                                arm.op_name
                            ),
                        ));
                    }
                    belongs_to_declared = true;
                    // Record arm span -> (op definition span, source module) for LSP go-to-def (level 2)
                    if let Some(&op_span) = info.op_spans.get(&arm.op_name) {
                        self.lsp
                            .handler_arm_targets
                            .insert(arm.span, (op_span, info.source_module.clone()));
                    }
                    arm_spans.insert(arm.op_name.clone(), arm.span);
                    // Apply handler type bindings to specialize the op signature
                    let specialized = EffectOpSig {
                        name: op.name.clone(),
                        effect_name: op.effect_name.clone(),
                        params: op
                            .params
                            .iter()
                            .map(|(label, t)| {
                                (label.clone(), self.replace_vars(t, &handler_type_mapping))
                            })
                            .collect(),
                        return_type: self.replace_vars(&op.return_type, &handler_type_mapping),
                        needs: op.needs.clone(),
                    };
                    matched_op = Some(specialized);
                }
            }
            if !belongs_to_declared {
                return Err(Diagnostic::error_at(
                    arm.span,
                    format!(
                        "handler arm '{}' is not an operation of {}",
                        arm.op_name,
                        effect_names
                            .iter()
                            .map(|e| format!("'{}'", e.name))
                            .collect::<Vec<_>>()
                            .join(", ")
                    ),
                ));
            }

            let op_sig = matched_op.unwrap();

            // Bind op params and set resume context, then check body
            let saved_env = self.env.clone();
            let saved_resume = self.resume_type.take();
            let saved_resume_ret = self.resume_return_type.take();
            self.resume_type = Some(op_sig.return_type.clone());
            self.resume_return_type = Some(answer_ty.clone());

            for (i, pat) in arm.params.iter().enumerate() {
                let param_ty = if i < op_sig.params.len() {
                    op_sig.params[i].1.clone()
                } else {
                    self.fresh_var()
                };
                self.bind_pattern(pat, &param_ty)?;
            }

            let body_ty = self.infer_expr(&arm.body)?;
            if let Err(e) = self.unify(&answer_ty, &body_ty) {
                self.collected_diagnostics.push(e.with_span(arm.span));
            }

            // Typecheck optional `finally` block: may use the handler's `needs` effects
            // (they're already provided by the caller) but must not introduce new ones.
            if let Some(ref finally_expr) = arm.finally_block {
                let saved_effs = self.save_effects();
                let _finally_ty = self.infer_expr(finally_expr)?;
                let finally_effs = self.restore_effects(saved_effs);
                if let Err(e) = self.check_effects_via_row(
                    &finally_effs,
                    &needs_row,
                    &format!("finally block for '{}'", arm.op_name),
                    finally_expr.span,
                ) {
                    self.collected_diagnostics.push(e);
                }
            }

            self.resume_type = saved_resume;
            self.resume_return_type = saved_resume_ret;
            self.env = saved_env;
        }

        // Check the return clause body if present, capturing the param var and return type
        let handler_return_type = if let Some(rc) = return_clause {
            let saved_env = self.env.clone();
            let saved_resume = self.resume_type.take();
            let param_ty = self.fresh_var();
            let param_var_id = match &param_ty {
                Type::Var(id) => *id,
                _ => unreachable!(),
            };
            if let Some(pat) = rc.params.first() {
                self.bind_pattern(pat, &param_ty)?;
            }
            let ret_ty = self.infer_expr(&rc.body)?;
            // Constrain answer_ty to match the return clause's body type
            if let Err(e) = self.unify(&answer_ty, &ret_ty) {
                self.collected_diagnostics.push(e.with_span(rc.body.span));
            }
            self.resume_type = saved_resume;
            self.env = saved_env;
            // Freeze by applying sub: resolves internal handler vars but leaves
            // polymorphic vars (handler type params, answer type) as free Var nodes.
            let frozen_param = self.sub.apply(&Type::Var(param_var_id));
            let frozen_ret = self.sub.apply(&ret_ty);
            Some((frozen_param, frozen_ret))
        } else {
            // No return clause: the handler doesn't transform the result type.
            // Freeze answer_ty so usage sites get a template to instantiate.
            let frozen = self.sub.apply(&answer_ty);
            Some((frozen.clone(), frozen))
        };

        // Collect accumulated handler effects and restore outer scope
        let all_handler_effs = self.restore_effects(handler_saved_effs);
        let _scope_result = self.exit_scope(body_scope);
        let declared_effects: std::collections::HashSet<String> = needs
            .iter()
            .map(|e| {
                self.resolve_effect(&e.name)
                    .and_then(|info| {
                        let short = e.name.rsplit('.').next().unwrap_or(&e.name);
                        info.source_module
                            .as_ref()
                            .map(|m| format!("{}.{}", m, short))
                    })
                    .unwrap_or_else(|| {
                        if let Some(m) = &self.current_module {
                            format!("{}.{}", m, e.name)
                        } else {
                            e.name.clone()
                        }
                    })
            })
            .collect();

        let body_effects: std::collections::HashSet<String> = all_handler_effs
            .effects
            .iter()
            .map(|e| e.name.clone())
            .collect();
        if !body_effects.is_empty() || !declared_effects.is_empty() {
            let err_span = arms.first().map(|a| a.node.span).unwrap_or(*span);
            let undeclared: Vec<String> = body_effects
                .difference(&declared_effects)
                .cloned()
                .collect();
            if !undeclared.is_empty() {
                let mut sorted = undeclared;
                sorted.sort();
                let label = format!("handler '{}'", name);
                if declared_effects.is_empty() {
                    return Err(Diagnostic::error_at(
                        err_span,
                        format!(
                            "{} uses effects {{{}}} but has no 'needs' declaration",
                            label,
                            sorted.join(", ")
                        ),
                    ));
                } else {
                    return Err(Diagnostic::error_at(
                        err_span,
                        format!(
                            "{} uses effects {{{}}} not declared in its 'needs' clause",
                            label,
                            sorted.join(", ")
                        ),
                    ));
                }
            }
        }

        // Check that all operations from the handled effects are covered
        if !self.allow_bodyless_annotations {
            let handled_ops: std::collections::HashSet<&str> =
                arms.iter().map(|a| a.node.op_name.as_str()).collect();
            for effect_ref in effect_names {
                if let Some(info) = self.resolve_effect(&effect_ref.name) {
                    let missing: Vec<_> = info
                        .ops
                        .iter()
                        .filter(|op| !handled_ops.contains(op.name.as_str()))
                        .map(|op| op.name.as_str())
                        .collect();
                    if !missing.is_empty() {
                        self.collected_diagnostics.push(Diagnostic::error_at(
                            effect_ref.span,
                            format!(
                                "handler '{}' is missing {} from effect '{}'",
                                name,
                                missing.join(", "),
                                effect_ref.name,
                            ),
                        ));
                    }
                }
            }
        }

        // Collect free vars from frozen return type and needs effects as forall (polymorphic per usage).
        let mut forall = if let Some((ref param_ty, ref ret_ty)) = handler_return_type {
            let mut vars = Vec::new();
            super::collect_free_vars(param_ty, &mut vars);
            super::collect_free_vars(ret_ty, &mut vars);
            vars
        } else {
            vec![]
        };
        for entry in &all_handler_effs.effects {
            for t in &entry.args {
                super::collect_free_vars(t, &mut forall);
            }
        }

        // Build where_constraints map: (effect_name, param_index) -> trait constraints.
        // Links where clause type vars back to their position in the effect's type param list.
        let mut where_constraints: super::HandlerWhereConstraints =
            std::collections::HashMap::new();
        for bound in where_clause {
            if let Some((_, var_id)) = type_var_params.iter().find(|(n, _)| n == &bound.type_var) {
                // Find which effect and param index this var corresponds to
                for effect_ref in effect_names {
                    if let Some(info) = self.resolve_effect(&effect_ref.name) {
                        let canonical_effect =
                            self.resolved_effect_name(effect_ref.id, &effect_ref.name);
                        for (i, &param_id) in info.type_params.iter().enumerate() {
                            if let Some(mapped_ty) = handler_type_mapping.get(&param_id)
                                && matches!(mapped_ty, Type::Var(id) if *id == *var_id)
                            {
                                let entry = where_constraints
                                    .entry((canonical_effect.clone(), i))
                                    .or_default();
                                for tr in &bound.traits {
                                    let resolved_trait = self
                                        .resolve_trait_name(&tr.name)
                                        .unwrap_or_else(|| tr.name.clone());
                                    let extra_var_ids: Vec<u32> = tr
                                        .type_args
                                        .iter()
                                        .filter_map(|te| match te {
                                            crate::ast::TypeExpr::Var { name, .. } => {
                                                type_var_params
                                                    .iter()
                                                    .find(|(n, _)| n == name)
                                                    .map(|(_, id)| *id)
                                            }
                                            _ => None,
                                        })
                                        .collect();
                                    entry.push((resolved_trait, extra_var_ids));
                                }
                            }
                        }
                    }
                }
            }
        }

        // Canonicalize effect names so they match canonical names in effect rows.
        let canonical_effects: Vec<String> = effect_names
            .iter()
            .map(|e| {
                self.resolve_effect(&e.name)
                    .and_then(|info| {
                        let short = e.name.rsplit('.').next().unwrap_or(&e.name);
                        info.source_module
                            .as_ref()
                            .map(|m| format!("{}.{}", m, short))
                    })
                    .unwrap_or_else(|| {
                        if let Some(m) = &self.current_module {
                            format!("{}.{}", m, e.name)
                        } else {
                            e.name.clone()
                        }
                    })
            })
            .collect();
        let info = HandlerInfo {
            effects: canonical_effects,
            return_type: handler_return_type,
            needs_effects: all_handler_effs,
            forall,
            arm_spans,
            where_constraints,
            source_module: self.current_module.clone(),
        };
        self.handlers.insert(name.into(), info.clone());
        if let Some(module) = &self.current_module {
            self.handlers.insert(format!("{}.{}", module, name), info);
        }

        // Build Handler type from the effects this handler handles.
        // E.g. `handler h for Log` -> Con("Handler", [Con("Log", [])])
        // E.g. `handler h for State Int` -> Con("Handler", [Con("State", [Int])])
        let handler_effect_types: Vec<Type> = effect_names
            .iter()
            .map(|e| {
                let type_args: Vec<Type> = e
                    .type_args
                    .iter()
                    .map(|ta| self.convert_user_type_expr(ta, &mut vec![]))
                    .collect();
                Type::Con(self.canonical_effect_name(&e.name), type_args)
            })
            .collect();
        let handler_ty = Type::Con(
            super::canonicalize_type_name("Handler").into(),
            handler_effect_types,
        );

        // Put the handler name in the env so it can be referenced
        self.env.insert_with_def(
            name.into(),
            Scheme {
                forall: vec![],
                constraints: vec![],
                ty: handler_ty,
            },
            *def_id,
        );
        self.lsp.node_spans.insert(*def_id, *name_span);

        Ok(())
    }

    // --- Trait constraint checking ---

    pub(crate) fn check_pending_constraints(&mut self) -> Result<(), Diagnostic> {
        // Build resolved where bounds (substitution may have chained var IDs)
        let mut resolved_bounds: std::collections::HashMap<u32, std::collections::HashSet<String>> =
            std::collections::HashMap::new();
        // Also resolve var names through substitution
        let mut resolved_var_names: std::collections::HashMap<u32, String> =
            std::collections::HashMap::new();
        for (&var_id, traits) in &self.trait_state.where_bounds {
            if let Type::Var(resolved_id) = self.sub.apply(&Type::Var(var_id)) {
                resolved_bounds
                    .entry(resolved_id)
                    .or_default()
                    .extend(traits.iter().cloned());
                if let Some(name) = self.trait_state.where_bound_var_names.get(&var_id) {
                    resolved_var_names.insert(resolved_id, name.clone());
                }
            }
        }

        // Process constraints in a loop since conditional impls may push new ones
        loop {
            let constraints = std::mem::take(&mut self.trait_state.pending_constraints);
            if constraints.is_empty() {
                break;
            }
            for (trait_name, trait_type_arg_types, ty, span, node_id) in constraints {
                let resolved = self.sub.apply(&ty);
                if matches!(resolved, Type::Error) {
                    continue;
                }
                // Resolve trait type args to concrete type names for impl lookup
                let resolved_trait_type_args: Vec<String> = trait_type_arg_types
                    .iter()
                    .filter_map(|t| {
                        let resolved_t = self.sub.apply(t);
                        match &resolved_t {
                            Type::Con(name, _) => Some(name.clone()),
                            _ => None,
                        }
                    })
                    .collect();
                match &resolved {
                    // Concrete type (includes primitives): check that an impl exists.
                    // Try canonical form first, then resolve through scope_map.
                    Type::Con(type_name, args) => {
                        let resolved_trait = self
                            .resolve_trait_name(&trait_name)
                            .unwrap_or_else(|| trait_name.clone());
                        let impl_info = self
                            .trait_state
                            .impls
                            .get(&(
                                resolved_trait.clone(),
                                resolved_trait_type_args.clone(),
                                type_name.clone(),
                            ))
                            .or_else(|| {
                                // Fallback: try bare trait name for builtin impls (Num, Eq, Show for Tuple, etc.)
                                let bare =
                                    resolved_trait.rsplit('.').next().unwrap_or(&resolved_trait);
                                if bare != resolved_trait {
                                    self.trait_state.impls.get(&(
                                        bare.to_string(),
                                        resolved_trait_type_args.clone(),
                                        type_name.clone(),
                                    ))
                                } else {
                                    None
                                }
                            });
                        match impl_info {
                            None => {
                                // Check if this might be caused by a user function
                                // shadowing a trait method that would have worked.
                                let mut hint = String::new();
                                for (t_name, t_info) in &self.trait_state.traits {
                                    let has_impl = self
                                        .trait_state
                                        .impls
                                        .keys()
                                        .any(|(tn, _, tt)| tn == t_name && tt == type_name);
                                    if has_impl {
                                        for tm in &t_info.methods {
                                            // A user function shadowing a trait method by bare
                                            // name will have its own env entry without this
                                            // trait's constraint. Trait methods themselves no
                                            // longer have bare env entries, so any hit here is
                                            // either a user shadow or unrelated.
                                            if let Some(scheme) = self.env.get(&tm.name) {
                                                let is_trait_scheme = scheme
                                                    .constraints
                                                    .iter()
                                                    .any(|(c, _, _)| c == t_name);
                                                if !is_trait_scheme {
                                                    hint = format!(
                                                        ". `{}` shadows trait method `{}.{}`. \
                                                         rename it to use the trait method",
                                                        tm.name, t_name, tm.name
                                                    );
                                                }
                                            }
                                        }
                                    }
                                }
                                let display_trait =
                                    resolved_trait.rsplit('.').next().unwrap_or(&resolved_trait);
                                return Err(Diagnostic::error_at(
                                    span,
                                    format!(
                                        "no impl of {} for {}{}",
                                        display_trait, type_name, hint
                                    ),
                                ));
                            }
                            Some(info) => {
                                // Resolve extra type args through substitution so the
                                // elaborator sees concrete types for dict key lookup.
                                let resolved_extra_types: Vec<Type> = trait_type_arg_types
                                    .iter()
                                    .map(|t| self.sub.apply(t))
                                    .collect();
                                // Record evidence for the elaboration pass
                                self.evidence.push(super::TraitEvidence {
                                    node_id,
                                    trait_name: trait_name.clone(),
                                    resolved_type: Some((type_name.clone(), args.clone())),
                                    type_var_name: None,
                                    trait_type_args: resolved_extra_types,
                                });
                                // Push conditional constraints for type parameters
                                if type_name == super::canonicalize_type_name("Tuple") {
                                    // Tuples: propagate the trait to all elements
                                    for arg_ty in args {
                                        self.trait_state.pending_constraints.push((
                                            trait_name.clone(),
                                            vec![],
                                            arg_ty.clone(),
                                            span,
                                            node_id,
                                        ));
                                    }
                                } else {
                                    for (req_trait, param_idx) in &info.param_constraints {
                                        if let Some(arg_ty) = args.get(*param_idx) {
                                            self.trait_state.pending_constraints.push((
                                                req_trait.clone(),
                                                vec![],
                                                arg_ty.clone(),
                                                span,
                                                node_id,
                                            ));
                                        }
                                    }
                                }
                            }
                        }
                    }
                    // Still a type variable: check where clause bounds
                    Type::Var(id) => {
                        let covered = resolved_bounds
                            .get(id)
                            .is_some_and(|b| b.contains(&trait_name));
                        if !covered {
                            let display = trait_name.rsplit('.').next().unwrap_or(&trait_name);
                            return Err(Diagnostic::error_at(
                                span,
                                format!(
                                    "ambiguous type variable requires {}. Add a type annotation to pin the unconstrained type variable",
                                    display
                                ),
                            ));
                        }
                        // Record evidence for polymorphic passthrough
                        let var_name = resolved_var_names.get(id).cloned();
                        self.evidence.push(super::TraitEvidence {
                            node_id,
                            trait_name: trait_name.clone(),
                            resolved_type: None,
                            type_var_name: var_name,
                            trait_type_args: trait_type_arg_types.clone(),
                        });
                    }
                    Type::Fun(_, _, _) => {
                        let display = trait_name.rsplit('.').next().unwrap_or(&trait_name);
                        return Err(Diagnostic::error_at(
                            span,
                            format!("no impl of {} for function type", display),
                        ));
                    }
                    Type::Record(_) => {
                        let display = trait_name.rsplit('.').next().unwrap_or(&trait_name);
                        return Err(Diagnostic::error_at(
                            span,
                            format!("no impl of {} for anonymous record type", display),
                        ));
                    }
                    // Error/Never type: skip trait checking
                    Type::Error => {}
                }
            }
        }
        Ok(())
    }

    // --- Supertrait checking ---

    /// Verify that every impl's trait has its supertraits also implemented for the same type.
    pub(crate) fn check_supertrait_impls(&self) -> Result<(), Diagnostic> {
        for ((trait_name, _trait_type_args, target_type), impl_info) in &self.trait_state.impls {
            if let Some(trait_info) = self.trait_state.traits.get(trait_name) {
                for supertrait in &trait_info.supertraits {
                    // Supertraits are always single-param (no type args)
                    if !self.trait_state.impls.contains_key(&(
                        supertrait.clone(),
                        vec![],
                        target_type.clone(),
                    )) {
                        let msg = format!(
                            "impl {} for {} requires impl {} for {} (supertrait)",
                            trait_name, target_type, supertrait, target_type
                        );
                        return Err(match impl_info.span {
                            Some(span) => Diagnostic::error_at(span, msg),
                            None => Diagnostic::error(msg),
                        });
                    }
                }
            }
        }
        Ok(())
    }
}
