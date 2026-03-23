use std::collections::HashMap;

use crate::ast::{self, Decl};

use super::result::CheckResult;
use super::{
    Checker, Diagnostic, EffectDefInfo, EffectOpSig, HandlerInfo, RecordInfo, Scheme, Span, Type,
};

/// Annotations collected from FunAnnotation declarations:
/// (name -> (type, span)) and (name -> where clause constraints).
type Annotations = (
    HashMap<String, (Type, Span)>,
    HashMap<String, Vec<(String, u32)>>,
);

impl Checker {
    // --- Top-level declarations ---

    /// Typecheck a program and return the public result.
    /// This is the main entry point for external callers.
    pub fn check_program(&mut self, program: &[Decl]) -> CheckResult {
        if let Err(errors) = self.check_program_inner(program) {
            for e in errors {
                self.collected_diagnostics.push(e);
            }
        }
        self.check_unused_variables();
        self.zonk_warnings();
        self.to_result()
    }

    /// Internal implementation of check_program.
    /// Returns Err for fatal errors that prevent further checking.
    /// Non-fatal diagnostics are accumulated in collected_diagnostics.
    pub(crate) fn check_program_inner(
        &mut self,
        program: &[Decl],
    ) -> std::result::Result<(), Vec<Diagnostic>> {
        self.register_definitions(program)?;
        self.process_imports(program)?;
        self.register_externals(program)?;
        let (annotations, annotation_constraints) = self.collect_annotations(program)?;
        let fun_vars = self.pre_bind_functions(program, &annotations);
        self.register_all_impls(program)?;
        self.check_supertrait_impls().map_err(|e| vec![e])?;

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
        if let Some(effects) = self.effect_state.fun_effects.get("main")
            && !effects.is_empty()
        {
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
                        effects.iter().cloned().collect::<Vec<_>>().join(", ")
                    ),
                ));
        }

        // Validate that `main` does not have unresolved trait constraints
        // (it is the entry point -- there is no caller to supply dictionaries)
        if let Some(scheme) = self.env.get("main")
            && !scheme.constraints.is_empty()
        {
            let traits: Vec<_> = scheme.constraints.iter().map(|(t, _)| t.as_str()).collect();
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
                        name, annotations: ann, ..
                    } if ann.iter().any(|a| a.name == "external" || a.name == "builtin") => {
                        Some(name.as_str())
                    }
                    _ => None,
                })
                .collect();
            for (name, (_, span)) in &annotations {
                if !bound_names.contains(name.as_str())
                    && !bodyless_names.contains(name.as_str())
                {
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
                    let ann_ty = self.convert_type_expr(ann, &mut vec![]);
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
    fn register_definitions(
        &mut self,
        program: &[Decl],
    ) -> std::result::Result<(), Vec<Diagnostic>> {
        for decl in program {
            match decl {
                Decl::TypeDef {
                    name,
                    type_params,
                    variants,
                    ..
                } => {
                    self.register_type_def(name, type_params, variants)
                        .map_err(|e| vec![e])?;
                }
                Decl::RecordDef {
                    id,
                    name,
                    type_params,
                    fields,
                    ..
                } => {
                    self.register_record_def(name, type_params, fields, *id)
                        .map_err(|e| vec![e])?;
                }
                Decl::EffectDef {
                    name,
                    type_params,
                    operations,
                    ..
                } => {
                    self.register_effect_def(name, type_params, operations)
                        .map_err(|e| vec![e])?;
                }
                Decl::TraitDef {
                    name,
                    type_param,
                    supertraits,
                    methods,
                    ..
                } => {
                    self.register_trait_def(name, type_param, supertraits, methods)
                        .map_err(|e| vec![e])?;
                }
                _ => {}
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
                let mut fun_ty = self.convert_type_expr(return_type, &mut params_list);
                for (_, texpr) in params.iter().rev() {
                    let param_ty = self.convert_type_expr(texpr, &mut params_list);
                    fun_ty = Type::Arrow(Box::new(param_ty), Box::new(fun_ty));
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
                        for (trait_name, trait_span) in &bound.traits {
                            self.lsp
                                .type_references
                                .push((*trait_span, trait_name.clone()));
                        }
                        if let Some((_, var_id)) =
                            params_list.iter().find(|(n, _)| *n == bound.type_var)
                        {
                            for (trait_name, _) in &bound.traits {
                                scheme_constraints.push((trait_name.clone(), *var_id));
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
        let mut annotation_constraints: HashMap<String, Vec<(String, u32)>> = HashMap::new();

        for decl in program {
            if let Decl::FunSignature {
                id,
                name,
                name_span,
                params,
                return_type,
                effects,
                where_clause,
                span,
                ..
            } = decl
            {
                let mut params_list: Vec<(String, u32)> = vec![];
                let mut fun_ty = self.convert_type_expr(return_type, &mut params_list);
                for (_, texpr) in params.iter().rev() {
                    let param_ty = self.convert_type_expr(texpr, &mut params_list);
                    fun_ty = Type::Arrow(Box::new(param_ty), Box::new(fun_ty));
                }
                annotations.insert(name.clone(), (fun_ty.clone(), *span));

                // Always register in fun_effects (even pure functions get an empty
                // set) so the `with` validation can distinguish local declarations
                // from imports/parameters.
                self.effect_state.fun_effects.insert(
                    name.clone(),
                    effects.iter().map(|e| e.name.clone()).collect(),
                );
                if !effects.is_empty() {
                    let mut constraints = Vec::new();
                    for eff in effects {
                        self.record_effect_ref(eff);
                        if !eff.type_args.is_empty() {
                            let concrete_types: Vec<Type> = eff
                                .type_args
                                .iter()
                                .map(|ta| self.convert_type_expr(ta, &mut params_list))
                                .collect();
                            constraints.push((eff.name.clone(), concrete_types));
                        }
                    }
                    if !constraints.is_empty() {
                        self.effect_state
                            .fun_type_constraints
                            .insert(name.clone(), constraints);
                    }
                }

                if !where_clause.is_empty() {
                    let mut constraints = Vec::new();
                    for bound in where_clause {
                        for (trait_name, trait_span) in &bound.traits {
                            self.lsp
                                .type_references
                                .push((*trait_span, trait_name.clone()));
                        }
                        if let Some((_, var_id)) =
                            params_list.iter().find(|(n, _)| *n == bound.type_var)
                        {
                            self.trait_state
                                .where_bound_var_names
                                .insert(*var_id, bound.type_var.clone());
                            for (trait_name, _) in &bound.traits {
                                constraints.push((trait_name.clone(), *var_id));
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
                && !fun_vars.contains_key(name)
            {
                // Register all functions in fun_effects (annotated ones are
                // already registered with their declared effects; un-annotated
                // ones get an empty set). This lets `with` validation distinguish
                // local functions from imports.
                self.effect_state
                    .fun_effects
                    .entry(name.clone())
                    .or_default();
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
            }
        }
        fun_vars
    }

    /// Pass 6: Register trait impls.
    fn register_all_impls(&mut self, program: &[Decl]) -> std::result::Result<(), Vec<Diagnostic>> {
        for decl in program {
            if let Decl::ImplDef {
                trait_name,
                trait_name_span,
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
                self.register_impl(
                    trait_name,
                    target_type,
                    type_params,
                    where_clause,
                    needs,
                    methods,
                    *span,
                )
                .map_err(|e| vec![e])?;
            }
        }
        Ok(())
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
        where_constraints: &[(String, u32)],
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
            for param_ty in &param_types {
                match ann_current {
                    Type::Arrow(ann_param, ann_ret) | Type::EffArrow(ann_param, ann_ret, _) => {
                        self.unify(param_ty, &ann_param)?;
                        ann_current = *ann_ret;
                    }
                    _ => break,
                }
            }
            self.unify(&result_ty, &ann_current)?;

            // Build the function type from annotation-constrained params and unify with pre-bound var
            let mut pre_ty = result_ty.clone();
            for param_ty in param_types.iter().rev() {
                pre_ty = Type::Arrow(Box::new(param_ty.clone()), Box::new(pre_ty));
            }
            self.unify(fun_var, &pre_ty)?;
        }

        // Register where clause bounds on type variable IDs
        for (trait_name, var_id) in where_constraints {
            self.trait_state
                .where_bounds
                .entry(*var_id)
                .or_default()
                .insert(trait_name.clone());
        }

        // Snapshot pending constraints so we can partition new ones after body checking
        let constraints_before = self.trait_state.pending_constraints.len();

        // Save and clear effect tracking and field candidate tracking for this function body
        let body_scope = self.enter_effect_scope();

        // Pre-populate effect type param cache from annotation constraints (e.g. needs {State Int})
        if let Some(constraints) = self.effect_state.fun_type_constraints.get(name).cloned() {
            for (effect_name, concrete_types) in &constraints {
                if let Some(info) = self.effects.get(effect_name).cloned() {
                    let mapping: std::collections::HashMap<u32, Type> = info
                        .type_params
                        .iter()
                        .zip(concrete_types.iter())
                        .map(|(&param_id, ty)| (param_id, ty.clone()))
                        .collect();
                    self.effect_state
                        .type_param_cache
                        .insert(effect_name.clone(), mapping);
                }
            }
        }

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
                let guard_ty = self.infer_expr(guard)?;
                self.unify_at(&guard_ty, &Type::bool(), guard.span)?;
            }

            let body_ty = self.infer_expr(body)?;
            self.unify_at(&result_ty, &body_ty, body.span)?;

            self.env = saved_env;
        }

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

        // Check effect requirements against declared needs
        let scope_result = self.exit_effect_scope(body_scope);
        let body_effects = scope_result.effects;
        let body_field_candidates = scope_result.field_candidates;
        let declared_effects = self
            .effect_state
            .fun_effects
            .get(name)
            .cloned()
            .unwrap_or_default();

        if !body_effects.is_empty() || !declared_effects.is_empty() {
            let err_span = match clauses[0] {
                Decl::FunBinding { span, .. } => *span,
                _ => unreachable!(),
            };
            Self::check_undeclared_effects(
                &body_effects,
                &declared_effects,
                &format!("function '{}'", name),
                err_span,
            )?;

            // Check for effects declared but never used
            let unused: Vec<_> = declared_effects.difference(&body_effects).collect();
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

        // Build curried function type
        let mut fun_ty = result_ty;
        for param_ty in param_types.into_iter().rev() {
            fun_ty = Type::Arrow(Box::new(param_ty), Box::new(fun_ty));
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

    /// Partition pending constraints into scheme-level (polymorphic) vs global
    /// (concrete), then generalize the function type into a scheme with constraints.
    fn build_fun_scheme(
        &mut self,
        name: &str,
        fun_ty: Type,
        constraints_before: usize,
        has_annotation: bool,
        where_constraints: &[(String, u32)],
    ) -> Result<Scheme, Diagnostic> {
        let new_constraints = self
            .trait_state
            .pending_constraints
            .split_off(constraints_before);
        let mut scheme_constraints: Vec<(String, u32, Span)> = Vec::new();
        for (trait_name, ty, span, node_id) in new_constraints {
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
                        // Record polymorphic passthrough evidence so the elaborator
                        // knows this is a trait method call (needs DictMethodAccess).
                        let var_name = self.trait_state.where_bound_var_names.get(&id).cloned();
                        self.evidence.push(super::TraitEvidence {
                            node_id,
                            trait_name: trait_name.clone(),
                            resolved_type: None,
                            type_var_name: var_name,
                        });
                        continue;
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
                    let var_name = self.trait_state.where_bound_var_names.get(&id).cloned();
                    self.evidence.push(super::TraitEvidence {
                        node_id,
                        trait_name: trait_name.clone(),
                        resolved_type: None,
                        type_var_name: var_name,
                    });
                    scheme_constraints.push((trait_name, id, span));
                }
                _ => {
                    self.trait_state
                        .pending_constraints
                        .push((trait_name, ty, span, node_id));
                }
            }
        }

        self.env.remove(name);
        let mut scheme = self.generalize(&fun_ty);

        for (trait_name, var_id) in where_constraints {
            let resolved_id = match self.sub.apply(&Type::Var(*var_id)) {
                Type::Var(id) => id,
                _ => continue,
            };
            if scheme.forall.contains(&resolved_id) {
                scheme.constraints.push((trait_name.clone(), resolved_id));
            }
        }

        // Collect type vars that actually appear in the function's type
        let mut type_vars = Vec::new();
        super::collect_free_vars(&self.sub.apply(&fun_ty), &mut type_vars);

        for (trait_name, var_id, span) in scheme_constraints {
            if !type_vars.contains(&var_id) {
                return Err(Diagnostic::error_at(
                    span,
                    format!(
                        "ambiguous type variable requires {} but has no concrete type in '{}'",
                        trait_name, name
                    ),
                ));
            }
            if scheme.forall.contains(&var_id)
                && !scheme
                    .constraints
                    .iter()
                    .any(|(t, v)| t == &trait_name && *v == var_id)
            {
                scheme.constraints.push((trait_name, var_id));
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
            Type::Con(name, _) => self.adt_variants.contains_key(name) || name == "Tuple",
            _ => false,
        });
        if !has_adt_param {
            return Ok(());
        }

        let ctx = ExhaustivenessCtx {
            adt_variants: &self.adt_variants,
        };

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

            let row: Vec<SPat> = params.iter().map(exh::simplify_pat).collect();

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
        variants: &[ast::TypeConstructor],
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

        let result_type = Type::Con(
            name.into(),
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
                    let field_ty = self.convert_type_expr(field, &mut param_vars);
                    ty = Type::Arrow(Box::new(field_ty), Box::new(ty));
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
            name.into(),
            variants
                .iter()
                .map(|v| (v.name.clone(), v.fields.len()))
                .collect(),
        );

        self.type_arity.insert(name.into(), type_params.len());

        Ok(())
    }

    pub(crate) fn register_record_def(
        &mut self,
        name: &str,
        type_params: &[String],
        fields: &[(String, ast::TypeExpr)],
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
                    self.convert_type_expr(texpr, &mut param_vars),
                )
            })
            .collect();

        let forall: Vec<u32> = param_vars.iter().map(|(_, id)| *id).collect();

        // Build result type: e.g. Box a -> Con("Box", [Var(a_id)])
        let result_type = Type::Con(
            name.into(),
            forall.iter().map(|&id| Type::Var(id)).collect(),
        );

        // Register record constructor scheme: e.g. Box : forall a. a -> Box a
        // Constructor takes fields in order, returns the record type.
        let mut ctor_ty = result_type;
        for (_, field_ty) in field_types.iter().rev() {
            ctor_ty = Type::Arrow(Box::new(field_ty.clone()), Box::new(ctor_ty));
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

        self.records.insert(
            name.into(),
            RecordInfo {
                type_params: forall,
                fields: field_types,
            },
        );
        self.type_arity.insert(name.into(), type_params.len());
        Ok(())
    }

    pub(crate) fn register_effect_def(
        &mut self,
        name: &str,
        effect_type_params: &[String],
        operations: &[ast::EffectOp],
    ) -> Result<(), Diagnostic> {
        // Create fresh vars for the effect's type params, shared across all operations.
        // E.g. for `effect State s { get () -> s; put (val: s) -> Unit }`,
        // a single var ID for `s` is used by both `get` and `put`.
        let mut shared_params: Vec<(String, u32)> = vec![];
        let mut type_param_ids = Vec::new();
        for tp in effect_type_params {
            let var = self.fresh_var();
            let id = match &var {
                Type::Var(id) => *id,
                _ => unreachable!(),
            };
            shared_params.push((tp.clone(), id));
            type_param_ids.push(id);
        }

        let mut ops = Vec::new();
        let mut op_spans = std::collections::HashMap::new();
        for op in operations {
            // Start with the shared effect type params, then add op-local type vars
            let mut params_list = shared_params.clone();
            let param_types: Vec<(String, Type)> = op
                .params
                .iter()
                .map(|(label, texpr)| {
                    (
                        label.clone(),
                        self.convert_type_expr(texpr, &mut params_list),
                    )
                })
                .collect();
            let return_type = self.convert_type_expr(&op.return_type, &mut params_list);
            op_spans.insert(op.name.clone(), op.span);
            ops.push(EffectOpSig {
                name: op.name.clone(),
                params: param_types,
                return_type,
            });
        }
        self.effects.insert(
            name.into(),
            EffectDefInfo {
                type_params: type_param_ids,
                ops,
                op_spans,
                source_module: self.current_module.clone(),
            },
        );
        self.type_arity
            .insert(name.into(), effect_type_params.len());
        Ok(())
    }

    pub(crate) fn register_handler(&mut self, decl: &ast::Decl) -> Result<(), Diagnostic> {
        let ast::Decl::HandlerDef {
            id: def_id,
            name,
            name_span,
            effects: effect_names,
            needs,
            where_clause,
            arms,
            return_clause,
            span,
            ..
        } = decl
        else {
            unreachable!("register_handler called with non-HandlerDef");
        };
        let return_clause = return_clause.as_deref();
        // Save and clear effect/field tracking for this handler body
        let body_scope = self.enter_effect_scope();

        // Build type param bindings from handler's effect refs.
        // E.g. `handler counter for State Int` with effect State s:
        //   creates mapping {s_var_id -> Int}
        // Also track type variable names -> var IDs for where clause binding.
        let mut handler_type_mapping: std::collections::HashMap<u32, Type> =
            std::collections::HashMap::new();
        let mut type_var_params: Vec<(String, u32)> = Vec::new();
        for effect_ref in effect_names {
            self.record_effect_ref(effect_ref);
            if let Some(info) = self.effects.get(&effect_ref.name) {
                let info = info.clone();
                for (i, &param_id) in info.type_params.iter().enumerate() {
                    if let Some(type_arg_expr) = effect_ref.type_args.get(i) {
                        let concrete_ty =
                            self.convert_type_expr(type_arg_expr, &mut type_var_params);
                        handler_type_mapping.insert(param_id, concrete_ty);
                    }
                }
            }
        }

        // Register where clause bounds on handler type params.
        // E.g. `handler show_store for Store a where {a: Show}` registers Show bound on `a`'s var.
        for bound in where_clause {
            if let Some((_, var_id)) = type_var_params.iter().find(|(n, _)| n == &bound.type_var) {
                self.trait_state
                    .where_bound_var_names
                    .insert(*var_id, bound.type_var.clone());
                for (trait_req, trait_span) in &bound.traits {
                    self.lsp
                        .type_references
                        .push((*trait_span, trait_req.clone()));
                    self.trait_state
                        .where_bounds
                        .entry(*var_id)
                        .or_default()
                        .insert(trait_req.clone());
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

        // Validate that each arm's operation belongs to the handler's declared effects
        let mut seen_ops: std::collections::HashSet<String> = std::collections::HashSet::new();
        let mut arm_spans: std::collections::HashMap<String, Span> =
            std::collections::HashMap::new();
        for arm in arms {
            if !seen_ops.insert(arm.op_name.clone()) {
                return Err(Diagnostic::error_at(
                    arm.span,
                    format!("duplicate handler arm for operation '{}'", arm.op_name),
                ));
            }
            let mut belongs_to_declared = false;
            let mut matched_op: Option<EffectOpSig> = None;
            for effect_ref in effect_names {
                if let Some(info) = self.effects.get(&effect_ref.name)
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
                        params: op
                            .params
                            .iter()
                            .map(|(label, t)| {
                                (label.clone(), self.replace_vars(t, &handler_type_mapping))
                            })
                            .collect(),
                        return_type: self.replace_vars(&op.return_type, &handler_type_mapping),
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

            for (i, (param_name, param_span)) in arm.params.iter().enumerate() {
                let param_ty = if i < op_sig.params.len() {
                    op_sig.params[i].1.clone()
                } else {
                    self.fresh_var()
                };
                let param_id = crate::ast::NodeId::fresh();
                self.env.insert_with_def(
                    param_name.clone(),
                    Scheme {
                        forall: vec![],
                        constraints: vec![],
                        ty: param_ty.clone(),
                    },
                    param_id,
                );
                self.lsp.node_spans.insert(param_id, *param_span);
                self.lsp.type_at_span.insert(*param_span, param_ty);
                self.lsp
                    .definitions
                    .push((param_id, param_name.clone(), *param_span));
            }

            let body_ty = self.infer_expr(&arm.body)?;
            // If the op returns Never (non-resumable), the arm body must also
            // be Never (i.e. diverge). Otherwise the handler would silently
            // produce a non-Never value with no way to continue the computation.
            if matches!(op_sig.return_type, Type::Never) {
                let resolved = self.sub.apply(&body_ty);
                if !matches!(resolved, Type::Never | Type::Error) {
                    let display_ty = self.prettify_type(&body_ty);
                    self.collected_diagnostics.push(Diagnostic::error_at(
                        arm.span,
                        format!(
                            "non-resumable handler arm must diverge (return Never), but returns `{}`",
                            display_ty
                        ),
                    ));
                }
            } else if let Err(e) = self.unify(&answer_ty, &body_ty) {
                self.collected_diagnostics.push(e.with_span(arm.span));
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
            if let Some((param_name, param_span)) = rc.params.first() {
                let param_id = crate::ast::NodeId::fresh();
                self.env.insert_with_def(
                    param_name.clone(),
                    Scheme {
                        forall: vec![],
                        constraints: vec![],
                        ty: param_ty.clone(),
                    },
                    param_id,
                );
                self.lsp.node_spans.insert(param_id, *param_span);
                self.lsp.type_at_span.insert(*param_span, param_ty);
                self.lsp
                    .definitions
                    .push((param_id, param_name.clone(), *param_span));
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

        // Check effect requirements against declared needs
        let scope_result = self.exit_effect_scope(body_scope);
        let body_effects = scope_result.effects;
        let declared_effects: std::collections::HashSet<String> =
            needs.iter().map(|e| e.name.clone()).collect();

        if !body_effects.is_empty() || !declared_effects.is_empty() {
            let err_span = arms.first().map(|a| a.span).unwrap_or(*span);
            Self::check_undeclared_effects(
                &body_effects,
                &declared_effects,
                &format!("handler '{}'", name),
                err_span,
            )?;
        }

        // Check that all operations from the handled effects are covered
        if !self.allow_bodyless_annotations {
            let handled_ops: std::collections::HashSet<&str> =
                arms.iter().map(|a| a.op_name.as_str()).collect();
            for effect_ref in effect_names {
                if let Some(info) = self.effects.get(&effect_ref.name) {
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

        // Collect free vars from frozen return type as forall (polymorphic per usage).
        let forall = if let Some((ref param_ty, ref ret_ty)) = handler_return_type {
            let mut vars = Vec::new();
            super::collect_free_vars(param_ty, &mut vars);
            super::collect_free_vars(ret_ty, &mut vars);
            vars
        } else {
            vec![]
        };

        // Build where_constraints map: (effect_name, param_index) -> set of required trait names.
        // Links where clause type vars back to their position in the effect's type param list.
        let mut where_constraints: std::collections::HashMap<
            (String, usize),
            std::collections::HashSet<String>,
        > = std::collections::HashMap::new();
        for bound in where_clause {
            if let Some((_, var_id)) = type_var_params.iter().find(|(n, _)| n == &bound.type_var) {
                // Find which effect and param index this var corresponds to
                for effect_ref in effect_names {
                    if let Some(info) = self.effects.get(&effect_ref.name) {
                        for (i, &param_id) in info.type_params.iter().enumerate() {
                            if let Some(mapped_ty) = handler_type_mapping.get(&param_id)
                                && matches!(mapped_ty, Type::Var(id) if *id == *var_id)
                            {
                                let entry = where_constraints
                                    .entry((effect_ref.name.clone(), i))
                                    .or_default();
                                for (trait_name, _) in &bound.traits {
                                    entry.insert(trait_name.clone());
                                }
                            }
                        }
                    }
                }
            }
        }

        self.handlers.insert(
            name.into(),
            HandlerInfo {
                effects: effect_names.iter().map(|e| e.name.clone()).collect(),
                return_type: handler_return_type,
                forall,
                arm_spans,
                where_constraints,
                source_module: self.current_module.clone(),
            },
        );

        // Put the handler name in the env so it can be referenced
        self.env.insert_with_def(
            name.into(),
            Scheme {
                forall: vec![],
                constraints: vec![],
                ty: Type::unit(), // handlers don't have a meaningful standalone type
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
            for (trait_name, ty, span, node_id) in constraints {
                let resolved = self.sub.apply(&ty);
                if matches!(resolved, Type::Error | Type::Never) {
                    continue;
                }
                match &resolved {
                    // Concrete type (includes primitives): check that an impl exists
                    Type::Con(type_name, args) => {
                        let impl_info = self
                            .trait_state
                            .impls
                            .get(&(trait_name.clone(), type_name.clone()));
                        match impl_info {
                            None => {
                                // Check if this might be caused by a user function
                                // shadowing a trait method that would have worked.
                                let mut hint = String::new();
                                for (t_name, t_info) in &self.trait_state.traits {
                                    if self
                                        .trait_state
                                        .impls
                                        .contains_key(&(t_name.clone(), type_name.clone()))
                                    {
                                        for (m_name, _, _, _) in &t_info.methods {
                                            if let Some(scheme) = self.env.get(m_name) {
                                                // A trait method's scheme has the trait name
                                                // in its constraints. If the env entry doesn't,
                                                // it's a user function shadowing the method.
                                                let is_trait_scheme = scheme
                                                    .constraints
                                                    .iter()
                                                    .any(|(c, _)| c == t_name);
                                                if !is_trait_scheme {
                                                    hint = format!(
                                                        ". `{}` shadows trait method `{}.{}`. \
                                                         rename it to use the trait method",
                                                        m_name, t_name, m_name
                                                    );
                                                }
                                            }
                                        }
                                    }
                                }
                                return Err(Diagnostic::error_at(
                                    span,
                                    format!("no impl of {} for {}{}", trait_name, type_name, hint),
                                ));
                            }
                            Some(info) => {
                                // Record evidence for the elaboration pass
                                self.evidence.push(super::TraitEvidence {
                                    node_id,
                                    trait_name: trait_name.clone(),
                                    resolved_type: Some((type_name.clone(), args.clone())),
                                    type_var_name: None,
                                });
                                // Push conditional constraints for type parameters
                                if type_name == "Tuple" {
                                    // Tuples: propagate the trait to all elements
                                    for arg_ty in args {
                                        self.trait_state.pending_constraints.push((
                                            trait_name.clone(),
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
                            return Err(Diagnostic::error_at(
                                span,
                                format!(
                                    "trait {} required but no impl or where clause bound for this type",
                                    trait_name
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
                        });
                    }
                    Type::Arrow(_, _) | Type::EffArrow(_, _, _) => {
                        return Err(Diagnostic::error_at(
                            span,
                            format!("no impl of {} for function type", trait_name),
                        ));
                    }
                    Type::Record(_) => {
                        return Err(Diagnostic::error_at(
                            span,
                            format!("no impl of {} for anonymous record type", trait_name),
                        ));
                    }
                    // Error/Never type: skip trait checking
                    Type::Error | Type::Never => {}
                }
            }
        }
        Ok(())
    }

    // --- Supertrait checking ---

    /// Verify that every impl's trait has its supertraits also implemented for the same type.
    pub(crate) fn check_supertrait_impls(&self) -> Result<(), Diagnostic> {
        for ((trait_name, target_type), impl_info) in &self.trait_state.impls {
            if let Some(trait_info) = self.trait_state.traits.get(trait_name) {
                for supertrait in &trait_info.supertraits {
                    if !self
                        .trait_state
                        .impls
                        .contains_key(&(supertrait.clone(), target_type.clone()))
                    {
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
