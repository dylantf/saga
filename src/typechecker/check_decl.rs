use std::collections::HashMap;

use crate::ast::{self, Decl};

use super::{Checker, EffectDefInfo, EffectOpSig, HandlerInfo, Scheme, Type, TypeError};

impl Checker {
    // --- Top-level declarations ---

    pub fn check_program(&mut self, program: &[Decl]) -> Result<(), TypeError> {
        // First pass: register type definitions and record definitions
        for decl in program {
            match decl {
                Decl::TypeDef {
                    name,
                    type_params,
                    variants,
                    ..
                } => {
                    self.register_type_def(name, type_params, variants)?;
                }
                Decl::RecordDef { name, fields, .. } => {
                    self.register_record_def(name, fields)?;
                }
                Decl::EffectDef {
                    name,
                    type_params,
                    operations,
                    ..
                } => {
                    self.register_effect_def(name, type_params, operations)?;
                }
                Decl::TraitDef {
                    name,
                    type_param,
                    supertraits,
                    methods,
                    ..
                } => {
                    self.register_trait_def(name, type_param, supertraits, methods)?;
                }
                _ => {}
            }
        }

        // Register impls (after traits so we can validate against them)
        for decl in program {
            if let Decl::ImplDef {
                trait_name,
                target_type,
                type_params,
                where_clause,
                needs,
                methods,
                span,
            } = decl
            {
                self.register_impl(
                    trait_name,
                    target_type,
                    type_params,
                    where_clause,
                    needs,
                    methods,
                    *span,
                )?;
            }
        }

        // Check supertrait requirements (after all impls are registered so order doesn't matter)
        self.check_supertrait_impls()?;

        // Collect function annotations: name -> declared type, effects, and where constraints
        let mut annotations: HashMap<std::string::String, Type> = HashMap::new();
        let mut annotation_constraints: HashMap<std::string::String, Vec<(String, u32)>> =
            HashMap::new();
        for decl in program {
            if let Decl::FunAnnotation {
                name,
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
                annotations.insert(name.clone(), fun_ty);
                if !effects.is_empty() {
                    self.fun_effects.insert(
                        name.clone(),
                        effects.iter().map(|e| e.name.clone()).collect(),
                    );
                    // Store effect type arg constraints for pre-populating the cache
                    let mut constraints = Vec::new();
                    for eff in effects {
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
                        self.fun_effect_type_constraints
                            .insert(name.clone(), constraints);
                    }
                }

                // Process where clause into (trait_name, var_id) constraints
                if !where_clause.is_empty() {
                    let mut constraints = Vec::new();
                    for bound in where_clause {
                        if let Some((_, var_id)) =
                            params_list.iter().find(|(n, _)| *n == bound.type_var)
                        {
                            for trait_name in &bound.traits {
                                constraints.push((trait_name.clone(), *var_id));
                            }
                        } else {
                            return Err(TypeError::at(
                                *span,
                                format!(
                                    "where clause references unknown type variable '{}'",
                                    bound.type_var
                                ),
                            ));
                        }
                    }
                    annotation_constraints.insert(name.clone(), constraints);
                }
            }
        }

        // Second pass: pre-bind all function names with fresh vars (enables mutual recursion)
        let mut fun_vars: HashMap<std::string::String, Type> = HashMap::new();
        for decl in program {
            if let Decl::FunBinding { name, .. } = decl
                && !fun_vars.contains_key(name)
            {
                let var = self.fresh_var();
                fun_vars.insert(name.clone(), var.clone());
                self.env.insert(
                    name.clone(),
                    Scheme {
                        forall: vec![],
                        constraints: vec![],
                        ty: var,
                    },
                );
            }
        }

        // Third pass: group multi-clause function bindings, then check everything
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
                let annotation = annotations.get(&name).cloned();
                let where_cons = annotation_constraints
                    .get(&name)
                    .map(|v| v.as_slice())
                    .unwrap_or(&[]);
                self.check_fun_clauses(&name, &clauses, &fun_var, annotation.as_ref(), where_cons)?;
            } else {
                self.check_decl(&program[i])?;
                i += 1;
            }
        }

        // Validate that `main` does not declare effects (it's the top of the call stack,
        // there is no caller above to provide handlers)
        if let Some(effects) = self.fun_effects.get("main") {
            if !effects.is_empty() {
                // Find the span from the annotation
                let span = program.iter().find_map(|d| {
                    if let Decl::FunAnnotation { name, span, .. } = d
                        && name == "main"
                    {
                        Some(*span)
                    } else {
                        None
                    }
                });
                return Err(TypeError::at(
                    span.unwrap_or(crate::token::Span { start: 0, end: 0 }),
                    format!(
                        "`main` cannot use `needs` -- it is the entry point and there is no caller to provide handlers for {{{}}}. Handle effects inside `main` using `with` instead.",
                        effects.iter().cloned().collect::<Vec<_>>().join(", ")
                    ),
                ));
            }
        }

        // Check all accumulated trait constraints now that types are resolved
        self.check_pending_constraints()?;

        Ok(())
    }

    pub(crate) fn check_decl(&mut self, decl: &Decl) -> Result<(), TypeError> {
        match decl {
            Decl::Let {
                name,
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
                self.env.insert(name.clone(), scheme);
                Ok(())
            }

            Decl::FunBinding { .. } => {
                // Multi-clause functions are handled in check_program
                Ok(())
            }

            Decl::HandlerDef {
                name,
                effects: effect_names,
                needs,
                arms,
                return_clause,
                span,
                ..
            } => {
                self.register_handler(
                    name,
                    effect_names,
                    needs,
                    arms,
                    return_clause.as_deref(),
                    *span,
                )?;
                Ok(())
            }

            Decl::Import {
                module_path,
                alias,
                exposing,
                span,
                ..
            } => self.typecheck_import(module_path, alias.as_deref(), exposing.as_deref(), *span),

            // Type annotations, type defs (already registered), effects, traits, impls,
            // module declarations -- skip
            _ => Ok(()),
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
        where_constraints: &[(String, u32)],
    ) -> Result<(), TypeError> {
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
            self.where_bounds
                .entry(*var_id)
                .or_default()
                .insert(trait_name.clone());
        }

        // Snapshot pending constraints so we can partition new ones after body checking
        let constraints_before = self.pending_constraints.len();

        // Save and clear effect tracking and field candidate tracking for this function body
        let saved_effects = std::mem::take(&mut self.current_effects);
        let saved_effect_cache = std::mem::take(&mut self.effect_type_param_cache);
        let saved_field_candidates = std::mem::take(&mut self.field_candidates);

        // Pre-populate effect type param cache from annotation constraints (e.g. needs {State Int})
        if let Some(constraints) = self.fun_effect_type_constraints.get(name).cloned() {
            for (effect_name, concrete_types) in &constraints {
                if let Some(info) = self.effects.get(effect_name).cloned() {
                    let mapping: std::collections::HashMap<u32, Type> = info
                        .type_params
                        .iter()
                        .zip(concrete_types.iter())
                        .map(|(&param_id, ty)| (param_id, ty.clone()))
                        .collect();
                    self.effect_type_param_cache
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
                return Err(TypeError::at(
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
                    return Err(TypeError::at(
                        span,
                        "Effect calls are not allowed in guard expressions".to_string(),
                    ));
                }
                let guard_ty = self.infer_expr(guard)?;
                self.unify_at(&guard_ty, &Type::bool(), guard.span())?;
            }

            let body_ty = self.infer_expr(body)?;
            self.unify_at(&result_ty, &body_ty, body.span())?;

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
        let body_effects = std::mem::replace(&mut self.current_effects, saved_effects);
        self.effect_type_param_cache = saved_effect_cache;
        let declared_effects = self.fun_effects.get(name).cloned().unwrap_or_default();

        if !body_effects.is_empty() || !declared_effects.is_empty() {
            // Check for effects used but not declared
            let undeclared: Vec<_> = body_effects.difference(&declared_effects).collect();
            if !undeclared.is_empty() {
                let span = match clauses[0] {
                    Decl::FunBinding { span, .. } => *span,
                    _ => unreachable!(),
                };
                let mut effects: Vec<_> = undeclared.into_iter().cloned().collect();
                effects.sort();
                if declared_effects.is_empty() {
                    return Err(TypeError::at(
                        span,
                        format!(
                            "function '{}' uses effects {{{}}} but has no 'needs' declaration",
                            name,
                            effects.join(", ")
                        ),
                    ));
                } else {
                    return Err(TypeError::at(
                        span,
                        format!(
                            "function '{}' uses effect{{{}}} not declared in its 'needs' clause",
                            name,
                            effects.join(", ")
                        ),
                    ));
                }
            }
        }

        // Check for unresolved ambiguous field accesses. Any var still in field_candidates
        // after the full body was checked is genuinely ambiguous -- the programmer needs
        // to add a type annotation to disambiguate.
        let body_field_candidates =
            std::mem::replace(&mut self.field_candidates, saved_field_candidates);
        for (var_id, (record_names, field_span)) in body_field_candidates {
            let resolved = self.sub.apply(&Type::Var(var_id));
            if matches!(resolved, Type::Var(_)) {
                let mut names = record_names.clone();
                names.sort();
                return Err(TypeError::at(
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
                TypeError::at(
                    span,
                    format!("type annotation mismatch for '{}': {}", name, e.message),
                )
            })?;
        }

        // Partition new pending constraints: vars go to scheme, concrete stay for global check
        let new_constraints = self.pending_constraints.split_off(constraints_before);
        let mut scheme_constraints: Vec<(String, u32)> = Vec::new();
        for (trait_name, ty, span) in new_constraints {
            let resolved = self.sub.apply(&ty);
            match resolved {
                Type::Var(id) => {
                    // Covered by where clause -- satisfied, don't propagate
                    if self
                        .where_bounds
                        .get(&id)
                        .is_some_and(|b| b.contains(&trait_name))
                    {
                        continue;
                    }
                    if annotation.is_some() {
                        // Function has a type annotation: where clause must be explicit
                        return Err(TypeError::at(
                            span,
                            format!(
                                "trait {} required but not declared in where clause for '{}'",
                                trait_name, name
                            ),
                        ));
                    }
                    // No annotation -- infer as scheme constraint
                    scheme_constraints.push((trait_name, id));
                }
                _ => {
                    // Concrete type -- push back for global checking
                    self.pending_constraints.push((trait_name, ty, span));
                }
            }
        }

        // Remove the function's own pre-bound entry before generalizing,
        // otherwise its type vars appear in env_vars and block generalization
        self.env.remove(name);
        let mut scheme = self.generalize(&fun_ty);

        // Add explicit where clause constraints
        for (trait_name, var_id) in where_constraints {
            let resolved_id = match self.sub.apply(&Type::Var(*var_id)) {
                Type::Var(id) => id,
                _ => continue,
            };
            if scheme.forall.contains(&resolved_id) {
                scheme.constraints.push((trait_name.clone(), resolved_id));
            }
        }

        // Add inferred constraints from body
        for (trait_name, var_id) in scheme_constraints {
            if scheme.forall.contains(&var_id)
                && !scheme
                    .constraints
                    .iter()
                    .any(|(t, v)| t == &trait_name && *v == var_id)
            {
                scheme.constraints.push((trait_name, var_id));
            }
        }

        self.env.insert(name.into(), scheme);
        Ok(())
    }

    /// Check exhaustiveness of multi-clause function patterns using Maranget.
    fn check_fun_exhaustiveness(
        &self,
        name: &str,
        clauses: &[&Decl],
        param_types: &[Type],
    ) -> Result<(), TypeError> {
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
                return Err(TypeError::at(
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
                return Err(TypeError::at(
                    span,
                    format!(
                        "non-exhaustive clauses for '{}': missing {}",
                        name,
                        formatted.join(", ")
                    ),
                ));
            }
            return Err(TypeError::at(
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
    ) -> Result<(), TypeError> {
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
                for field in variant.fields.iter().rev() {
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
        }

        self.adt_variants.insert(
            name.into(),
            variants
                .iter()
                .map(|v| (v.name.clone(), v.fields.len()))
                .collect(),
        );

        Ok(())
    }

    pub(crate) fn register_record_def(
        &mut self,
        name: &str,
        fields: &[(String, ast::TypeExpr)],
    ) -> Result<(), TypeError> {
        let mut params: Vec<(String, u32)> = vec![];
        let field_types: Vec<(std::string::String, Type)> = fields
            .iter()
            .map(|(fname, texpr)| (fname.clone(), self.convert_type_expr(texpr, &mut params)))
            .collect();
        self.records.insert(name.into(), field_types);
        Ok(())
    }

    pub(crate) fn register_effect_def(
        &mut self,
        name: &str,
        effect_type_params: &[String],
        operations: &[ast::EffectOp],
    ) -> Result<(), TypeError> {
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
        for op in operations {
            // Start with the shared effect type params, then add op-local type vars
            let mut params_list = shared_params.clone();
            let param_types: Vec<Type> = op
                .params
                .iter()
                .map(|(_, texpr)| self.convert_type_expr(texpr, &mut params_list))
                .collect();
            let return_type = self.convert_type_expr(&op.return_type, &mut params_list);
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
            },
        );
        Ok(())
    }

    pub(crate) fn register_handler(
        &mut self,
        name: &str,
        effect_names: &[ast::EffectRef],
        needs: &[ast::EffectRef],
        arms: &[ast::HandlerArm],
        return_clause: Option<&ast::HandlerArm>,
        span: crate::token::Span,
    ) -> Result<(), TypeError> {
        // Save and clear effect tracking for this handler body
        let saved_effects = std::mem::take(&mut self.current_effects);
        let saved_effect_cache = std::mem::take(&mut self.effect_type_param_cache);

        // Build type param bindings from handler's effect refs.
        // E.g. `handler counter for State Int` with effect State s:
        //   creates mapping {s_var_id -> Int}
        let mut handler_type_mapping: std::collections::HashMap<u32, Type> =
            std::collections::HashMap::new();
        for effect_ref in effect_names {
            if let Some(info) = self.effects.get(&effect_ref.name) {
                let info = info.clone();
                for (i, &param_id) in info.type_params.iter().enumerate() {
                    if let Some(type_arg_expr) = effect_ref.type_args.get(i) {
                        let concrete_ty = self.convert_type_expr(type_arg_expr, &mut vec![]);
                        handler_type_mapping.insert(param_id, concrete_ty);
                    }
                }
            }
        }

        // Validate that each arm's operation belongs to the handler's declared effects
        for arm in arms {
            let mut belongs_to_declared = false;
            let mut matched_op: Option<EffectOpSig> = None;
            for effect_ref in effect_names {
                if let Some(info) = self.effects.get(&effect_ref.name)
                    && let Some(op) = info.ops.iter().find(|o| o.name == arm.op_name)
                {
                    belongs_to_declared = true;
                    // Apply handler type bindings to specialize the op signature
                    let specialized = EffectOpSig {
                        name: op.name.clone(),
                        params: op
                            .params
                            .iter()
                            .map(|t| self.replace_vars(t, &handler_type_mapping))
                            .collect(),
                        return_type: self.replace_vars(&op.return_type, &handler_type_mapping),
                    };
                    matched_op = Some(specialized);
                    break;
                }
            }
            if !belongs_to_declared {
                return Err(TypeError::at(
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
            self.resume_type = Some(op_sig.return_type.clone());

            for (i, param_name) in arm.params.iter().enumerate() {
                let param_ty = if i < op_sig.params.len() {
                    op_sig.params[i].clone()
                } else {
                    self.fresh_var()
                };
                self.env.insert(
                    param_name.clone(),
                    Scheme {
                        forall: vec![],
                        constraints: vec![],
                        ty: param_ty,
                    },
                );
            }

            self.infer_expr(&arm.body)?;
            self.resume_type = saved_resume;
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
            if let Some(param_name) = rc.params.first() {
                self.env.insert(
                    param_name.clone(),
                    Scheme {
                        forall: vec![],
                        constraints: vec![],
                        ty: param_ty,
                    },
                );
            }
            let ret_ty = self.infer_expr(&rc.body)?;
            self.resume_type = saved_resume;
            self.env = saved_env;
            Some((param_var_id, ret_ty))
        } else {
            None
        };

        // Check effect requirements against declared needs
        let body_effects = std::mem::replace(&mut self.current_effects, saved_effects);
        self.effect_type_param_cache = saved_effect_cache;
        let declared_effects: std::collections::HashSet<String> =
            needs.iter().map(|e| e.name.clone()).collect();

        if !body_effects.is_empty() || !declared_effects.is_empty() {
            let undeclared: Vec<_> = body_effects.difference(&declared_effects).collect();
            if !undeclared.is_empty() {
                let err_span = arms.first().map(|a| a.span).unwrap_or(span);
                let mut effects: Vec<_> = undeclared.into_iter().cloned().collect();
                effects.sort();
                if declared_effects.is_empty() {
                    return Err(TypeError::at(
                        err_span,
                        format!(
                            "handler '{}' uses effects {{{}}} but has no 'needs' declaration",
                            name,
                            effects.join(", ")
                        ),
                    ));
                } else {
                    return Err(TypeError::at(
                        err_span,
                        format!(
                            "handler '{}' uses effects {{{}}} not declared in its 'needs' clause",
                            name,
                            effects.join(", ")
                        ),
                    ));
                }
            }
        }

        self.handlers.insert(
            name.into(),
            HandlerInfo {
                effects: effect_names.iter().map(|e| e.name.clone()).collect(),
                return_type: handler_return_type,
            },
        );

        // Put the handler name in the env so it can be referenced
        self.env.insert(
            name.into(),
            Scheme {
                forall: vec![],
                constraints: vec![],
                ty: Type::unit(), // handlers don't have a meaningful standalone type
            },
        );

        Ok(())
    }

    // --- Trait constraint checking ---

    pub(crate) fn check_pending_constraints(&mut self) -> Result<(), TypeError> {
        // Build resolved where bounds (substitution may have chained var IDs)
        let mut resolved_bounds: std::collections::HashMap<u32, std::collections::HashSet<String>> =
            std::collections::HashMap::new();
        for (&var_id, traits) in &self.where_bounds {
            if let Type::Var(resolved_id) = self.sub.apply(&Type::Var(var_id)) {
                resolved_bounds
                    .entry(resolved_id)
                    .or_default()
                    .extend(traits.iter().cloned());
            }
        }

        // Process constraints in a loop since conditional impls may push new ones
        loop {
            let constraints = std::mem::take(&mut self.pending_constraints);
            if constraints.is_empty() {
                break;
            }
            for (trait_name, ty, span) in constraints {
                let resolved = self.sub.apply(&ty);
                match &resolved {
                    // Concrete type (includes primitives): check that an impl exists
                    Type::Con(type_name, args) => {
                        let impl_info = self
                            .trait_impls
                            .get(&(trait_name.clone(), type_name.clone()));
                        match impl_info {
                            None => {
                                return Err(TypeError::at(
                                    span,
                                    format!("no impl of {} for {}", trait_name, type_name),
                                ));
                            }
                            Some(info) => {
                                // Record evidence for the elaboration pass
                                self.evidence.push(super::TraitEvidence {
                                    span,
                                    trait_name: trait_name.clone(),
                                    resolved_type: Some((type_name.clone(), args.clone())),
                                });
                                // Push conditional constraints for type parameters
                                if type_name == "Tuple" {
                                    // Tuples: propagate the trait to all elements
                                    for arg_ty in args {
                                        self.pending_constraints.push((
                                            trait_name.clone(),
                                            arg_ty.clone(),
                                            span,
                                        ));
                                    }
                                } else {
                                    for (req_trait, param_idx) in &info.param_constraints {
                                        if let Some(arg_ty) = args.get(*param_idx) {
                                            self.pending_constraints.push((
                                                req_trait.clone(),
                                                arg_ty.clone(),
                                                span,
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
                            return Err(TypeError::at(
                                span,
                                format!(
                                    "trait {} required but no impl or where clause bound for this type",
                                    trait_name
                                ),
                            ));
                        }
                        // Record evidence for polymorphic passthrough
                        self.evidence.push(super::TraitEvidence {
                            span,
                            trait_name: trait_name.clone(),
                            resolved_type: None,
                        });
                    }
                    Type::Arrow(_, _) | Type::EffArrow(_, _, _) => {
                        return Err(TypeError::at(
                            span,
                            format!("no impl of {} for function type", trait_name),
                        ));
                    }
                }
            }
        }
        Ok(())
    }

    // --- Supertrait checking ---

    /// Verify that every impl's trait has its supertraits also implemented for the same type.
    pub(crate) fn check_supertrait_impls(&self) -> Result<(), TypeError> {
        for ((trait_name, target_type), impl_info) in &self.trait_impls {
            if let Some(trait_info) = self.traits.get(trait_name) {
                for supertrait in &trait_info.supertraits {
                    if !self
                        .trait_impls
                        .contains_key(&(supertrait.clone(), target_type.clone()))
                    {
                        let msg = format!(
                            "impl {} for {} requires impl {} for {} (supertrait)",
                            trait_name, target_type, supertrait, target_type
                        );
                        return Err(match impl_info.span {
                            Some(span) => TypeError::at(span, msg),
                            None => TypeError::new(msg),
                        });
                    }
                }
            }
        }
        Ok(())
    }
}
