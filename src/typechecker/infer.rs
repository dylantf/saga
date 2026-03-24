use crate::ast::{BinOp, CaseArm, Expr, ExprKind, Lit, NodeId, Pat, Stmt};

use super::{Checker, Diagnostic, EffectRow, Scheme, Type};
use crate::token::Span;

impl Checker {
    // --- Expression inference ---

    pub(crate) fn infer_expr(&mut self, expr: &Expr) -> Result<(Type, EffectRow), Diagnostic> {
        let span = expr.span;
        let node_id = expr.id;
        match &expr.kind {
            ExprKind::Lit { value, .. } => Ok((match value {
                Lit::Int(_) => Type::int(),
                Lit::Float(_) => Type::float(),
                Lit::String(_) => Type::string(),
                Lit::Bool(_) => Type::bool(),
                Lit::Unit => Type::unit(),
            }, EffectRow::empty())),

            ExprKind::Var { name, .. } => {
                if let Some(scheme) = self.env.get(name) {
                    let scheme = scheme.clone();
                    // Propagate effect type params from callee's annotations.
                    // e.g. calling `counter` which has `needs {Actor CounterMsg}`
                    // populates the cache so lambdas can build typed EffArrows.
                    if let Some(constraints) = self.effect_meta.fun_type_constraints.get(name).cloned() {
                        for (effect_name, concrete_types) in &constraints {
                            if let Some(info) = self.effects.get(effect_name).cloned() {
                                let mapping: std::collections::HashMap<u32, Type> = info
                                    .type_params
                                    .iter()
                                    .zip(concrete_types.iter())
                                    .map(|(&param_id, ty)| (param_id, ty.clone()))
                                    .collect();
                                self.effect_meta.type_param_cache
                                    .insert(effect_name.clone(), mapping);
                            }
                        }
                    }
                    let (mut ty, constraints) = self.instantiate(&scheme);
                    for (trait_name, trait_ty) in constraints {
                        self.trait_state.pending_constraints
                            .push((trait_name, trait_ty, span, node_id));
                    }
                    // If this function has effect type constraints, convert the
                    // outermost Arrow to EffArrow so spawn! can link type args.
                    if let Some(eff_constraints) =
                        self.effect_meta.fun_type_constraints.get(name).cloned()
                        && let Type::Fun(a, b, _) = ty
                    {
                        let eff_refs: Vec<(String, Vec<Type>)> =
                            eff_constraints.into_iter().collect();
                        ty = Type::Fun(a, b, super::EffectRow::closed(eff_refs));
                    }
                    // Effects are committed when the App chain saturates
                    // via the type-directed path. No special handling for Var.
                    self.record_type(node_id, &ty);
                    // Record reference: this usage resolves to the definition
                    if let Some(def_id) = self.env.def_id(name) {
                        self.record_reference(node_id, span, def_id);
                    }
                    Ok((ty, EffectRow::empty()))
                } else {
                    Err(Diagnostic::error_at(
                        span,
                        format!("undefined variable: {}", name),
                    ))
                }
            }

            ExprKind::Constructor { name, .. } => {
                if let Some(scheme) = self.constructors.get(name) {
                    let scheme = scheme.clone();
                    let (ty, _) = self.instantiate(&scheme);
                    self.record_type(node_id, &ty);
                    if let Some(def_id) = self.lsp.constructor_def_ids.get(name).copied() {
                        self.record_reference(node_id, span, def_id);
                    }
                    Ok((ty, EffectRow::empty()))
                } else {
                    Err(Diagnostic::error_at(
                        span,
                        format!("undefined constructor: {}", name),
                    ))
                }
            }

            ExprKind::App { func, arg, .. } => {
                let (func_ty, func_effs) = self.infer_expr(func)?;
                let (arg_ty, arg_effs) = self.infer_expr(arg)?;
                let arg_ty_pre = arg_ty.clone(); // Save before move for effect subtype check
                let ret_ty = self.fresh_var();
                let eff_row_var = self.fresh_var();
                if self
                    .unify_at(
                        &func_ty,
                        &Type::Fun(
                            Box::new(arg_ty),
                            Box::new(ret_ty.clone()),
                            EffectRow { effects: vec![], tail: Some(Box::new(eff_row_var)) },
                        ),
                        span,
                    )
                    .is_err()
                {
                    let resolved = self.sub.apply(&func_ty);
                    let display = self.prettify_type(&resolved);
                    return Err(Diagnostic::error_at(
                        func.span,
                        format!("{} is not a function", display),
                    ));
                }

                // Effect subtyping check: when passing a function-typed argument,
                // its effects must be a subset of the parameter's expected effects.
                // This prevents effectful callbacks from being silently accepted
                // where pure (or less-effectful) callbacks are expected.
                {
                    let resolved_func = self.sub.apply(&func_ty);
                    if let Type::Fun(param, _, _) = &resolved_func {
                        self.check_callback_effect_subtype(&arg_ty_pre, param, arg.span)?;
                    }
                }

                let resolved_ret = self.sub.apply(&ret_ty);
                self.record_type(node_id, &ret_ty);

                // Build the returned EffectRow: func + arg + (if saturated) callee.
                let mut merged_effs = func_effs.merge(&arg_effs);

                // Absorption: if the function's parameter type is itself a Fun
                // with a declared effect row (e.g. `f: () -> a needs {Fail}`),
                // subtract those declared effects. The parameter's effects are
                // the function's responsibility, not the caller's.
                //
                // We use resolve_var (not full apply) to get the parameter type
                // structure without chasing row_map, so only the statically
                // declared effects are subtracted -- not effects captured by a
                // row variable (..e) which should propagate to the caller.
                let func_shallow = self.sub.resolve_var(&func_ty);
                if let Type::Fun(p, _, _) = func_shallow {
                    let param_shallow = self.sub.resolve_var(p);
                    if let Type::Fun(_, _, row) = param_shallow {
                        let absorbed: std::collections::HashSet<String> = row
                            .effects.iter().map(|(n, _)| n.clone()).collect();
                        merged_effs = merged_effs.subtract(&absorbed);
                    }
                }

                // Saturated call: add the callee's own effect row
                if !matches!(resolved_ret, Type::Fun(_, _, _)) {
                    let resolved_func = self.sub.apply(&func_ty);
                    if let Type::Fun(_, _, row) = &resolved_func {
                        let applied_row = self.sub.apply_effect_row(row);
                        merged_effs = merged_effs.merge(&applied_row);
                    }
                }

                Ok((ret_ty, merged_effs))
            }

            ExprKind::BinOp {
                op, left, right, ..
            } => {
                let (left_ty, _left_effs) = self.infer_expr(left)?;
                let (right_ty, _right_effs) = self.infer_expr(right)?;
                match op {
                    BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::FloatDiv | BinOp::IntDiv => {
                        self.unify_at(&left_ty, &right_ty, span)?;
                        self.trait_state.pending_constraints.push((
                            "Num".into(),
                            left_ty.clone(),
                            span,
                            node_id,
                        ));
                        Ok((left_ty, EffectRow::empty()))
                    }
                    BinOp::Mod => {
                        self.unify_at(&left_ty, &Type::int(), span)?;
                        self.unify_at(&right_ty, &Type::int(), span)?;
                        Ok((Type::int(), EffectRow::empty()))
                    }
                    BinOp::Eq | BinOp::NotEq => {
                        self.unify_at(&left_ty, &right_ty, span)?;
                        self.trait_state.pending_constraints.push((
                            "Eq".into(),
                            left_ty.clone(),
                            span,
                            node_id,
                        ));
                        Ok((Type::bool(), EffectRow::empty()))
                    }
                    BinOp::Lt | BinOp::Gt | BinOp::LtEq | BinOp::GtEq => {
                        self.unify_at(&left_ty, &right_ty, span)?;
                        self.trait_state.pending_constraints.push((
                            "Ord".into(),
                            left_ty.clone(),
                            span,
                            node_id,
                        ));
                        Ok((Type::bool(), EffectRow::empty()))
                    }
                    BinOp::And | BinOp::Or => {
                        self.unify_at(&left_ty, &Type::bool(), span)?;
                        self.unify_at(&right_ty, &Type::bool(), span)?;
                        Ok((Type::bool(), EffectRow::empty()))
                    }
                    BinOp::Concat => {
                        self.unify_at(&Type::string(), &left_ty, span)?;
                        self.unify_at(&Type::string(), &right_ty, span)?;
                        Ok((Type::string(), EffectRow::empty()))
                    }
                }
            }

            ExprKind::UnaryMinus { expr: inner, .. } => {
                let (ty, _effs) = self.infer_expr(inner)?;
                self.trait_state.pending_constraints
                    .push(("Num".into(), ty.clone(), span, node_id));
                Ok((ty, EffectRow::empty()))
            }

            ExprKind::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => {
                let (cond_ty, cond_effs) = self.infer_expr(cond)?;
                self.unify_at(&cond_ty, &Type::bool(), cond.span)?;
                let (then_ty, then_effs) = self.infer_expr(then_branch)?;
                let (else_ty, else_effs) = self.infer_expr(else_branch)?;
                self.unify_at(&then_ty, &else_ty, span)?;
                let mut merged_effs = cond_effs;
                merged_effs.effects.extend(then_effs.effects);
                merged_effs.effects.extend(else_effs.effects);
                let mut seen = std::collections::HashSet::new();
                merged_effs.effects.retain(|(name, _)| seen.insert(name.clone()));
                Ok((then_ty, merged_effs))
            }

            ExprKind::Block { stmts, .. } => self.infer_block(stmts),

            ExprKind::Lambda { params, body, .. } => self.infer_lambda(params, body),


            ExprKind::Case {
                scrutinee, arms, ..
            } => {
                let (scrut_ty, scrut_effs) = self.infer_expr(scrutinee)?;
                let result_ty = self.fresh_var();
                let mut merged_effs = scrut_effs;

                for arm in arms {
                    let saved_env = self.env.clone();

                    self.bind_pattern(&arm.pattern, &scrut_ty)?;

                    if let Some(guard) = &arm.guard {
                        self.check_guard(guard)?;
                    }

                    let (body_ty, body_effs) = self.infer_expr(&arm.body)?;
                    merged_effs.effects.extend(body_effs.effects);
                    self.unify_at(&result_ty, &body_ty, arm.body.span)?;

                    self.env = saved_env;
                }

                self.check_exhaustiveness(arms, &scrut_ty, span)?;

                let mut seen = std::collections::HashSet::new();
                merged_effs.effects.retain(|(name, _)| seen.insert(name.clone()));
                Ok((result_ty, merged_effs))
            }

            ExprKind::RecordCreate { name, fields, .. } => {
                let ty = self.infer_record_create(name, fields, span)?;
                Ok((ty, EffectRow::empty()))
            }

            ExprKind::AnonRecordCreate { fields, .. } => {
                let ty = self.infer_anon_record_create(fields)?;
                Ok((ty, EffectRow::empty()))
            }

            ExprKind::FieldAccess {
                expr: inner, field, ..
            } => {
                let ty = self.infer_field_access(inner, field, span)?;
                Ok((ty, EffectRow::empty()))
            }

            ExprKind::RecordUpdate { record, fields, .. } => {
                let ty = self.infer_record_update(record, fields, span)?;
                Ok((ty, EffectRow::empty()))
            }

            ExprKind::EffectCall {
                name, qualifier, ..
            } => {
                let op_sig = self.lookup_effect_op(name, qualifier.as_deref(), span)?;

                // Record call site -> handler arm for LSP go-to-def (level 1).
                // Scan the with-stack innermost-first; first match wins (innermost shadows outer).
                if let Some((arm_span, arm_module)) = self
                    .lsp
                    .with_arm_stacks
                    .iter()
                    .rev()
                    .find_map(|map| map.get(name.as_str()))
                {
                    self.lsp.effect_call_targets
                        .insert(span, (*arm_span, arm_module.clone()));
                }

                // Build curried function type: param1 -> param2 -> ... -> return_type
                let mut ty = op_sig.return_type.clone();
                if op_sig.params.is_empty() {
                    // Zero-param ops like `get! ()` still take a Unit argument
                    ty = Type::arrow(Type::unit(), ty);
                } else {
                    for (_, param_ty) in op_sig.params.iter().rev() {
                        ty = Type::arrow(param_ty.clone(), ty);
                    }
                }
                let eff_row = if let Some(effect_name) = self.effect_for_op(name, qualifier.as_deref()) {
                    EffectRow::closed(vec![(effect_name.clone(), vec![])])
                } else {
                    EffectRow::empty()
                };
                Ok((ty, eff_row))
            }

            ExprKind::With {
                expr: inner,
                handler,
                ..
            } => {
                let (ty, effs) = self.infer_with(inner, handler, span, node_id)?;
                Ok((ty, effs))
            }

            ExprKind::Resume { value, .. } => {
                let (val_ty, _effs) = self.infer_expr(value)?;
                if let Some(expected) = &self.resume_type.clone() {
                    self.unify_at(&val_ty, expected, span)?;
                }
                // resume's return type is the answer type (what the with-expression produces)
                if let Some(ret_ty) = &self.resume_return_type.clone() {
                    Ok((ret_ty.clone(), EffectRow::empty()))
                } else {
                    let ty = self.fresh_var();
                    Ok((ty, EffectRow::empty()))
                }
            }

            ExprKind::Tuple { elements, .. } => {
                let tys: Vec<Type> = elements
                    .iter()
                    .map(|e| self.infer_expr(e).map(|(ty, _effs)| ty))
                    .collect::<Result<_, _>>()?;
                Ok((Type::Con("Tuple".into(), tys), EffectRow::empty()))
            }

            ExprKind::QualifiedName { module, name, .. } => {
                // Empty name means incomplete module access (e.g. `Math.`).
                // Return a fresh type var so inference can continue.
                if name.is_empty() {
                    return Ok((self.fresh_var(), EffectRow::empty()));
                }
                let key = format!("{}.{}", module, name);
                match self.env.get(&key).cloned() {
                    Some(scheme) => {
                        let (ty, constraints) = self.instantiate(&scheme);
                        for (trait_name, trait_ty) in constraints {
                            self.trait_state.pending_constraints
                                .push((trait_name, trait_ty, span, node_id));
                        }
                        if let Some(def_id) = self.env.def_id(&key) {
                            self.record_reference(node_id, span, def_id);
                        }
                        Ok((ty, EffectRow::empty()))
                    }
                    None => Err(Diagnostic::error_at(
                        span,
                        format!("unknown qualified name '{}.{}'", module, name),
                    )),
                }
            }

            ExprKind::Do {
                bindings,
                success,
                else_arms,
                ..
            } => {
                let result_ty = self.fresh_var();
                let saved_env = self.env.clone();
                let mut merged_effs = EffectRow::empty();

                // Type-check each binding in sequence; env accumulates bound vars.
                // Also collect the inferred types for exhaustiveness checking later.
                let mut binding_types: Vec<Type> = Vec::new();
                for (pat, expr) in bindings {
                    let (expr_ty, expr_effs) = self.infer_expr(expr)?;
                    merged_effs.effects.extend(expr_effs.effects);
                    self.bind_pattern(pat, &expr_ty)?;
                    binding_types.push(expr_ty);
                }

                // Success expression runs in do-block scope; its type is the
                // success-path return type.
                let (success_ty, success_effs) = self.infer_expr(success)?;
                merged_effs.effects.extend(success_effs.effects);
                self.unify_at(&result_ty, &success_ty, success.span)?;

                // Restore env so else arms only see the outer scope
                self.env = saved_env.clone();

                // Type-check else arms: each gets a fresh scrutinee type; body
                // types are unified with result_ty.
                for arm in else_arms {
                    let arm_saved = self.env.clone();
                    let scrutinee_ty = self.fresh_var();
                    self.bind_pattern(&arm.pattern, &scrutinee_ty)?;
                    let (body_ty, body_effs) = self.infer_expr(&arm.body)?;
                    merged_effs.effects.extend(body_effs.effects);
                    self.unify_at(&result_ty, &body_ty, arm.body.span)?;
                    self.env = arm_saved;
                }

                // Exhaustiveness: collect bail constructors from all bindings
                // and check that else arms cover them all.
                self.check_do_exhaustiveness(bindings, &binding_types, else_arms, span)?;

                // do-block bindings must not leak into the surrounding scope
                self.env = saved_env;
                let mut seen = std::collections::HashSet::new();
                merged_effs.effects.retain(|(name, _)| seen.insert(name.clone()));
                Ok((result_ty, merged_effs))
            }

            ExprKind::Receive {
                arms, after_clause, ..
            } => {
                self.infer_receive(
                    arms,
                    after_clause.as_ref().map(|(t, b)| (t.as_ref(), b.as_ref())),
                    span,
                )
            }

            ExprKind::Ascription {
                expr: inner,
                type_expr,
                ..
            } => {
                let (inferred, _effs) = self.infer_expr(inner)?;
                let ann_ty = self.convert_type_expr(type_expr, &mut vec![]);
                self.unify_at(&inferred, &ann_ty, span)?;
                self.record_type(node_id, &ann_ty);
                Ok((ann_ty, EffectRow::empty()))
            }

            ExprKind::DictMethodAccess { .. }
            | ExprKind::DictRef { .. }
            | ExprKind::ForeignCall { .. } => {
                unreachable!("elaboration-only construct in typechecker")
            }

            ExprKind::Pipe { .. }
            | ExprKind::PipeBack { .. }
            | ExprKind::ComposeForward { .. }
            | ExprKind::ComposeBack { .. }
            | ExprKind::Cons { .. }
            | ExprKind::ListLit { .. }
            | ExprKind::StringInterp { .. }
            | ExprKind::ListComprehension { .. } => {
                unreachable!("surface syntax should be desugared before typechecking")
            }
        }
    }

    /// Check that a guard expression is a pure Bool.
    fn check_guard(&mut self, guard: &Expr) -> Result<(), Diagnostic> {
        if let Some(span) = super::find_effect_call(guard) {
            return Err(Diagnostic::error_at(
                span,
                "Effect calls are not allowed in guard expressions".to_string(),
            ));
        }
        let (guard_ty, _effs) = self.infer_expr(guard)?;
        self.unify_at(&guard_ty, &Type::bool(), guard.span)
    }

    fn infer_lambda(&mut self, params: &[Pat], body: &Expr) -> Result<(Type, EffectRow), Diagnostic> {
        let saved_env = self.env.clone();
        // Save and clear type_param_cache, then inherit the outer cache so
        // effect ops (e.g. get!) resolve type params from enclosing annotations.
        let saved_cache = self.effect_meta.type_param_cache.clone();
        self.effect_meta.type_param_cache = saved_cache.clone();

        let mut param_types = Vec::new();
        for pat in params {
            let ty = self.fresh_var();
            self.bind_pattern(pat, &ty)?;
            param_types.push(ty);
        }

        let (body_ty, body_effs) = self.infer_expr(body)?;
        self.env = saved_env;

        // Restore the type_param_cache
        self.effect_meta.type_param_cache = saved_cache;

        // Build curried arrow: a -> b -> c -> ret
        let mut ty = body_ty;
        for param_ty in param_types.into_iter().rev() {
            ty = Type::arrow(param_ty, ty);
        }

        // If the lambda has effects, wrap the outermost arrow with the effect row
        let propagated_effs = body_effs.clone();
        if !body_effs.effects.is_empty()
            && let Type::Fun(a, b, _) = ty
        {
            ty = Type::Fun(a, b, body_effs);
        }

        // Lambda effects propagate to the enclosing function's effect check.
        Ok((ty, propagated_effs))
    }

    fn infer_receive(
        &mut self,
        arms: &[CaseArm],
        after_clause: Option<(&Expr, &Expr)>,
        span: Span,
    ) -> Result<(Type, EffectRow), Diagnostic> {
        // Look up Actor effect's message type from the effect type param cache
        let msg_ty = match (
            self.effect_meta.type_param_cache.get("Actor"),
            self.effects.get("Actor"),
        ) {
            (Some(cache), Some(info)) => {
                let param_id = info.type_params.first().ok_or_else(|| {
                    Diagnostic::error_at(span, "Actor effect has no type parameter".to_string())
                })?;
                cache
                    .get(param_id)
                    .cloned()
                    .unwrap_or_else(|| self.fresh_var())
            }
            _ => {
                return Err(Diagnostic::error_at(
                    span,
                    "receive requires the Actor effect (declare `needs {Actor MsgType}`)"
                        .to_string(),
                ));
            }
        };

        let result_ty = self.fresh_var();

        for arm in arms {
            let saved_env = self.env.clone();

            // System message patterns (Down, Exit) are not part of the user's message type
            if let Pat::Constructor {
                name,
                args,
                span: pat_span,
                ..
            } = &arm.pattern
                && matches!(name.as_str(), "Down" | "Exit")
            {
                if args.len() != 2 {
                    return Err(Diagnostic::error_at(
                        *pat_span,
                        format!(
                            "{} pattern requires exactly 2 arguments: {}(pid, reason)",
                            name, name
                        ),
                    ));
                }
                let msg_var = self.fresh_var();
                let pid_ty = Type::Con("Pid".into(), vec![msg_var]);
                self.bind_pattern(&args[0], &pid_ty)?;
                self.bind_pattern(&args[1], &Type::Con("ExitReason".into(), vec![]))?;
            } else {
                self.bind_pattern(&arm.pattern, &msg_ty)?;
            }

            if let Some(guard) = &arm.guard {
                self.check_guard(guard)?;
            }

            let (body_ty, _body_effs) = self.infer_expr(&arm.body)?;
            self.unify_at(&result_ty, &body_ty, arm.body.span)?;
            self.env = saved_env;
        }

        if let Some((timeout, body)) = after_clause {
            let (timeout_ty, _timeout_effs) = self.infer_expr(timeout)?;
            self.unify_at(&timeout_ty, &Type::int(), timeout.span)?;
            let (body_ty, _body_effs) = self.infer_expr(body)?;
            self.unify_at(&result_ty, &body_ty, body.span)?;
        }

        Ok((result_ty, EffectRow::closed(vec![("Actor".to_string(), vec![])])))
    }

    pub(crate) fn infer_block(&mut self, stmts: &[Stmt]) -> Result<(Type, EffectRow), Diagnostic> {
        let mut last_ty = Type::unit();
        let mut merged_effs = EffectRow::empty();
        let mut errors: Vec<Diagnostic> = Vec::new();
        let mut i = 0;
        while i < stmts.len() {
            match &stmts[i] {
                Stmt::Let {
                    pattern,
                    annotation,
                    value,
                    span,
                    ..
                } => {
                    let ty = match self.infer_expr(value) {
                        Ok((ty, val_effs)) => {
                            merged_effs.effects.extend(val_effs.effects);
                            if let Some(ann) = annotation {
                                let ann_ty = self.convert_type_expr(ann, &mut vec![]);
                                if let Err(e) = self.unify_at(&ty, &ann_ty, *span) {
                                    errors.push(e);
                                    Type::Error
                                } else {
                                    ty
                                }
                            } else {
                                ty
                            }
                        }
                        Err(e) => {
                            errors.push(e);
                            Type::Error
                        }
                    };
                    // Check if this let binding carries deferred effects (partial
                    // application of an effectful function).
                    let resolved_ty = self.sub.apply(&ty);
                    let has_deferred_effects = !super::effects_from_type(&resolved_ty).is_empty();
                    if let Pat::Var {
                        id: pat_id,
                        name,
                        span: var_span,
                        ..
                    } = pattern
                    {
                        self.generalize_let_binding(
                            name, *pat_id, *var_span, &ty, has_deferred_effects,
                        );
                    } else {
                        if let Err(e) = self.bind_pattern(pattern, &ty) {
                            errors.push(e);
                        }
                        if let Err(e) = self.check_let_pattern_irrefutable(pattern, &ty)
                        {
                            errors.push(e);
                        }
                    }
                    last_ty = Type::unit();
                    i += 1;
                }
                Stmt::LetFun {
                    id,
                    name,
                    name_span,
                    span,
                    ..
                } => {
                    // Group consecutive LetFun clauses with the same name
                    let fun_name = name.clone();
                    let fun_id = *id;
                    let fun_name_span = *name_span;
                    let fun_span = *span;
                    type Clause<'a> = (&'a [Pat], &'a Option<Box<Expr>>, &'a Expr);
                    let mut clauses: Vec<Clause> = Vec::new();
                    while i < stmts.len() {
                        if let Stmt::LetFun {
                            name: n,
                            params,
                            guard,
                            body,
                            ..
                        } = &stmts[i]
                        {
                            if *n != fun_name {
                                break;
                            }
                            clauses.push((params, guard, body));
                            i += 1;
                        } else {
                            break;
                        }
                    }

                    // Create a fresh type var for the function and insert it
                    // into env before checking clauses (enables recursion)
                    let fun_ty = self.fresh_var();
                    self.env.insert_with_def(
                        fun_name.clone(),
                        Scheme {
                            forall: vec![],
                            constraints: vec![],
                            ty: fun_ty.clone(),
                        },
                        fun_id,
                    );
                    self.lsp.node_spans.insert(fun_id, fun_name_span);

                    // Check each clause like a lambda, unifying with fun_ty
                    let arity = clauses[0].0.len();
                    for (params, guard, body) in &clauses {
                        if params.len() != arity {
                            return Err(Diagnostic::error_at(
                                fun_span,
                                format!(
                                    "clause for '{}' has {} parameters, expected {}",
                                    fun_name,
                                    params.len(),
                                    arity
                                ),
                            ));
                        }
                        let saved_env = self.env.clone();
                        let mut param_types = Vec::new();
                        for pat in *params {
                            let ty = self.fresh_var();
                            self.bind_pattern(pat, &ty)?;
                            param_types.push(ty);
                        }
                        if let Some(g) = guard {
                            let (guard_ty, _guard_effs) = self.infer_expr(g)?;
                            self.unify_at(&guard_ty, &Type::bool(), g.span)?;
                        }
                        let (body_ty, _body_effs) = self.infer_expr(body)?;
                        // Build curried arrow type
                        let mut clause_ty = body_ty;
                        for param_ty in param_types.into_iter().rev() {
                            clause_ty = Type::arrow(param_ty, clause_ty);
                        }
                        self.unify_at(&fun_ty, &clause_ty, fun_span)?;
                        self.env = saved_env;
                    }

                    // Generalize and update env with the final type
                    let scheme = self.generalize(&fun_ty);
                    self.env.insert(fun_name, scheme);
                    last_ty = Type::unit();
                }
                Stmt::Expr(expr) => {
                    match self.infer_expr(expr) {
                        Ok((ty, expr_effs)) => {
                            merged_effs.effects.extend(expr_effs.effects);
                            // Warn if a non-unit value is discarded (not last statement).
                            // Deferred: the type may still contain unresolved variables.
                            if i + 1 < stmts.len() {
                                self.pending_warnings.push(super::PendingWarning::DiscardedValue {
                                    span: expr.span,
                                    ty: ty.clone(),
                                });
                            }
                            last_ty = ty;
                        }
                        Err(e) => {
                            errors.push(e);
                            last_ty = Type::Error;
                        }
                    }
                    i += 1;
                }
            }
        }
        if !errors.is_empty() {
            // Return the first error (others are collected on self.collected_diagnostics)
            let first = errors.remove(0);
            self.collected_diagnostics.extend(errors);
            Err(first)
        } else {
            let mut seen = std::collections::HashSet::new();
            merged_effs.effects.retain(|(name, _)| seen.insert(name.clone()));
            Ok((last_ty, merged_effs))
        }
    }

    /// Generalize a let-bound variable: absorb trait constraints into the
    /// scheme, record dict params for the elaborator, and register metadata
    /// (env entry, spans, definitions, deferred effects).
    fn generalize_let_binding(
        &mut self,
        name: &str,
        pat_id: NodeId,
        var_span: Span,
        ty: &Type,
        has_deferred_effects: bool,
    ) {
        let mut scheme = self.generalize(ty);

        // Absorb pending trait constraints for generalized vars
        // so let-bound values can be polymorphic over traits.
        // e.g. `let f = debug >> println` gets scheme
        // `forall a. a -> Unit where {a: Debug}`
        self.trait_state.pending_constraints
            .retain(|(trait_name, cty, _span, node_id)| {
                let resolved = self.sub.apply(cty);
                if let Type::Var(id) = resolved
                    && scheme.forall.contains(&id)
                {
                    if !scheme
                        .constraints
                        .iter()
                        .any(|(t, v)| t == trait_name && *v == id)
                    {
                        scheme.constraints.push((trait_name.clone(), id));
                    }
                    self.evidence.push(super::TraitEvidence {
                        node_id: *node_id,
                        trait_name: trait_name.clone(),
                        resolved_type: None,
                        type_var_name: None,
                    });
                    return false; // remove from pending
                }
                true // keep in pending
            });

        // Record dict params for the elaborator
        let operator_traits: std::collections::HashSet<&str> =
            ["Num", "Eq"].into_iter().collect();
        let dict_params: Vec<(String, String)> = scheme
            .constraints
            .iter()
            .filter(|(t, _)| !operator_traits.contains(t.as_str()))
            .map(|(t, id)| (t.clone(), format!("v{}", id)))
            .collect();
        if !dict_params.is_empty() {
            let resolved_ty = self.sub.apply(ty);
            let mut arity = 0usize;
            let mut t = &resolved_ty;
            while let Type::Fun(_, ret, _) = t {
                arity += 1;
                t = ret;
            }
            self.let_dict_params
                .insert(name.to_string(), (dict_params, arity));
        }

        self.env
            .insert_with_def(name.to_string(), scheme, pat_id);
        if has_deferred_effects {
            self.effect_meta.known_let_bindings.insert(name.to_string());
        }
        self.lsp.node_spans.insert(pat_id, var_span);
        self.record_type_at_span(var_span, ty);
        self.lsp.definitions
            .push((pat_id, name.to_string(), var_span));
    }

    /// Check that a function-typed argument's effect row is compatible with
    /// the expected parameter's effect row. When both rows are closed, the
    /// argument's effects must be a subset of the parameter's effects.
    ///
    /// This enforces directional effect subtyping at call sites: a pure
    /// function can be passed where an effectful callback is expected, but
    /// NOT the reverse.
    fn check_callback_effect_subtype(
        &self,
        actual_arg: &Type,
        expected_param: &Type,
        span: Span,
    ) -> Result<(), Diagnostic> {
        let actual = self.sub.apply(actual_arg);
        let expected = self.sub.apply(expected_param);
        if let (Type::Fun(_, _, actual_row), Type::Fun(_, _, expected_row)) = (&actual, &expected) {
            let actual_row = self.sub.apply_effect_row(actual_row);
            let expected_row = self.sub.apply_effect_row(expected_row);
            // Only check when both rows are closed (open rows accept any extras)
            if actual_row.tail.is_none() && expected_row.tail.is_none() {
                let mut extra_effects: Vec<&str> = actual_row
                    .effects
                    .iter()
                    .filter(|(n, _)| !expected_row.effects.iter().any(|(en, _)| en == n))
                    .map(|(n, _)| n.as_str())
                    .collect();
                if !extra_effects.is_empty() {
                    extra_effects.sort();
                    let msg = if expected_row.effects.is_empty() {
                        format!(
                            "effectful function (uses {{{}}}) passed where a pure callback is expected",
                            extra_effects.join(", ")
                        )
                    } else {
                        let mut expected_names: Vec<&str> = expected_row
                            .effects
                            .iter()
                            .map(|(n, _)| n.as_str())
                            .collect();
                        expected_names.sort();
                        format!(
                            "function uses effects {{{}}} not allowed by callback parameter (allows {{{}}})",
                            extra_effects.join(", "),
                            expected_names.join(", ")
                        )
                    };
                    return Err(Diagnostic::error_at(span, msg));
                }
            }
        }
        Ok(())
    }
}
