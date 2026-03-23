use crate::ast::{BinOp, CaseArm, Expr, ExprKind, Lit, NodeId, Pat, Stmt};

use super::{Checker, Diagnostic, Scheme, Type};
use crate::token::Span;

/// Walk an App chain to find the callee name at the root.
/// e.g. `App(App(Var("f"), a), b)` -> Some("f")
///       `App(QualifiedName("M", "f"), a)` -> Some("M.f")
/// Returns None if the callee isn't a Var or QualifiedName.
pub(super) fn extract_callee_name(expr: &Expr) -> Option<String> {
    match &expr.kind {
        ExprKind::Var { name, .. } => Some(name.clone()),
        ExprKind::QualifiedName { module, name, .. } => Some(format!("{}.{}", module, name)),
        ExprKind::App { func, .. } => extract_callee_name(func),
        ExprKind::With { expr, .. } => extract_callee_name(expr),
        _ => None,
    }
}

impl Checker {
    // --- Expression inference ---

    pub fn infer_expr(&mut self, expr: &Expr) -> Result<Type, Diagnostic> {
        let span = expr.span;
        let node_id = expr.id;
        match &expr.kind {
            ExprKind::Lit { value, .. } => Ok(match value {
                Lit::Int(_) => Type::int(),
                Lit::Float(_) => Type::float(),
                Lit::String(_) => Type::string(),
                Lit::Bool(_) => Type::bool(),
                Lit::Unit => Type::unit(),
            }),

            ExprKind::Var { name, .. } => {
                if let Some(scheme) = self.env.get(name) {
                    let scheme = scheme.clone();
                    // Propagate effect type params from callee's annotations.
                    // e.g. calling `counter` which has `needs {Actor CounterMsg}`
                    // populates the cache so lambdas can build typed EffArrows.
                    if let Some(constraints) = self.effect_state.fun_type_constraints.get(name).cloned() {
                        for (effect_name, concrete_types) in &constraints {
                            if let Some(info) = self.effects.get(effect_name).cloned() {
                                let mapping: std::collections::HashMap<u32, Type> = info
                                    .type_params
                                    .iter()
                                    .zip(concrete_types.iter())
                                    .map(|(&param_id, ty)| (param_id, ty.clone()))
                                    .collect();
                                self.effect_state.type_param_cache
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
                        self.effect_state.fun_type_constraints.get(name).cloned()
                        && let Type::Arrow(a, b) = ty
                    {
                        let eff_refs: Vec<(String, Vec<Type>)> =
                            eff_constraints.into_iter().collect();
                        ty = Type::EffArrow(a, b, eff_refs);
                    }
                    // Only propagate effects for zero-arity functions (where the
                    // Var reference itself is the full "call"). For functions that
                    // take args, effects are committed when the App chain saturates.
                    if !matches!(ty, Type::Arrow(_, _) | Type::EffArrow(_, _, _)) {
                        self.commit_callee_effects(name);
                    }
                    self.record_type(node_id, &ty);
                    // Record reference: this usage resolves to the definition
                    if let Some(def_id) = self.env.def_id(name) {
                        self.record_reference(node_id, span, def_id);
                    }
                    Ok(ty)
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
                    Ok(ty)
                } else {
                    Err(Diagnostic::error_at(
                        span,
                        format!("undefined constructor: {}", name),
                    ))
                }
            }

            ExprKind::App { func, arg, .. } => {
                let func_ty = self.infer_expr(func)?;
                let effects_before_arg = self.effect_state.current.clone();
                let arg_ty = self.infer_expr(arg)?;
                let ret_ty = self.fresh_var();
                if self
                    .unify_at(
                        &func_ty,
                        &Type::Arrow(Box::new(arg_ty), Box::new(ret_ty.clone())),
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
                // If the function declares its argument absorbs specific effects
                // (via EffArrow on the parameter type), subtract those from current_effects.
                // Only remove effects that the argument *introduced*, not effects the
                // caller already had. This prevents spawn! from absorbing the caller's
                // own Actor effect.
                let resolved_func = self.sub.apply(&func_ty);
                let param_ty = match &resolved_func {
                    Type::Arrow(p, _) | Type::EffArrow(p, _, _) => Some(self.sub.apply(p)),
                    _ => None,
                };
                if let Some(Type::EffArrow(_, _, needs)) = param_ty {
                    for (eff, _) in &needs {
                        if !effects_before_arg.contains(eff) {
                            self.effect_state.current.remove(eff);
                        }
                    }
                }
                // Fully saturated call: if the return type is no longer an Arrow,
                // walk the App chain to find the callee and commit its effects.
                let resolved_ret = self.sub.apply(&ret_ty);
                if !matches!(resolved_ret, Type::Arrow(_, _) | Type::EffArrow(_, _, _))
                    && let Some(callee) = extract_callee_name(expr)
                {
                    self.commit_callee_effects(&callee);
                }
                self.record_type(node_id, &ret_ty);
                Ok(ret_ty)
            }

            ExprKind::BinOp {
                op, left, right, ..
            } => {
                let left_ty = self.infer_expr(left)?;
                let right_ty = self.infer_expr(right)?;
                match op {
                    BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::FloatDiv | BinOp::IntDiv => {
                        self.unify_at(&left_ty, &right_ty, span)?;
                        self.trait_state.pending_constraints.push((
                            "Num".into(),
                            left_ty.clone(),
                            span,
                            node_id,
                        ));
                        Ok(left_ty)
                    }
                    BinOp::Mod => {
                        self.unify_at(&left_ty, &Type::int(), span)?;
                        self.unify_at(&right_ty, &Type::int(), span)?;
                        Ok(Type::int())
                    }
                    BinOp::Eq | BinOp::NotEq => {
                        self.unify_at(&left_ty, &right_ty, span)?;
                        self.trait_state.pending_constraints.push((
                            "Eq".into(),
                            left_ty.clone(),
                            span,
                            node_id,
                        ));
                        Ok(Type::bool())
                    }
                    BinOp::Lt | BinOp::Gt | BinOp::LtEq | BinOp::GtEq => {
                        self.unify_at(&left_ty, &right_ty, span)?;
                        self.trait_state.pending_constraints.push((
                            "Ord".into(),
                            left_ty.clone(),
                            span,
                            node_id,
                        ));
                        Ok(Type::bool())
                    }
                    BinOp::And | BinOp::Or => {
                        self.unify_at(&left_ty, &Type::bool(), span)?;
                        self.unify_at(&right_ty, &Type::bool(), span)?;
                        Ok(Type::bool())
                    }
                    BinOp::Concat => {
                        self.unify_at(&Type::string(), &left_ty, span)?;
                        self.unify_at(&Type::string(), &right_ty, span)?;
                        Ok(Type::string())
                    }
                }
            }

            ExprKind::UnaryMinus { expr: inner, .. } => {
                let ty = self.infer_expr(inner)?;
                self.trait_state.pending_constraints
                    .push(("Num".into(), ty.clone(), span, node_id));
                Ok(ty)
            }

            ExprKind::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => {
                let cond_ty = self.infer_expr(cond)?;
                self.unify_at(&cond_ty, &Type::bool(), cond.span)?;
                let then_ty = self.infer_expr(then_branch)?;
                let else_ty = self.infer_expr(else_branch)?;
                self.unify_at(&then_ty, &else_ty, span)?;
                Ok(then_ty)
            }

            ExprKind::Block { stmts, .. } => self.infer_block(stmts),

            ExprKind::Lambda { params, body, .. } => self.infer_lambda(params, body),

            ExprKind::Case {
                scrutinee, arms, ..
            } => {
                let scrut_ty = self.infer_expr(scrutinee)?;
                let result_ty = self.fresh_var();

                for arm in arms {
                    let saved_env = self.env.clone();

                    self.bind_pattern(&arm.pattern, &scrut_ty)?;

                    if let Some(guard) = &arm.guard {
                        self.check_guard(guard)?;
                    }

                    let body_ty = self.infer_expr(&arm.body)?;
                    self.unify_at(&result_ty, &body_ty, arm.body.span)?;

                    self.env = saved_env;
                }

                self.check_exhaustiveness(arms, &scrut_ty, span)?;

                Ok(result_ty)
            }

            ExprKind::RecordCreate { name, fields, .. } => {
                self.infer_record_create(name, fields, span)
            }

            ExprKind::AnonRecordCreate { fields, .. } => self.infer_anon_record_create(fields),

            ExprKind::FieldAccess {
                expr: inner, field, ..
            } => self.infer_field_access(inner, field, span),

            ExprKind::RecordUpdate { record, fields, .. } => {
                self.infer_record_update(record, fields, span)
            }

            ExprKind::EffectCall {
                name, qualifier, ..
            } => {
                let op_sig = self.lookup_effect_op(name, qualifier.as_deref(), span)?;

                // Track which effect this op belongs to
                if let Some(effect_name) = self.effect_for_op(name, qualifier.as_deref()) {
                    self.effect_state.current.insert(effect_name);
                }

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
                    ty = Type::Arrow(Box::new(Type::unit()), Box::new(ty));
                } else {
                    for (_, param_ty) in op_sig.params.iter().rev() {
                        ty = Type::Arrow(Box::new(param_ty.clone()), Box::new(ty));
                    }
                }
                Ok(ty)
            }

            ExprKind::With {
                expr: inner,
                handler,
                ..
            } => self.infer_with(inner, handler, span, node_id),

            ExprKind::Resume { value, .. } => {
                let val_ty = self.infer_expr(value)?;
                if let Some(expected) = &self.resume_type.clone() {
                    self.unify_at(&val_ty, expected, span)?;
                }
                // resume's return type is the answer type (what the with-expression produces)
                if let Some(ret_ty) = &self.resume_return_type.clone() {
                    Ok(ret_ty.clone())
                } else {
                    let ty = self.fresh_var();
                    Ok(ty)
                }
            }

            ExprKind::Tuple { elements, .. } => {
                let tys: Vec<Type> = elements
                    .iter()
                    .map(|e| self.infer_expr(e))
                    .collect::<Result<_, _>>()?;
                Ok(Type::Con("Tuple".into(), tys))
            }

            ExprKind::QualifiedName { module, name, .. } => {
                // Empty name means incomplete module access (e.g. `Math.`).
                // Return a fresh type var so inference can continue.
                if name.is_empty() {
                    return Ok(self.fresh_var());
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
                        Ok(ty)
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

                // Type-check each binding in sequence; env accumulates bound vars.
                // Also collect the inferred types for exhaustiveness checking later.
                let mut binding_types: Vec<Type> = Vec::new();
                for (pat, expr) in bindings {
                    let expr_ty = self.infer_expr(expr)?;
                    self.bind_pattern(pat, &expr_ty)?;
                    binding_types.push(expr_ty);
                }

                // Success expression runs in do-block scope; its type is the
                // success-path return type.
                let success_ty = self.infer_expr(success)?;
                self.unify_at(&result_ty, &success_ty, success.span)?;

                // Restore env so else arms only see the outer scope
                self.env = saved_env.clone();

                // Type-check else arms: each gets a fresh scrutinee type; body
                // types are unified with result_ty.
                for arm in else_arms {
                    let arm_saved = self.env.clone();
                    let scrutinee_ty = self.fresh_var();
                    self.bind_pattern(&arm.pattern, &scrutinee_ty)?;
                    let body_ty = self.infer_expr(&arm.body)?;
                    self.unify_at(&result_ty, &body_ty, arm.body.span)?;
                    self.env = arm_saved;
                }

                // Exhaustiveness: collect bail constructors from all bindings
                // and check that else arms cover them all.
                self.check_do_exhaustiveness(bindings, &binding_types, else_arms, span)?;

                // do-block bindings must not leak into the surrounding scope
                self.env = saved_env;
                Ok(result_ty)
            }

            ExprKind::Receive {
                arms, after_clause, ..
            } => self.infer_receive(
                arms,
                after_clause.as_ref().map(|(t, b)| (t.as_ref(), b.as_ref())),
                span,
            ),

            ExprKind::Ascription {
                expr: inner,
                type_expr,
                ..
            } => {
                let inferred = self.infer_expr(inner)?;
                let ann_ty = self.convert_type_expr(type_expr, &mut vec![]);
                self.unify_at(&inferred, &ann_ty, span)?;
                self.record_type(node_id, &ann_ty);
                Ok(ann_ty)
            }

            ExprKind::DictMethodAccess { .. }
            | ExprKind::DictRef { .. }
            | ExprKind::ForeignCall { .. } => {
                unreachable!("elaboration-only construct in typechecker")
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
        let guard_ty = self.infer_expr(guard)?;
        self.unify_at(&guard_ty, &Type::bool(), guard.span)
    }

    fn infer_lambda(&mut self, params: &[Pat], body: &Expr) -> Result<Type, Diagnostic> {
        let saved_env = self.env.clone();
        let scope = self.enter_effect_scope();
        // Lambda inherits the outer effect cache so effect ops (e.g. get!)
        // resolve type params from the enclosing function's annotations.
        self.effect_state.type_param_cache = scope.effect_cache.clone();

        let mut param_types = Vec::new();
        for pat in params {
            let ty = self.fresh_var();
            self.bind_pattern(pat, &ty)?;
            param_types.push(ty);
        }

        let body_ty = self.infer_expr(body)?;
        self.env = saved_env;

        // Build effect type args from the lambda's cache before exiting scope
        let lambda_effects: Vec<String> = self.effect_state.current.iter().cloned().collect();
        let eff_refs: Vec<(String, Vec<Type>)> = lambda_effects
            .iter()
            .map(|name| {
                let args = if let Some(cache) = self.effect_state.type_param_cache.get(name) {
                    if let Some(info) = self.effects.get(name) {
                        info.type_params
                            .iter()
                            .filter_map(|pid| cache.get(pid).cloned())
                            .collect()
                    } else {
                        vec![]
                    }
                } else {
                    vec![]
                };
                (name.clone(), args)
            })
            .collect();

        let result = self.exit_effect_scope(scope);
        // Lambda effects propagate to enclosing scope (the enclosing function
        // needs them for its `needs` declaration checking).
        self.effect_state.current.extend(result.effects);

        // Build curried arrow: a -> b -> c -> ret
        let mut ty = body_ty;
        for param_ty in param_types.into_iter().rev() {
            ty = Type::Arrow(Box::new(param_ty), Box::new(ty));
        }

        // If the lambda has effects, wrap the outermost arrow as EffArrow
        if !eff_refs.is_empty()
            && let Type::Arrow(a, b) = ty
        {
            ty = Type::EffArrow(a, b, eff_refs);
        }

        Ok(ty)
    }

    fn infer_receive(
        &mut self,
        arms: &[CaseArm],
        after_clause: Option<(&Expr, &Expr)>,
        span: Span,
    ) -> Result<Type, Diagnostic> {
        // Look up Actor effect's message type from the effect type param cache
        let msg_ty = match (
            self.effect_state.type_param_cache.get("Actor"),
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

            let body_ty = self.infer_expr(&arm.body)?;
            self.unify_at(&result_ty, &body_ty, arm.body.span)?;
            self.env = saved_env;
        }

        if let Some((timeout, body)) = after_clause {
            let timeout_ty = self.infer_expr(timeout)?;
            self.unify_at(&timeout_ty, &Type::int(), timeout.span)?;
            let body_ty = self.infer_expr(body)?;
            self.unify_at(&result_ty, &body_ty, body.span)?;
        }

        self.effect_state.current.insert("Actor".to_string());
        Ok(result_ty)
    }

    pub(crate) fn infer_block(&mut self, stmts: &[Stmt]) -> Result<Type, Diagnostic> {
        let mut last_ty = Type::unit();
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
                        Ok(ty) => {
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
                    // Partial application of effectful function: if the result type
                    // is still an Arrow, walk the RHS to find the callee and defer
                    // its effects to this binding.
                    let resolved_ty = self.sub.apply(&ty);
                    let mut deferred_effects = Vec::new();
                    if matches!(resolved_ty, Type::Arrow(_, _) | Type::EffArrow(_, _, _))
                        && let Some(callee) = extract_callee_name(value)
                    {
                        deferred_effects.extend(self.callee_effects(&callee));
                    }
                    if let Pat::Var {
                        id: pat_id,
                        name,
                        span: var_span,
                        ..
                    } = pattern
                    {
                        self.generalize_let_binding(
                            name, *pat_id, *var_span, &ty, deferred_effects,
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
                            let guard_ty = self.infer_expr(g)?;
                            self.unify_at(&guard_ty, &Type::bool(), g.span)?;
                        }
                        let body_ty = self.infer_expr(body)?;
                        // Build curried arrow type
                        let mut clause_ty = body_ty;
                        for param_ty in param_types.into_iter().rev() {
                            clause_ty = Type::Arrow(Box::new(param_ty), Box::new(clause_ty));
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
                        Ok(ty) => {
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
            Ok(last_ty)
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
        mut deferred_effects: Vec<String>,
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
            while let Type::Arrow(_, ret) | Type::EffArrow(_, ret, _) = t {
                arity += 1;
                t = ret;
            }
            self.let_dict_params
                .insert(name.to_string(), (dict_params, arity));
        }

        self.env
            .insert_with_def(name.to_string(), scheme, pat_id);
        deferred_effects.sort();
        self.effect_state.let_bindings
            .insert(name.to_string(), deferred_effects);
        self.lsp.node_spans.insert(pat_id, var_span);
        self.record_type_at_span(var_span, ty);
        self.lsp.definitions
            .push((pat_id, name.to_string(), var_span));
    }
}
