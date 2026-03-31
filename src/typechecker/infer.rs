use crate::ast::{Annotated, BinOp, CaseArm, Expr, ExprKind, Lit, NodeId, Pat, Stmt};

use super::{Checker, Diagnostic, EffectRow, Scheme, Type};
use crate::token::Span;

impl Checker {
    // --- Expression inference ---
    //
    // Effects accumulate on self.effect_row automatically. Isolation scopes
    // (handlers, lambdas, local funs) use save_effects/restore_effects.

    pub(crate) fn infer_expr(&mut self, expr: &Expr) -> Result<Type, Diagnostic> {
        let span = expr.span;
        let node_id = expr.id;
        match &expr.kind {
            ExprKind::Lit { value, .. } => Ok(match value {
                Lit::Int(..) => Type::int(),
                Lit::Float(..) => Type::float(),
                Lit::String(..) => Type::string(),
                Lit::Bool(_) => Type::bool(),
                Lit::Unit => Type::unit(),
            }),

            ExprKind::Var { name, .. } => {
                if let Some(scheme) = self.env.get(name) {
                    let scheme = scheme.clone();
                    // Propagate effect type params from callee's annotations.
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
                    for (trait_name, trait_ty, extra_types) in constraints {
                        self.trait_state.pending_constraints
                            .push((trait_name, extra_types, trait_ty, span, node_id));
                    }
                    if let Some(eff_constraints) =
                        self.effect_meta.fun_type_constraints.get(name).cloned()
                        && let Type::Fun(a, b, _) = ty
                    {
                        let eff_refs: Vec<(String, Vec<Type>)> =
                            eff_constraints.into_iter().collect();
                        ty = Type::Fun(a, b, super::EffectRow::closed(eff_refs));
                    }
                    self.record_type(node_id, &ty);
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
                let arg_ty = self.infer_expr(arg)?;
                let arg_ty_pre = arg_ty.clone();
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

                // Effect subtyping check
                {
                    let resolved_func = self.sub.apply(&func_ty);
                    if let Type::Fun(param, _, _) = &resolved_func {
                        self.check_callback_effect_subtype(&arg_ty_pre, param, arg.span)?;
                    }
                }

                let resolved_ret = self.sub.apply(&ret_ty);
                self.record_type(node_id, &ret_ty);

                // Absorption (call-site half): when passing a callback to a HOF,
                // the lambda's effects propagate immediately during lambda inference.
                // We subtract the HOF parameter's declared effects here because this
                // is the only point where we know "this callback was passed to a
                // function that handles these effects."
                //
                // There is a second absorption site in check_fun_clauses (boundary
                // half) that handles the inverse case: directly calling a callback
                // parameter like `f ()` inside `run_state`. Both are needed -- see
                // check_decl.rs for the rationale.
                let func_shallow = self.sub.resolve_var(&func_ty);
                if let Type::Fun(p, _, _) = func_shallow {
                    let param_shallow = self.sub.resolve_var(p);
                    if let Type::Fun(_, _, row) = param_shallow {
                        let absorbed: std::collections::HashSet<String> = row
                            .effects.iter().map(|(n, _)| n.clone()).collect();
                        self.effect_row = self.effect_row.subtract(&absorbed);
                    }
                }

                // Saturated call: emit the callee's effect row
                if !matches!(resolved_ret, Type::Fun(_, _, _)) {
                    let resolved_func = self.sub.apply(&func_ty);
                    if let Type::Fun(_, _, row) = &resolved_func {
                        let applied_row = self.sub.apply_effect_row(row);
                        self.emit_effects(&applied_row);
                    }
                }

                Ok(ret_ty)
            }

            ExprKind::BinOp {
                op, left, right, ..
            } => {
                let left_ty = self.infer_expr(left)?;
                let right_ty = self.infer_expr(right)?;
                match op {
                    BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::FloatDiv | BinOp::IntDiv | BinOp::Mod | BinOp::FloatMod => {
                        self.unify_at(&left_ty, &right_ty, span)?;
                        self.trait_state.pending_constraints.push((
                            "Num".into(),
                            vec![],
                            left_ty.clone(),
                            span,
                            node_id,
                        ));
                        Ok(left_ty)
                    }
                    BinOp::Eq | BinOp::NotEq => {
                        self.unify_at(&left_ty, &right_ty, span)?;
                        self.trait_state.pending_constraints.push((
                            "Eq".into(),
                            vec![],
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
                            vec![],
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
                        self.unify_at(&left_ty, &right_ty, span)?;
                        self.trait_state.pending_constraints.push((
                            "Semigroup".into(),
                            vec![],
                            left_ty.clone(),
                            span,
                            node_id,
                        ));
                        Ok(left_ty)
                    }
                }
            }

            ExprKind::UnaryMinus { expr: inner, .. } => {
                let ty = self.infer_expr(inner)?;
                self.trait_state.pending_constraints
                    .push(("Num".into(), vec![], ty.clone(), span, node_id));
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
                    let arm = &arm.node;
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

            ExprKind::AnonRecordCreate { fields, .. } => {
                self.infer_anon_record_create(fields)
            }

            ExprKind::FieldAccess {
                expr: inner, field, ..
            } => {
                self.infer_field_access(inner, field, span)
            }

            ExprKind::RecordUpdate { record, fields, .. } => {
                self.infer_record_update(record, fields, span)
            }

            ExprKind::EffectCall {
                name, qualifier, ..
            } => {
                let op_sig = self.lookup_effect_op(name, qualifier.as_deref(), span)?;

                // Record call site -> handler arm for LSP go-to-def
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

                // Build curried function type
                let mut ty = op_sig.return_type.clone();
                if op_sig.params.is_empty() {
                    ty = Type::arrow(Type::unit(), ty);
                } else {
                    for (_, param_ty) in op_sig.params.iter().rev() {
                        ty = Type::arrow(param_ty.clone(), ty);
                    }
                }
                // Emit the effect onto the accumulator
                if let Some(effect_name) = self.effect_for_op(name, qualifier.as_deref()) {
                    self.emit_effect(effect_name.clone(), vec![]);
                }
                Ok(ty)
            }

            ExprKind::With {
                expr: inner,
                handler,
                ..
            } => {
                self.infer_with(inner, handler, span, node_id)
            }

            ExprKind::Resume { value, .. } => {
                let val_ty = self.infer_expr(value)?;
                if let Some(expected) = &self.resume_type.clone() {
                    self.unify_at(&val_ty, expected, span)?;
                }
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
                    .collect::<Result<_, Diagnostic>>()?;
                Ok(Type::Con("Tuple".into(), tys))
            }

            ExprKind::QualifiedName { module, name, .. } => {
                if name.is_empty() {
                    return Ok(self.fresh_var());
                }
                let key = format!("{}.{}", module, name);
                // If not in env, try auto-importing the stdlib module on demand.
                // This allows Std.X.y to work without an explicit import.
                if self.env.get(&key).is_none() {
                    let parts: Vec<String> = module.split('.').map(String::from).collect();
                    if crate::typechecker::check_module::builtin_module_source(&parts).is_some()
                        && !self.modules.exports.contains_key(module.as_str())
                    {
                        // Alias = full module name so only Std.X.y is registered
                        if self.typecheck_import(&parts, Some(module), None, span).is_ok() {
                            // Register synthetic import so resolver/codegen can see it
                            self.prelude_imports.push(crate::ast::Decl::Import {
                                id: crate::ast::NodeId::fresh(),
                                module_path: parts,
                                alias: Some(module.clone()),
                                exposing: None,
                                span,
                            });
                        }
                    }
                }
                match self.env.get(&key).cloned() {
                    Some(scheme) => {
                        let (ty, constraints) = self.instantiate(&scheme);
                        for (trait_name, trait_ty, extra_types) in constraints {
                            self.trait_state.pending_constraints
                                .push((trait_name, extra_types, trait_ty, span, node_id));
                        }
                        self.record_type(node_id, &ty);
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

                let mut binding_types: Vec<Type> = Vec::new();
                for (pat, expr) in bindings {
                    let expr_ty = self.infer_expr(expr)?;
                    self.bind_pattern(pat, &expr_ty)?;
                    binding_types.push(expr_ty);
                }

                let success_ty = self.infer_expr(success)?;
                self.unify_at(&result_ty, &success_ty, success.span)?;

                self.env = saved_env.clone();

                for arm in else_arms {
                    let arm = &arm.node;
                    let arm_saved = self.env.clone();
                    let scrutinee_ty = self.fresh_var();
                    self.bind_pattern(&arm.pattern, &scrutinee_ty)?;
                    let body_ty = self.infer_expr(&arm.body)?;
                    self.unify_at(&result_ty, &body_ty, arm.body.span)?;
                    self.env = arm_saved;
                }

                self.check_do_exhaustiveness(bindings, &binding_types, else_arms, span)?;
                self.env = saved_env;
                Ok(result_ty)
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

            ExprKind::Pipe { .. }
            | ExprKind::BinOpChain { .. }
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
        // Guards must be pure: isolate effects so they don't leak
        let saved = self.save_effects();
        let guard_ty = self.infer_expr(guard)?;
        self.restore_effects(saved);
        self.unify_at(&guard_ty, &Type::bool(), guard.span)
    }

    fn infer_lambda(&mut self, params: &[Pat], body: &Expr) -> Result<Type, Diagnostic> {
        let saved_env = self.env.clone();
        let saved_cache = self.effect_meta.type_param_cache.clone();
        self.effect_meta.type_param_cache = saved_cache.clone();

        let mut param_types = Vec::new();
        for pat in params {
            let ty = self.fresh_var();
            self.bind_pattern(pat, &ty)?;
            param_types.push(ty);
        }

        // Isolate body effects
        let saved_effs = self.save_effects();
        let body_ty = self.infer_expr(body)?;
        let body_effs = self.restore_effects(saved_effs);
        self.env = saved_env;
        self.effect_meta.type_param_cache = saved_cache;

        // Build curried arrow
        let mut ty = body_ty;
        for param_ty in param_types.into_iter().rev() {
            ty = Type::arrow(param_ty, ty);
        }

        // Put effects on outermost arrow
        if !body_effs.effects.is_empty()
            && let Type::Fun(a, b, _) = ty
        {
            ty = Type::Fun(a, b, body_effs.clone());
        }

        // Lambda effects propagate to enclosing scope
        self.emit_effects(&body_effs);
        Ok(ty)
    }

    fn infer_receive(
        &mut self,
        arms: &[Annotated<CaseArm>],
        after_clause: Option<(&Expr, &Expr)>,
        span: Span,
    ) -> Result<Type, Diagnostic> {
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
            let arm = &arm.node;
            let saved_env = self.env.clone();

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

            // Arm body effects accumulate on self.effect_row automatically
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

        self.emit_effect("Actor".to_string(), vec![]);
        Ok(result_ty)
    }

    pub(crate) fn infer_block(&mut self, stmts: &[Annotated<Stmt>]) -> Result<Type, Diagnostic> {
        let mut last_ty = Type::unit();
        let mut errors: Vec<Diagnostic> = Vec::new();
        let mut i = 0;
        while i < stmts.len() {
            match &stmts[i].node {
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
                    span: fun_span,
                    ..
                } => {
                    // Group consecutive LetFun clauses with the same name
                    let fun_name = name.clone();
                    let fun_id = *id;
                    let fun_name_span = *name_span;
                    let fun_span = *fun_span;
                    type Clause<'a> = (&'a [Pat], &'a Option<Box<Expr>>, &'a Expr);
                    let mut clauses: Vec<Clause> = Vec::new();
                    while i < stmts.len() {
                        if let Stmt::LetFun {
                            name: n,
                            params,
                            guard,
                            body,
                            ..
                        } = &stmts[i].node
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
                    self.lsp.type_at_span.insert(fun_name_span, fun_ty.clone());
                    self.lsp
                        .definitions
                        .push((fun_id, fun_name.clone(), fun_name_span));
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
                            let saved = self.save_effects();
                            let guard_ty = self.infer_expr(g)?;
                            self.restore_effects(saved);
                            self.unify_at(&guard_ty, &Type::bool(), g.span)?;
                        }
                        // Isolate body effects for local fun
                        let saved_effs = self.save_effects();
                        let body_ty = self.infer_expr(body)?;
                        let body_effs = self.restore_effects(saved_effs);
                        // Build curried arrow with effects on innermost
                        let mut clause_ty = body_ty;
                        for (j, param_ty) in param_types.into_iter().rev().enumerate() {
                            if j == 0 && !body_effs.effects.is_empty() {
                                clause_ty = Type::Fun(Box::new(param_ty), Box::new(clause_ty), body_effs.clone());
                            } else {
                                clause_ty = Type::arrow(param_ty, clause_ty);
                            }
                        }
                        self.unify_at(&fun_ty, &clause_ty, fun_span)?;
                        self.env = saved_env;
                    }

                    let scheme = self.generalize(&fun_ty);
                    self.env.insert(fun_name, scheme);
                    last_ty = Type::unit();
                    // Don't increment i -- the while loop already advanced it
                    continue;
                }
                Stmt::Expr(expr) => {
                    match self.infer_expr(expr) {
                        Ok(ty) => {
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
            let first = errors.remove(0);
            self.collected_diagnostics.extend(errors);
            Err(first)
        } else {
            Ok(last_ty)
        }
    }

    fn generalize_let_binding(
        &mut self,
        name: &str,
        pat_id: NodeId,
        var_span: Span,
        ty: &Type,
        has_deferred_effects: bool,
    ) {
        let mut scheme = self.generalize(ty);

        self.trait_state.pending_constraints
            .retain(|(trait_name, _trait_type_args, cty, _span, node_id)| {
                let resolved = self.sub.apply(cty);
                if let Type::Var(id) = resolved
                    && scheme.forall.contains(&id)
                {
                    if !scheme
                        .constraints
                        .iter()
                        .any(|(t, v, _)| t == trait_name && *v == id)
                    {
                        // Resolve extra type arg var IDs through substitution
                        let extra_resolved: Vec<Type> = _trait_type_args
                            .iter()
                            .map(|t| self.sub.apply(t))
                            .collect();
                        scheme.constraints.push((trait_name.clone(), id, extra_resolved));
                    }
                    self.evidence.push(super::TraitEvidence {
                        node_id: *node_id,
                        trait_name: trait_name.clone(),
                        resolved_type: None,
                        type_var_name: None,
                        trait_type_args: _trait_type_args.clone(),
                    });
                    return false;
                }
                true
            });

        let operator_traits: std::collections::HashSet<&str> =
            ["Num", "Semigroup", "Eq"].into_iter().collect();
        let dict_params: Vec<(String, String)> = scheme
            .constraints
            .iter()
            .filter(|(t, _, _)| !operator_traits.contains(t.as_str()))
            .map(|(t, id, _)| (t.clone(), format!("v{}", id)))
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
    /// the expected parameter's effect row.
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
