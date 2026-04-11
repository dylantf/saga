use crate::ast::{Annotated, BinOp, CaseArm, Decl, Expr, ExprKind, Lit, NodeId, Pat, Stmt};

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
                let resolved_name = self
                    .scope_map
                    .resolve_value(name)
                    .map(|s| s.to_string())
                    .unwrap_or_else(|| name.clone());
                // Try bare name first (locals), then resolved name (imports)
                let env_lookup = self.env.get(name).or_else(|| self.env.get(&resolved_name));
                if let Some(scheme) = env_lookup {
                    let scheme = scheme.clone();
                    // Propagate effect type params from callee's annotations.
                    let effect_key = if self.effect_meta.fun_type_constraints.contains_key(name) {
                        name.clone()
                    } else {
                        resolved_name.clone()
                    };
                    if let Some(constraints) = self
                        .effect_meta
                        .fun_type_constraints
                        .get(&effect_key)
                        .cloned()
                    {
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
                    let (ty, constraints) = self.instantiate(&scheme);
                    for (trait_name, trait_ty, extra_types) in constraints {
                        self.trait_state.pending_constraints.push((
                            trait_name,
                            extra_types,
                            trait_ty,
                            span,
                            node_id,
                        ));
                    }
                    self.record_type(node_id, &ty);
                    let def_id = self
                        .env
                        .def_id(name)
                        .or_else(|| self.env.def_id(&resolved_name));
                    if let Some(def_id) = def_id {
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
                let resolved_ctor = self
                    .scope_map
                    .resolve_constructor(name)
                    .map(|s| s.to_string())
                    .unwrap_or_else(|| name.clone());
                let ctor_lookup = self
                    .constructors
                    .get(name)
                    .or_else(|| self.constructors.get(&resolved_ctor));
                if let Some(scheme) = ctor_lookup {
                    let scheme = scheme.clone();
                    let (ty, _) = self.instantiate(&scheme);
                    self.record_type(node_id, &ty);
                    let def_id = self
                        .lsp
                        .constructor_def_ids
                        .get(name)
                        .or_else(|| self.lsp.constructor_def_ids.get(&resolved_ctor))
                        .copied();
                    if let Some(def_id) = def_id {
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
                let arg_ty = match &arg.kind {
                    ExprKind::Lambda { params, body } => {
                        let resolved_func = self.sub.apply(&func_ty);
                        if let Type::Fun(expected_param, _, _) = &resolved_func {
                            match self.infer_lambda_against(params, body, expected_param)? {
                                Some(ty) => ty,
                                None => self.infer_expr(arg)?,
                            }
                        } else {
                            self.infer_expr(arg)?
                        }
                    }
                    _ => self.infer_expr(arg)?,
                };
                let arg_ty_pre = arg_ty.clone();
                let ret_ty = self.fresh_var();
                let eff_row_var = self.fresh_var();
                if self
                    .unify_at(
                        &func_ty,
                        &Type::Fun(
                            Box::new(arg_ty),
                            Box::new(ret_ty.clone()),
                            EffectRow {
                                effects: vec![],
                                tail: Some(Box::new(eff_row_var)),
                            },
                        ),
                        span,
                    )
                    .is_err()
                {
                    let resolved = self.sub.apply(&func_ty);
                    if let Type::Fun(param_ty, _, _) = &resolved {
                        let expected = self.prettify_type(param_ty);
                        let actual = self.prettify_type(&arg_ty_pre);
                        return Err(Diagnostic::error_at(
                            arg.span,
                            format!("type mismatch: expected {}, got {}", expected, actual),
                        ));
                    }

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

                let mut absorbed_entries = Vec::new();

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
                    if let Type::Fun(_, _, _) = param_shallow {
                        fn collect_declared_entries_applied(
                            checker: &Checker,
                            ty: &Type,
                            out: &mut Vec<super::EffectEntry>,
                        ) {
                            if let Type::Fun(_, ret, row) = ty {
                                for entry in &row.effects {
                                    let applied = super::EffectEntry {
                                        name: entry.name.clone(),
                                        args: entry
                                            .args
                                            .iter()
                                            .map(|arg| checker.sub.apply(arg))
                                            .collect(),
                                    };
                                    if !out.iter().any(|seen| seen.same_instantiation(&applied)) {
                                        out.push(applied);
                                    }
                                }
                                collect_declared_entries_applied(checker, ret, out);
                            }
                        }
                        collect_declared_entries_applied(
                            self,
                            param_shallow,
                            &mut absorbed_entries,
                        );
                        for entry in &absorbed_entries {
                            self.call_site_absorbed.insert(entry.name.clone());
                        }
                        let normalized_effect_row = self.sub.apply_effect_row(&self.effect_row);
                        self.effect_row = normalized_effect_row.subtract_entries(&absorbed_entries);
                    }
                }

                // Saturated call: emit the callee's effect row
                if !matches!(resolved_ret, Type::Fun(_, _, _)) {
                    let resolved_func = self.sub.apply(&func_ty);
                    if let Type::Fun(_, _, row) = &resolved_func {
                        let applied_row = self.sub.apply_effect_row(row);
                        let emitted_row = applied_row.subtract_entries(&absorbed_entries);
                        self.emit_effects(&emitted_row);
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
                    BinOp::Add
                    | BinOp::Sub
                    | BinOp::Mul
                    | BinOp::FloatDiv
                    | BinOp::IntDiv
                    | BinOp::Mod
                    | BinOp::FloatMod => {
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
                        let ord_name = self
                            .resolve_trait_name("Ord")
                            .unwrap_or_else(|| "Ord".into());
                        self.trait_state.pending_constraints.push((
                            ord_name,
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
                        let semigroup_name = self
                            .resolve_trait_name("Semigroup")
                            .unwrap_or_else(|| "Semigroup".into());
                        self.trait_state.pending_constraints.push((
                            semigroup_name,
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
                self.trait_state.pending_constraints.push((
                    "Num".into(),
                    vec![],
                    ty.clone(),
                    span,
                    node_id,
                ));
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

            ExprKind::AnonRecordCreate { fields, .. } => self.infer_anon_record_create(fields),

            ExprKind::FieldAccess {
                expr: inner, field, ..
            } => {
                let ty = self.infer_field_access(inner, field, span)?;
                self.record_type(node_id, &ty);
                Ok(ty)
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
                    self.lsp
                        .effect_call_targets
                        .insert(span, (*arm_span, arm_module.clone()));
                }

                // Build curried function type. If the op has its own `needs`,
                // place them on the outermost arrow so that App's saturated-call
                // emission will re-emit them after absorption.
                let mut ty = op_sig.return_type.clone();
                let needs_row = if op_sig.needs.is_empty() {
                    EffectRow::empty()
                } else {
                    op_sig.needs.clone()
                };
                if op_sig.params.is_empty() {
                    ty = Type::Fun(Box::new(Type::unit()), Box::new(ty), needs_row);
                } else {
                    for (i, (_, param_ty)) in op_sig.params.iter().rev().enumerate() {
                        let row = if i == op_sig.params.len() - 1 {
                            // Outermost arrow carries the needs
                            needs_row.clone()
                        } else {
                            EffectRow::empty()
                        };
                        ty = Type::Fun(Box::new(param_ty.clone()), Box::new(ty), row);
                    }
                }
                // Emit the effect onto the accumulator.
                if let Some(effect_name) = self.effect_for_op(name, qualifier.as_deref()) {
                    let effect_args = self.current_effect_args(&effect_name);
                    self.emit_effect(effect_name.clone(), effect_args);
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
                Ok(Type::Con(
                    super::canonicalize_type_name("Tuple").into(),
                    tys,
                ))
            }

            ExprKind::QualifiedName {
                module,
                name,
                canonical_module,
            } => {
                if name.is_empty() {
                    return Ok(self.fresh_var());
                }
                // Use canonical_module from resolve pass if available,
                // otherwise fall back to user-written module (for auto-imports)
                let effective_module = canonical_module.as_deref().unwrap_or(module);
                let key = format!("{}.{}", effective_module, name);
                // If not in env, try auto-importing the stdlib module on demand.
                // This allows Std.X.y to work without an explicit import.
                if self.env.get(&key).is_none() {
                    let parts: Vec<String> = module.split('.').map(String::from).collect();
                    if crate::typechecker::check_module::builtin_module_source(&parts).is_some()
                        && !self.modules.exports.contains_key(module.as_str())
                    {
                        // Alias = full module name so only Std.X.y is registered
                        if self
                            .typecheck_import(&parts, Some(module), None, span)
                            .is_ok()
                        {
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
                let resolved_key = self
                    .scope_map
                    .resolve_value(&key)
                    .map(|s| s.to_string())
                    .unwrap_or_else(|| key.clone());
                match self
                    .env
                    .get(&key)
                    .or_else(|| self.env.get(&resolved_key))
                    .cloned()
                {
                    Some(scheme) => {
                        let (ty, constraints) = self.instantiate(&scheme);
                        for (trait_name, trait_ty, extra_types) in constraints {
                            self.trait_state.pending_constraints.push((
                                trait_name,
                                extra_types,
                                trait_ty,
                                span,
                                node_id,
                            ));
                        }
                        self.record_type(node_id, &ty);
                        let def_id = self
                            .env
                            .def_id(&key)
                            .or_else(|| self.env.def_id(&resolved_key));
                        if let Some(def_id) = def_id {
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
                    // Constrain the scrutinee to one of the binding types so that
                    // payload type variables in the pattern (e.g. `e` in `Err(e)`)
                    // get pinned to the binding's actual error type. Try each
                    // binding type in order; the first that unifies wins. Mixed
                    // bail types are supported because each arm pattern usually
                    // matches exactly one binding's ADT.
                    for binding_ty in &binding_types {
                        let saved_sub = self.sub.clone();
                        if self.unify(&scrutinee_ty, binding_ty).is_ok() {
                            break;
                        }
                        self.sub = saved_sub;
                    }
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
                let ann_ty = self.convert_user_type_expr(type_expr, &mut vec![]);
                self.unify_at(&inferred, &ann_ty, span)?;
                self.record_type(node_id, &ann_ty);
                Ok(ann_ty)
            }

            ExprKind::HandlerExpr { body } => {
                // Create a synthetic HandlerDef and reuse register_handler
                let synthetic_name = format!("__handler_expr_{}", node_id.0);
                let synthetic_decl = Decl::HandlerDef {
                    id: node_id,
                    doc: vec![],
                    public: false,
                    name: synthetic_name.clone(),
                    name_span: span,
                    body: body.clone(),
                    recovered_arms: vec![],
                    dangling_trivia: vec![],
                    span,
                };
                self.register_handler(&synthetic_decl)?;
                // register_handler inserted the Handler type into self.env
                let scheme = self.env.get(&synthetic_name).unwrap();
                let ty = scheme.ty.clone();
                self.record_type(node_id, &ty);
                Ok(ty)
            }

            ExprKind::BitString { segments } => {
                for seg in segments {
                    let val_ty = self.infer_expr(&seg.value)?;
                    // Determine expected type based on specifiers
                    let has_spec = |s: &crate::ast::BitSegSpec| seg.specs.contains(s);
                    let expected = if has_spec(&crate::ast::BitSegSpec::Float) {
                        Type::float()
                    } else if has_spec(&crate::ast::BitSegSpec::Binary) {
                        Type::con("BitString")
                    } else if has_spec(&crate::ast::BitSegSpec::Utf8) {
                        Type::int()
                    } else {
                        // Default or explicit /integer: check for string literal sugar
                        match &seg.value.kind {
                            ExprKind::Lit {
                                value: Lit::String(..),
                                ..
                            } => Type::string(),
                            _ => Type::int(),
                        }
                    };
                    self.unify_at(&val_ty, &expected, seg.span)?;
                    if let Some(size) = &seg.size {
                        let size_ty = self.infer_expr(size)?;
                        self.unify_at(&size_ty, &Type::int(), size.span)?;
                    }
                }
                let ty = Type::con("BitString");
                self.record_type(node_id, &ty);
                Ok(ty)
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

    fn infer_lambda_against(
        &mut self,
        params: &[Pat],
        body: &Expr,
        expected_ty: &Type,
    ) -> Result<Option<Type>, Diagnostic> {
        let mut current = self.sub.apply(expected_ty);
        let mut param_types = Vec::with_capacity(params.len());

        for _ in params {
            match current {
                Type::Fun(param_ty, ret_ty, _) => {
                    param_types.push(*param_ty);
                    current = *ret_ty;
                }
                _ => return Ok(None),
            }
        }

        let expected_body_ty = current;
        let saved_env = self.env.clone();
        let saved_cache = self.effect_meta.type_param_cache.clone();
        self.effect_meta.type_param_cache = saved_cache.clone();

        for (pat, param_ty) in params.iter().zip(param_types.iter()) {
            self.bind_pattern(pat, param_ty)?;
        }

        let saved_effs = self.save_effects();
        let body_ty = self.infer_expr(body)?;
        let body_effs = self.restore_effects(saved_effs);
        self.unify_at(&body_ty, &expected_body_ty, body.span)?;
        self.env = saved_env;
        self.effect_meta.type_param_cache = saved_cache;

        let mut ty = body_ty;
        for param_ty in param_types.into_iter().rev() {
            ty = Type::arrow(param_ty, ty);
        }

        if !body_effs.effects.is_empty()
            && let Type::Fun(a, b, _) = ty
        {
            ty = Type::Fun(a, b, body_effs.clone());
        }

        self.emit_effects(&body_effs);
        Ok(Some(ty))
    }

    fn infer_receive(
        &mut self,
        arms: &[Annotated<CaseArm>],
        after_clause: Option<(&Expr, &Expr)>,
        span: Span,
    ) -> Result<Type, Diagnostic> {
        let msg_ty = match (
            self.effect_meta.type_param_cache.get("Std.Actor.Actor"),
            self.effects.get("Std.Actor.Actor"),
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
                let pid_ty = Type::Con(super::canonicalize_type_name("Pid").into(), vec![msg_var]);
                self.bind_pattern(&args[0], &pid_ty)?;
                self.bind_pattern(
                    &args[1],
                    &Type::Con(super::canonicalize_type_name("ExitReason").into(), vec![]),
                )?;
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

        self.emit_effect("Std.Actor.Actor".to_string(), vec![self.sub.apply(&msg_ty)]);
        Ok(result_ty)
    }

    /// Extract HandlerInfo from a handle binding's RHS expression.
    /// Handles direct variable references, if/else conditionals, and handler expressions.
    pub(crate) fn extract_handler_info(&self, expr: &Expr) -> Option<super::HandlerInfo> {
        fn applied_fun_name(expr: &Expr) -> Option<&str> {
            match &expr.kind {
                ExprKind::Var { name, .. } => Some(name.as_str()),
                ExprKind::App { func, .. } => applied_fun_name(func),
                _ => None,
            }
        }
        match &expr.kind {
            ExprKind::Var { name } => self.handlers.get(name).cloned(),
            ExprKind::App { .. } => {
                applied_fun_name(expr).and_then(|name| self.handler_funs.get(name).cloned())
            }
            ExprKind::If {
                then_branch,
                else_branch,
                ..
            } => {
                // For conditionals, try to extract from either branch
                // (both should handle the same effects, verified by type unification)
                self.extract_handler_info(then_branch)
                    .or_else(|| self.extract_handler_info(else_branch))
            }
            ExprKind::HandlerExpr { .. } => {
                // Handler expressions are registered under a synthetic name by infer_expr
                let synthetic = format!("__handler_expr_{}", expr.id.0);
                self.handlers.get(&synthetic).cloned()
            }
            _ => None,
        }
    }

    /// Build a minimal HandlerInfo from a Handler type.
    /// Used for dynamic handle bindings where the handler arms aren't statically known.
    fn handler_info_from_type(&mut self, ty: &Type) -> Option<super::HandlerInfo> {
        let resolved = self.sub.apply(ty);
        if let Type::Con(ref name, ref args) = resolved
            && name == super::canonicalize_type_name("Handler")
        {
            let effects: Vec<String> = args
                .iter()
                .filter_map(|arg| {
                    if let Type::Con(eff_name, _) = self.sub.apply(arg) {
                        Some(self.normalize_handler_effect_name(eff_name))
                    } else {
                        None
                    }
                })
                .collect();
            if effects.is_empty() {
                return None;
            }
            Some(super::HandlerInfo {
                effects,
                return_type: None,
                needs_effects: super::EffectRow {
                    effects: vec![],
                    tail: None,
                },
                forall: vec![],
                arm_spans: std::collections::HashMap::new(),
                where_constraints: std::collections::HashMap::new(),
                source_module: self.current_module.clone(),
            })
        } else {
            None
        }
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
                                let ann_ty = self.convert_user_type_expr(ann, &mut vec![]);
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
                            name,
                            *pat_id,
                            *var_span,
                            &ty,
                            has_deferred_effects,
                        );
                        // If the RHS is a handler, register it so `with name` works.
                        if let Some(info) = self.extract_handler_info(value) {
                            self.handlers.insert(name.clone(), info);
                        } else if let Some(info) = self.handler_info_from_type(&ty) {
                            self.handlers.insert(name.clone(), info);
                        }
                    } else {
                        if let Err(e) = self.bind_pattern(pattern, &ty) {
                            errors.push(e);
                        }
                        if let Err(e) = self.check_let_pattern_irrefutable(pattern, &ty) {
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
                                clause_ty = Type::Fun(
                                    Box::new(param_ty),
                                    Box::new(clause_ty),
                                    body_effs.clone(),
                                );
                            } else {
                                clause_ty = Type::arrow(param_ty, clause_ty);
                            }
                        }
                        self.unify_at(&fun_ty, &clause_ty, fun_span)?;
                        self.env = saved_env;
                    }

                    let scheme = self.generalize(&fun_ty);
                    self.record_type(fun_id, &fun_ty);
                    self.env.insert(fun_name, scheme);
                    last_ty = Type::unit();
                    // Don't increment i -- the while loop already advanced it
                    continue;
                }

                Stmt::Expr(expr) => {
                    match self.infer_expr(expr) {
                        Ok(ty) => {
                            if i + 1 < stmts.len() {
                                self.pending_warnings
                                    .push(super::PendingWarning::DiscardedValue {
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

        self.trait_state.pending_constraints.retain(
            |(trait_name, _trait_type_args, cty, _span, node_id)| {
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
                        let extra_resolved: Vec<Type> =
                            _trait_type_args.iter().map(|t| self.sub.apply(t)).collect();
                        scheme
                            .constraints
                            .push((trait_name.clone(), id, extra_resolved));
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
            },
        );

        let operator_traits: std::collections::HashSet<&str> = ["Num", "Eq"].into_iter().collect();
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
            self.let_dict_params.insert(
                (name.to_string(), pat_id),
                crate::typechecker::result::LetDictInfo {
                    params: dict_params,
                    value_arity: arity,
                },
            );
        }

        self.env.insert_with_def(name.to_string(), scheme, pat_id);
        if has_deferred_effects {
            self.effect_meta.known_let_bindings.insert(name.to_string());
        }
        self.lsp.node_spans.insert(pat_id, var_span);
        self.record_type_at_span(var_span, ty);
        self.lsp
            .definitions
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
                    .filter(|e| !expected_row.effects.iter().any(|en| en.name == e.name))
                    .map(|e| e.name.as_str())
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
                            .map(|e| e.name.as_str())
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
