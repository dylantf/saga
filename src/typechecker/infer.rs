use std::collections::HashSet;

use crate::ast::{self, BinOp, CaseArm, Expr, ExprKind, Lit, Pat, Stmt};

use super::{Checker, Diagnostic, EffectOpSig, Scheme, Type};
use crate::token::Span;

/// Walk an App chain to find the callee name at the root.
/// e.g. `App(App(Var("f"), a), b)` -> Some("f")
///       `App(QualifiedName("M", "f"), a)` -> Some("M.f")
/// Returns None if the callee isn't a Var or QualifiedName.
fn extract_callee_name(expr: &Expr) -> Option<String> {
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

    /// Collect effects for a callee from fun_effects and let_effect_bindings.
    fn callee_effects(&self, name: &str) -> Vec<String> {
        let mut effects = Vec::new();
        if let Some(effs) = self.fun_effects.get(name) {
            effects.extend(effs.iter().cloned());
        }
        if let Some(effs) = self.let_effect_bindings.get(name) {
            effects.extend(effs.iter().cloned());
        }
        effects
    }

    /// Commit a callee's effects to current_effects.
    fn commit_callee_effects(&mut self, name: &str) {
        if let Some(effects) = self.fun_effects.get(name).cloned() {
            self.current_effects.extend(effects);
        }
        if let Some(effects) = self.let_effect_bindings.get(name).cloned() {
            self.current_effects.extend(effects);
        }
    }

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
                    let (mut ty, constraints) = self.instantiate(&scheme);
                    for (trait_name, trait_ty) in constraints {
                        self.pending_constraints
                            .push((trait_name, trait_ty, span, node_id));
                    }
                    // If this function has effect type constraints, convert the
                    // outermost Arrow to EffArrow so spawn! can link type args.
                    if let Some(eff_constraints) =
                        self.fun_effect_type_constraints.get(name).cloned()
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
                    if let Some(def_id) = self.constructor_def_ids.get(name).copied() {
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
                let effects_before_arg = self.current_effects.clone();
                let arg_ty = self.infer_expr(arg)?;
                let ret_ty = self.fresh_var();
                self.unify_at(
                    &func_ty,
                    &Type::Arrow(Box::new(arg_ty), Box::new(ret_ty.clone())),
                    span,
                )?;
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
                            self.current_effects.remove(eff);
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
                        self.pending_constraints.push((
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
                        self.pending_constraints.push((
                            "Eq".into(),
                            left_ty.clone(),
                            span,
                            node_id,
                        ));
                        Ok(Type::bool())
                    }
                    BinOp::Lt | BinOp::Gt | BinOp::LtEq | BinOp::GtEq => {
                        self.unify_at(&left_ty, &right_ty, span)?;
                        self.pending_constraints.push((
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
                        self.unify_at(&left_ty, &Type::string(), span)?;
                        self.unify_at(&right_ty, &Type::string(), span)?;
                        Ok(Type::string())
                    }
                }
            }

            ExprKind::UnaryMinus { expr: inner, .. } => {
                let ty = self.infer_expr(inner)?;
                self.pending_constraints
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
                let info = self.records.get(name).cloned().ok_or_else(|| {
                    Diagnostic::error_at(span, format!("undefined record type: {}", name))
                })?;
                let (inst_fields, result_ty) = self.instantiate_record(name, &info);

                for (fname, fspan, fexpr) in fields {
                    let expected =
                        inst_fields
                            .iter()
                            .find(|(n, _)| n == fname);
                    match expected {
                        None => {
                            self.collected_diagnostics.push(Diagnostic::error_at(
                                *fspan,
                                format!("unknown field '{}' on record {}", fname, name),
                            ));
                            // Still infer the expression to check for errors within it
                            let _ = self.infer_expr(fexpr);
                        }
                        Some((_, expected_ty)) => {
                            if let Ok(actual) = self.infer_expr(fexpr) {
                                if let Err(e) = self.unify_at(expected_ty, &actual, fexpr.span) {
                                    self.collected_diagnostics.push(e);
                                }
                            }
                        }
                    }
                }

                // Check for missing fields
                let provided: Vec<&str> = fields.iter().map(|(n, _, _)| n.as_str()).collect();
                let missing: Vec<&str> = inst_fields
                    .iter()
                    .filter(|(n, _)| !provided.contains(&n.as_str()))
                    .map(|(n, _)| n.as_str())
                    .collect();
                if !missing.is_empty() {
                    self.collected_diagnostics.push(Diagnostic::error_at(
                        span,
                        format!(
                            "missing field{} on record {}: {}",
                            if missing.len() > 1 { "s" } else { "" },
                            name,
                            missing.join(", "),
                        ),
                    ));
                }

                Ok(result_ty)
            }

            ExprKind::AnonRecordCreate { fields, .. } => {
                let mut typed_fields: Vec<(String, Type)> = Vec::new();
                for (fname, _fspan, fexpr) in fields {
                    let ty = self.infer_expr(fexpr)?;
                    typed_fields.push((fname.clone(), ty));
                }
                typed_fields.sort_by(|(a, _), (b, _)| a.cmp(b));
                Ok(Type::Record(typed_fields))
            }

            ExprKind::FieldAccess {
                expr: inner, field, ..
            } => self.infer_field_access(inner, field, span),

            ExprKind::RecordUpdate { record, fields, .. } => {
                let rec_ty = self.infer_expr(record)?;
                let mut resolved = self.sub.apply(&rec_ty);

                if matches!(&resolved, Type::Var(_))
                    && let Some((fname, _, _)) = fields.first()
                {
                    let candidates: Vec<_> = self
                        .records
                        .iter()
                        .filter(|(_, info)| info.fields.iter().any(|(n, _)| n == fname))
                        .map(|(rname, _)| rname.clone())
                        .collect();
                    if candidates.len() == 1 {
                        self.unify(&resolved, &Type::Con(candidates[0].clone(), vec![]))?;
                        resolved = self.sub.apply(&rec_ty);
                    }
                }

                match &resolved {
                    Type::Con(name, _) => {
                        let info = self.records.get(name).cloned().ok_or_else(|| {
                            Diagnostic::error_at(span, format!("type {} is not a record", name))
                        })?;
                        let (inst_fields, result_ty) = self.instantiate_record(name, &info);
                        // Unify the record expression type with the instantiated result type
                        // so that type params flow from the input record to the field types.
                        self.unify_at(&resolved, &result_ty, span)?;
                        for (fname, fspan, fexpr) in fields {
                            let expected = inst_fields
                                .iter()
                                .find(|(n, _)| n == fname)
                                .ok_or_else(|| {
                                    Diagnostic::error_at(
                                        *fspan,
                                        format!("unknown field '{}' on record {}", fname, name),
                                    )
                                })?;
                            let actual = self.infer_expr(fexpr)?;
                            self.unify_at(&expected.1, &actual, fexpr.span)?;
                        }
                        Ok(self.sub.apply(&result_ty))
                    }
                    Type::Record(rec_fields) => {
                        for (fname, fspan, fexpr) in fields {
                            let (_, expected_ty) = rec_fields
                                .iter()
                                .find(|(n, _)| n == fname)
                                .ok_or_else(|| {
                                    Diagnostic::error_at(
                                        *fspan,
                                        format!("unknown field '{}' on anonymous record", fname),
                                    )
                                })?;
                            let actual = self.infer_expr(fexpr)?;
                            self.unify_at(expected_ty, &actual, fexpr.span)?;
                        }
                        Ok(self.sub.apply(&resolved))
                    }
                    _ => Err(Diagnostic::error_at(
                        span,
                        format!("cannot update non-record type {}", resolved),
                    )),
                }
            }

            ExprKind::EffectCall {
                name, qualifier, ..
            } => {
                let op_sig = self.lookup_effect_op(name, qualifier.as_deref(), span)?;

                // Track which effect this op belongs to
                if let Some(effect_name) = self.effect_for_op(name, qualifier.as_deref()) {
                    self.current_effects.insert(effect_name);
                }

                // Record call site -> handler arm for LSP go-to-def (level 1).
                // Scan the with-stack innermost-first; first match wins (innermost shadows outer).
                if let Some((arm_span, arm_module)) = self
                    .with_arm_stacks
                    .iter()
                    .rev()
                    .find_map(|map| map.get(name.as_str()))
                {
                    self.effect_call_targets
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
            } => self.infer_with(inner, handler, span),

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
                let key = format!("{}.{}", module, name);
                match self.env.get(&key).cloned() {
                    Some(scheme) => {
                        let (ty, constraints) = self.instantiate(&scheme);
                        for (trait_name, trait_ty) in constraints {
                            self.pending_constraints
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
        let saved_effect_cache = self.effect_type_param_cache.clone();
        let saved_effects = self.current_effects.clone();

        let mut param_types = Vec::new();
        for pat in params {
            let ty = self.fresh_var();
            self.bind_pattern(pat, &ty)?;
            param_types.push(ty);
        }

        let body_ty = self.infer_expr(body)?;
        self.env = saved_env;

        // Collect effects the lambda body introduced
        let lambda_effects: Vec<String> = self
            .current_effects
            .difference(&saved_effects)
            .cloned()
            .collect();

        // Build effect type args from the lambda's own cache
        let eff_refs: Vec<(String, Vec<Type>)> = lambda_effects
            .iter()
            .map(|name| {
                let args = if let Some(cache) = self.effect_type_param_cache.get(name) {
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

        self.effect_type_param_cache = saved_effect_cache;

        // Build curried arrow: a -> b -> c -> ret
        let mut result = body_ty;
        for param_ty in param_types.into_iter().rev() {
            result = Type::Arrow(Box::new(param_ty), Box::new(result));
        }

        // If the lambda has effects, wrap the outermost arrow as EffArrow
        if !eff_refs.is_empty()
            && let Type::Arrow(a, b) = result
        {
            result = Type::EffArrow(a, b, eff_refs);
        }

        Ok(result)
    }

    fn infer_field_access(
        &mut self,
        record_expr: &Expr,
        field: &str,
        span: Span,
    ) -> Result<Type, Diagnostic> {
        let expr_ty = self.infer_expr(record_expr)?;
        let resolved = self.sub.apply(&expr_ty);

        match &resolved {
            Type::Con(name, _) => {
                let info = self.records.get(name).cloned().ok_or_else(|| {
                    Diagnostic::error_at(span, format!("type {} is not a record", name))
                })?;
                let (inst_fields, result_ty) = self.instantiate_record(name, &info);
                // Unify so that the record's concrete type args flow into field types
                self.unify_at(&resolved, &result_ty, span)?;
                let (_, field_ty) =
                    inst_fields
                        .iter()
                        .find(|(n, _)| n == field)
                        .ok_or_else(|| {
                            Diagnostic::error_at(
                                span,
                                format!("no field '{}' on record {}", field, name),
                            )
                        })?;
                Ok(self.sub.apply(field_ty))
            }
            Type::Var(id) => {
                let id = *id;
                // Collect candidates: for each record that has this field,
                // instantiate its type params to fresh vars and return both the
                // record result type and the field type.
                let candidates: Vec<_> = self
                    .records
                    .iter()
                    .filter(|(_, info)| info.fields.iter().any(|(n, _)| n == field))
                    .map(|(rname, _)| rname.clone())
                    .collect();
                match candidates.len() {
                    0 => Err(Diagnostic::error_at(
                        span,
                        format!("no record has field '{}'", field),
                    )),
                    1 => {
                        let rname = &candidates[0];
                        let info = self.records.get(rname).cloned().unwrap();
                        let (inst_fields, result_ty) = self.instantiate_record(rname, &info);
                        self.unify(&resolved, &result_ty)?;
                        let (_, field_ty) = inst_fields.iter().find(|(n, _)| n == field).unwrap();
                        Ok(self.sub.apply(field_ty))
                    }
                    _ => {
                        // Multiple records have this field. Narrow by intersecting
                        // with candidates already observed for this variable.
                        let narrowed: Vec<String> = match self.field_candidates.get(&id) {
                            Some((existing, _)) => candidates
                                .into_iter()
                                .filter(|n| existing.contains(n))
                                .collect(),
                            None => candidates,
                        };
                        match narrowed.len() {
                            0 => Err(Diagnostic::error_at(
                                span,
                                format!(
                                    "no single record type has all accessed fields (including '{}')",
                                    field
                                ),
                            )),
                            1 => {
                                let rname = &narrowed[0];
                                let info = self.records.get(rname).cloned().unwrap();
                                let (inst_fields, result_ty) =
                                    self.instantiate_record(rname, &info);
                                self.unify(&resolved, &result_ty)?;
                                self.field_candidates.remove(&id);
                                let (_, field_ty) =
                                    inst_fields.iter().find(|(n, _)| n == field).unwrap();
                                Ok(self.sub.apply(field_ty))
                            }
                            _ => {
                                // For ambiguity checking, instantiate each candidate
                                // and compare the resolved field types structurally.
                                let mut inst_results: Vec<(String, Type)> = Vec::new();
                                for rname in &narrowed {
                                    let info = self.records.get(rname).cloned().unwrap();
                                    let (inst_fields, _) = self.instantiate_record(rname, &info);
                                    let (_, field_ty) =
                                        inst_fields.iter().find(|(n, _)| n == field).unwrap();
                                    inst_results.push((rname.clone(), self.sub.apply(field_ty)));
                                }
                                let first_ty = &inst_results[0].1;
                                let all_agree = inst_results.iter().all(|(_, ty)| ty == first_ty);
                                if all_agree {
                                    self.field_candidates.insert(id, (narrowed, span));
                                    Ok(first_ty.clone())
                                } else {
                                    Err(Diagnostic::error_at(
                                        span,
                                        format!(
                                            "ambiguous field '{}': found in [{}] with different types; add a type annotation",
                                            field,
                                            narrowed.join(", ")
                                        ),
                                    ))
                                }
                            }
                        }
                    }
                }
            }
            Type::Record(fields) => {
                let (_, field_ty) = fields
                    .iter()
                    .find(|(n, _)| n == field)
                    .ok_or_else(|| {
                        Diagnostic::error_at(
                            span,
                            format!("no field '{}' on anonymous record", field),
                        )
                    })?;
                Ok(self.sub.apply(field_ty))
            }
            _ => Err(Diagnostic::error_at(
                span,
                format!("cannot access field '{}' on type {}", field, resolved),
            )),
        }
    }

    fn infer_receive(
        &mut self,
        arms: &[CaseArm],
        after_clause: Option<(&Expr, &Expr)>,
        span: Span,
    ) -> Result<Type, Diagnostic> {
        // Look up Actor effect's message type from the effect type param cache
        let msg_ty = match (
            self.effect_type_param_cache.get("Actor"),
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

        self.current_effects.insert("Actor".to_string());
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
                        let mut scheme = self.generalize(&ty);
                        // Absorb pending trait constraints for generalized vars
                        // so let-bound values can be polymorphic over traits.
                        // e.g. `let f = debug >> println` gets scheme
                        // `forall a. a -> Unit where {a: Debug}`
                        self.pending_constraints
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
                            // Count arrow arity of the resolved type
                            let resolved_ty = self.sub.apply(&ty);
                            let mut arity = 0usize;
                            let mut t = &resolved_ty;
                            while let super::Type::Arrow(_, ret)
                            | super::Type::EffArrow(_, ret, _) = t
                            {
                                arity += 1;
                                t = ret;
                            }
                            self.let_dict_params
                                .insert(name.clone(), (dict_params, arity));
                        }
                        self.env.insert_with_def(name.clone(), scheme, *pat_id);
                        deferred_effects.sort();
                        self.let_effect_bindings
                            .insert(name.clone(), deferred_effects);
                        self.node_spans.insert(*pat_id, *var_span);
                        self.record_type_at_span(*var_span, &ty);
                        self.definitions.push((*pat_id, name.clone(), *var_span));
                    } else if let Err(e) = self.bind_pattern(pattern, &ty) {
                        errors.push(e);
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
                    self.node_spans.insert(fun_id, fun_name_span);

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
                            // Warn if a non-unit value is discarded (not last statement)
                            if i + 1 < stmts.len() {
                                let resolved = self.sub.apply(&ty);
                                let is_unit = matches!(&resolved, Type::Con(n, args) if n == "Unit" && args.is_empty());
                                if !is_unit && !matches!(resolved, Type::Error | Type::Never) {
                                    let display_ty = self.prettify_type(&ty);
                                    self.collected_diagnostics.push(Diagnostic::warning_at(
                                        expr.span,
                                        format!(
                                            "value of type `{}` is discarded; use `let _ = ...` to suppress",
                                            display_ty,
                                        ),
                                    ));
                                }
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

    // --- Pattern binding ---

    /// Bind a pattern to a type, adding variables to the environment.
    pub(crate) fn bind_pattern(&mut self, pat: &Pat, ty: &Type) -> Result<(), Diagnostic> {
        match pat {
            Pat::Wildcard { .. } => Ok(()),
            Pat::Var { id, name, span, .. } => {
                self.env.insert_with_def(
                    name.clone(),
                    Scheme {
                        forall: vec![],
                        constraints: vec![],
                        ty: ty.clone(),
                    },
                    *id,
                );
                self.record_type_at_span(*span, ty);
                self.node_spans.insert(*id, *span);
                self.definitions.push((*id, name.clone(), *span));
                Ok(())
            }
            Pat::Lit { value, span, .. } => {
                let lit_ty = match value {
                    Lit::Int(_) => Type::int(),
                    Lit::Float(_) => Type::float(),
                    Lit::String(_) => Type::string(),
                    Lit::Bool(_) => Type::bool(),
                    Lit::Unit => Type::unit(),
                };
                self.unify_at(ty, &lit_ty, *span)
            }
            Pat::Constructor {
                name, args, span, ..
            } => {
                let ctor_scheme = self.constructors.get(name).cloned().ok_or_else(|| {
                    Diagnostic::error_at(
                        *span,
                        format!("undefined constructor in pattern: {}", name),
                    )
                })?;
                let (ctor_ty, _) = self.instantiate(&ctor_scheme);
                let mut current = ctor_ty;
                for arg_pat in args {
                    match current {
                        Type::Arrow(param_ty, ret_ty) => {
                            self.bind_pattern(arg_pat, &param_ty)?;
                            current = *ret_ty;
                        }
                        _ => {
                            return Err(Diagnostic::error_at(
                                *span,
                                format!("constructor {} applied to too many arguments", name),
                            ));
                        }
                    }
                }
                self.unify_at(ty, &current, *span)
            }
            Pat::Record {
                name, fields, as_name, span, ..
            } => {
                let info = self.records.get(name).cloned().ok_or_else(|| {
                    Diagnostic::error_at(
                        *span,
                        format!("undefined record type in pattern: {}", name),
                    )
                })?;
                let (inst_fields, result_ty) = self.instantiate_record(name, &info);
                self.unify_at(ty, &result_ty, *span)?;

                for (fname, alias_pat) in fields {
                    let (_, field_ty) =
                        inst_fields
                            .iter()
                            .find(|(n, _)| n == fname)
                            .ok_or_else(|| {
                                Diagnostic::error_at(
                                    *span,
                                    format!("unknown field '{}' on record {}", fname, name),
                                )
                            })?;
                    let resolved_field_ty = self.sub.apply(field_ty);
                    match alias_pat {
                        Some(pat) => self.bind_pattern(pat, &resolved_field_ty)?,
                        None => {
                            self.env.insert(
                                fname.clone(),
                                Scheme {
                                    forall: vec![],
                                    constraints: vec![],
                                    ty: resolved_field_ty.clone(),
                                },
                            );
                            self.record_type_at_span(*span, &resolved_field_ty);
                        }
                    }
                }
                if let Some(as_var) = as_name {
                    let resolved = self.sub.apply(&result_ty);
                    self.env.insert(
                        as_var.clone(),
                        Scheme {
                            forall: vec![],
                            constraints: vec![],
                            ty: resolved.clone(),
                        },
                    );
                    self.record_type_at_span(*span, &resolved);
                }
                Ok(())
            }

            Pat::Tuple { elements, span, .. } => {
                let elem_tys: Vec<Type> = elements.iter().map(|_| self.fresh_var()).collect();
                let tuple_ty = Type::Con("Tuple".into(), elem_tys.clone());
                self.unify_at(ty, &tuple_ty, *span)?;
                for (pat, elem_ty) in elements.iter().zip(elem_tys.iter()) {
                    self.bind_pattern(pat, elem_ty)?;
                }
                Ok(())
            }

            Pat::StringPrefix { rest, span, .. } => {
                self.unify_at(ty, &Type::string(), *span)?;
                self.bind_pattern(rest, &Type::string())
            }

            Pat::AnonRecord { fields, span, .. } => {
                let mut field_tys: Vec<(String, Type)> = fields
                    .iter()
                    .map(|(fname, _)| (fname.clone(), self.fresh_var()))
                    .collect();
                field_tys.sort_by(|(a, _), (b, _)| a.cmp(b));
                let record_ty = Type::Record(field_tys.clone());
                self.unify_at(ty, &record_ty, *span)?;

                for (fname, alias_pat) in fields {
                    let (_, field_ty) = field_tys
                        .iter()
                        .find(|(n, _)| n == fname)
                        .unwrap();
                    let resolved_field_ty = self.sub.apply(field_ty);
                    match alias_pat {
                        Some(pat) => self.bind_pattern(pat, &resolved_field_ty)?,
                        None => {
                            self.env.insert(
                                fname.clone(),
                                Scheme {
                                    forall: vec![],
                                    constraints: vec![],
                                    ty: resolved_field_ty.clone(),
                                },
                            );
                            self.record_type_at_span(*span, &resolved_field_ty);
                        }
                    }
                }
                Ok(())
            }
        }
    }

    // --- Exhaustiveness checking ---

    /// Check whether case arms exhaustively cover a type using Maranget's
    /// usefulness algorithm. Also detects unreachable/redundant arms.
    pub(crate) fn check_exhaustiveness(
        &self,
        arms: &[ast::CaseArm],
        scrutinee_ty: &Type,
        span: Span,
    ) -> Result<(), Diagnostic> {
        use super::exhaustiveness::{self as exh, ExhaustivenessCtx, SPat};

        let resolved = self.sub.apply(scrutinee_ty);

        // Skip exhaustiveness for unresolved type variables and arrow types
        match &resolved {
            Type::Con(_, _) => {}
            _ => return Ok(()),
        };

        let type_name = match &resolved {
            Type::Con(name, _) => name.clone(),
            _ => unreachable!(),
        };

        // For primitive types with infinite value sets, keep the simple check:
        // require a wildcard/variable fallback if any literal patterns are used.
        if !self.adt_variants.contains_key(&type_name)
            && matches!(type_name.as_str(), "Int" | "Float" | "String")
        {
            let has_lit = arms
                .iter()
                .any(|arm| matches!(&arm.pattern, Pat::Lit { .. }));
            if has_lit {
                let has_catchall = arms.iter().any(|arm| {
                    arm.guard.is_none()
                        && matches!(&arm.pattern, Pat::Wildcard { .. } | Pat::Var { .. })
                });
                if !has_catchall {
                    return Err(Diagnostic::error_at(
                        span,
                        format!(
                            "non-exhaustive pattern match on {}: add a wildcard `_` or variable pattern",
                            type_name
                        ),
                    ));
                }
            }
            return Ok(());
        }

        // For non-ADT, non-primitive types (e.g. Unit, records), skip.
        // Tuples are allowed through -- they're single-constructor types
        // handled natively by the Maranget algorithm.
        if !self.adt_variants.contains_key(&type_name) && type_name != "Tuple" {
            return Ok(());
        }

        let ctx = ExhaustivenessCtx {
            adt_variants: &self.adt_variants,
        };

        // Build pattern matrix from arms (skip guarded arms for coverage,
        // but include them for redundancy checking)
        let mut matrix: Vec<Vec<SPat>> = Vec::new();

        for arm in arms {
            let spat = exh::simplify_pat(&arm.pattern);
            let row = vec![spat.clone()];

            // Redundancy check: is this arm useful w.r.t. prior unguarded arms?
            if arm.guard.is_none() && !exh::useful(&ctx, &matrix, &row) {
                let pat_str = exh::format_witness(&[spat]);
                return Err(Diagnostic::error_at(
                    arm.pattern.span(),
                    format!("unreachable pattern: {} already covered", pat_str),
                ));
            }

            // Only unguarded arms contribute to coverage
            if arm.guard.is_none() {
                matrix.push(row);
            }
        }

        // Exhaustiveness check: is a wildcard useful against the full matrix?
        let wildcard_row = vec![SPat::Wildcard];
        if exh::useful(&ctx, &matrix, &wildcard_row) {
            // Collect all uncovered witnesses for a complete error message
            let witnesses = exh::find_all_witnesses(&ctx, &matrix, 1);
            if !witnesses.is_empty() {
                let formatted: Vec<String> =
                    witnesses.iter().map(|w| exh::format_witness(w)).collect();
                return Err(Diagnostic::error_at(
                    span,
                    format!(
                        "non-exhaustive pattern match: missing {}",
                        formatted.join(", ")
                    ),
                ));
            }
            return Err(Diagnostic::error_at(span, "non-exhaustive pattern match"));
        }

        Ok(())
    }

    /// Check do...else exhaustiveness: for each binding `pat <- expr`, find the
    /// constructors of the expr type NOT matched by `pat` (the "bail" constructors),
    /// and verify the else arms cover them all.
    fn check_do_exhaustiveness(
        &self,
        bindings: &[(Pat, Expr)],
        binding_types: &[Type],
        else_arms: &[ast::CaseArm],
        span: Span,
    ) -> Result<(), Diagnostic> {
        use super::exhaustiveness::{self as exh, ExhaustivenessCtx, SPat};

        // Collect all bail constructors needed across all bindings
        let mut needed: HashSet<String> = HashSet::new();

        for ((pat, _), ty) in bindings.iter().zip(binding_types.iter()) {
            let resolved = self.sub.apply(ty);
            let type_name = match &resolved {
                Type::Con(name, _) => name,
                _ => continue,
            };
            let all_variants = match self.adt_variants.get(type_name) {
                Some(v) => v,
                None => continue,
            };

            // If the binding pattern is a wildcard/var, it matches everything -- no bail
            match pat {
                Pat::Wildcard { .. } | Pat::Var { .. } => continue,
                _ => {}
            }

            // Find which constructor the binding pattern matches
            let matched = match pat {
                Pat::Constructor { name, .. } => Some(name.as_str()),
                Pat::Lit {
                    value: Lit::Bool(b),
                    ..
                } => Some(if *b { "True" } else { "False" }),
                _ => None,
            };

            for (v, _arity) in all_variants {
                if matched != Some(v.as_str()) {
                    needed.insert(v.clone());
                }
            }
        }

        if needed.is_empty() {
            return Ok(());
        }

        // Use Maranget to check else arm coverage
        let ctx = ExhaustivenessCtx {
            adt_variants: &self.adt_variants,
        };

        // Build a matrix from else arms (each is a single-column pattern)
        let matrix: Vec<Vec<SPat>> = else_arms
            .iter()
            .filter(|arm| arm.guard.is_none())
            .map(|arm| vec![exh::simplify_pat(&arm.pattern)])
            .collect();

        // Check that each needed bail constructor is covered
        let mut missing_ctors = Vec::new();
        for ctor_name in &needed {
            let arity = self
                .adt_variants
                .values()
                .flat_map(|v| v.iter())
                .find(|(n, _)| n == ctor_name)
                .map(|(_, a)| *a)
                .unwrap_or(0);
            let row = vec![SPat::Constructor(
                ctor_name.clone(),
                vec![SPat::Wildcard; arity],
            )];
            if exh::useful(&ctx, &matrix, &row) {
                missing_ctors.push(ctor_name.as_str());
            }
        }

        if missing_ctors.is_empty() {
            Ok(())
        } else {
            missing_ctors.sort();
            Err(Diagnostic::error_at(
                span,
                format!(
                    "non-exhaustive do...else: missing {}",
                    missing_ctors.join(", ")
                ),
            ))
        }
    }

    // --- Effect & handler helpers ---

    /// Infer the type of a `with` expression: `expr with handler`
    pub(crate) fn infer_with(
        &mut self,
        expr: &Expr,
        handler: &ast::Handler,
        _with_span: Span,
    ) -> Result<Type, Diagnostic> {
        let handled = self.handler_handled_effects(handler);

        // Build op_name -> (arm_span, source_module) map for this handler and push onto the stack.
        // This lets EffectCall inference record which arm handles each call (for LSP go-to-def).
        let arm_stack_entry: std::collections::HashMap<String, (Span, Option<String>)> =
            match handler {
                ast::Handler::Named(name, handler_span) => {
                    // Record reference to the handler definition
                    if let Some(def_id) = self.env.def_id(name) {
                        let usage_id = crate::ast::NodeId::fresh();
                        self.record_reference(usage_id, *handler_span, def_id);
                    }
                    self.handlers
                        .get(name)
                        .map(|h| {
                            let src = h.source_module.clone();
                            h.arm_spans
                                .iter()
                                .map(|(op, &span)| (op.clone(), (span, src.clone())))
                                .collect()
                        })
                        .unwrap_or_default()
                }
                ast::Handler::Inline { named, arms, .. } => {
                    let mut map = std::collections::HashMap::new();
                    for n in named {
                        // Record reference to each named handler
                        if let Some(def_id) = self.env.def_id(n) {
                            let usage_id = crate::ast::NodeId::fresh();
                            self.record_reference(usage_id, _with_span, def_id);
                        }
                        if let Some(h) = self.handlers.get(n) {
                            let src = h.source_module.clone();
                            map.extend(
                                h.arm_spans
                                    .iter()
                                    .map(|(op, &span)| (op.clone(), (span, src.clone()))),
                            );
                        }
                    }
                    for arm in arms {
                        map.insert(arm.op_name.clone(), (arm.span, None));
                    }
                    map
                }
            };
        self.with_arm_stacks.push(arm_stack_entry);

        let ty = self.infer_with_inner(expr, handler, handled)?;
        self.with_arm_stacks.pop();

        Ok(ty)
    }

    fn infer_with_inner(
        &mut self,
        expr: &Expr,
        handler: &ast::Handler,
        handled: HashSet<String>,
    ) -> Result<Type, Diagnostic> {
        // Infer the inner expression, tracking its effects separately
        let saved_effects = std::mem::take(&mut self.current_effects);
        let saved_effect_cache = std::mem::take(&mut self.effect_type_param_cache);
        let expr_ty = self.infer_expr(expr)?;
        // Capture the inner expression's effect type param cache before restoring.
        // Inline handler arms need these bindings to properly type resume arguments.
        let inner_effect_cache = self.effect_type_param_cache.clone();
        // Unnecessary handler check: if the inner expression doesn't use any of
        // the handled effects, the handler is unnecessary (e.g. `with` on a pure
        // call or a partial application). Only emit when the callee is a known
        // local function/binding; skip for imports, EffArrow params, qualified
        // calls, etc. where effects are tracked outside fun_effects.
        if !handled.is_empty() && self.current_effects.is_disjoint(&handled) {
            let callee_name = extract_callee_name(expr);
            let callee_effects_known = callee_name
                .as_ref()
                .map(|name| {
                    self.fun_effects.contains_key(name.as_str())
                        || self.let_effect_bindings.contains_key(name.as_str())
                })
                .unwrap_or(false);
            if callee_effects_known {
                let mut effects: Vec<_> = handled.iter().cloned().collect();
                effects.sort();
                self.collected_diagnostics.push(Diagnostic::error_at(
                    expr.span,
                    format!(
                        "expression does not use effects {{{}}}; handler is unnecessary",
                        effects.join(", ")
                    ),
                ));
            }
        }
        // Subtract handled effects from the inner expression's effects
        for eff in &handled {
            self.current_effects.remove(eff);
        }
        let inner_effects = std::mem::replace(&mut self.current_effects, saved_effects);
        self.effect_type_param_cache = saved_effect_cache;
        self.current_effects.extend(inner_effects);

        let with_span = expr.span;
        match handler {
            ast::Handler::Named(name, _) => {
                if !self.handlers.contains_key(name) && self.env.get(name).is_none() {
                    return Err(Diagnostic::error_at(
                        with_span,
                        format!("undefined handler: {}", name),
                    ));
                }
                if let Some((param_var_id, ret_ty)) =
                    self.handlers.get(name).and_then(|h| h.return_type.clone())
                {
                    self.unify_at(&Type::Var(param_var_id), &expr_ty, with_span)?;
                    Ok(self.sub.apply(&ret_ty))
                } else {
                    Ok(expr_ty)
                }
            }
            ast::Handler::Inline {
                named,
                arms,
                return_clause,
            } => {
                for name in named {
                    if !self.handlers.contains_key(name) && self.env.get(name).is_none() {
                        return Err(Diagnostic::error_at(
                            with_span,
                            format!("undefined handler: {}", name),
                        ));
                    }
                }

                let saved_effects_arms = std::mem::take(&mut self.current_effects);

                // Compute answer_ty: infer return clause first if present,
                // since arms need it for resume return type and body unification.
                let answer_ty = if let Some(ret_arm) = return_clause {
                    let saved_env = self.env.clone();
                    if let Some((param_name, _)) = ret_arm.params.first() {
                        self.env.insert(
                            param_name.clone(),
                            Scheme {
                                forall: vec![],
                                constraints: vec![],
                                ty: expr_ty.clone(),
                            },
                        );
                    }
                    let ret_ty = self.infer_expr(&ret_arm.body)?;
                    self.env = saved_env;
                    ret_ty
                } else {
                    expr_ty.clone()
                };

                // Use inner expression's effect cache so inline handler arms
                // see the same type param bindings as the inner expression.
                let outer_effect_cache =
                    std::mem::replace(&mut self.effect_type_param_cache, inner_effect_cache);

                for arm in arms {
                    let op_sig = self.lookup_effect_op(&arm.op_name, None, arm.span).ok();

                    let saved_env = self.env.clone();
                    let saved_resume = self.resume_type.take();
                    let saved_resume_ret = self.resume_return_type.take();

                    if let Some(ref sig) = op_sig {
                        self.resume_type = Some(sig.return_type.clone());
                        self.resume_return_type = Some(answer_ty.clone());
                        for (i, (param_name, _)) in arm.params.iter().enumerate() {
                            let param_ty = if i < sig.params.len() {
                                sig.params[i].1.clone()
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
                    } else {
                        for (param_name, _) in &arm.params {
                            let param_ty = self.fresh_var();
                            self.env.insert(
                                param_name.clone(),
                                Scheme {
                                    forall: vec![],
                                    constraints: vec![],
                                    ty: param_ty,
                                },
                            );
                        }
                    }

                    let arm_ty = self.infer_expr(&arm.body)?;
                    // Each arm must produce the answer type
                    self.unify_at(&arm_ty, &answer_ty, arm.span)?;

                    self.resume_type = saved_resume;
                    self.resume_return_type = saved_resume_ret;
                    self.env = saved_env;
                }

                // Restore the outer effect cache
                self.effect_type_param_cache = outer_effect_cache;

                for eff in &handled {
                    self.current_effects.remove(eff);
                }
                let arm_effects = std::mem::replace(&mut self.current_effects, saved_effects_arms);
                self.current_effects.extend(arm_effects);

                Ok(answer_ty)
            }
        }
    }

    /// Find which effect an operation belongs to.
    pub(crate) fn effect_for_op(&self, op_name: &str, qualifier: Option<&str>) -> Option<String> {
        if let Some(effect_name) = qualifier
            && self.effects.contains_key(effect_name)
        {
            return Some(effect_name.to_string());
        }
        for (effect_name, info) in &self.effects {
            if info.ops.iter().any(|o| o.name == op_name) {
                return Some(effect_name.clone());
            }
        }
        None
    }

    /// Determine which effects a handler handles.
    pub(crate) fn handler_handled_effects(&self, handler: &ast::Handler) -> HashSet<String> {
        let mut handled = HashSet::new();
        match handler {
            ast::Handler::Named(name, _) => {
                if let Some(info) = self.handlers.get(name) {
                    handled.extend(info.effects.iter().cloned());
                }
            }
            ast::Handler::Inline { named, arms, .. } => {
                for name in named {
                    if let Some(info) = self.handlers.get(name) {
                        handled.extend(info.effects.iter().cloned());
                    }
                }
                for arm in arms {
                    if let Some(effect_name) = self.effect_for_op(&arm.op_name, None) {
                        handled.insert(effect_name);
                    }
                }
            }
        }
        handled
    }

    /// Instantiate an effect op signature, reusing cached type param vars for the same effect
    /// within the current function scope. This ensures `get` and `put` from `State s` share `s`.
    fn instantiate_effect_op(
        &mut self,
        effect_name: &str,
        op: &EffectOpSig,
        type_params: &[u32],
    ) -> EffectOpSig {
        if type_params.is_empty() {
            // No effect-level type params, but the op may have free type vars
            // (e.g. Process.spawn returns Pid msg where msg is free).
            // Collect all var IDs and instantiate fresh per call.
            let mut free_vars = std::collections::HashSet::new();
            fn collect_vars(ty: &Type, vars: &mut std::collections::HashSet<u32>) {
                match ty {
                    Type::Var(id) => {
                        vars.insert(*id);
                    }
                    Type::Arrow(a, b) | Type::EffArrow(a, b, _) => {
                        collect_vars(a, vars);
                        collect_vars(b, vars);
                    }
                    Type::Con(_, args) => {
                        for a in args {
                            collect_vars(a, vars);
                        }
                    }
                    Type::Record(fields) => {
                        for (_, ty) in fields {
                            collect_vars(ty, vars);
                        }
                    }
                    Type::Error | Type::Never => {}
                }
            }
            for (_, t) in &op.params {
                collect_vars(t, &mut free_vars);
            }
            collect_vars(&op.return_type, &mut free_vars);
            if free_vars.is_empty() {
                return op.clone();
            }
            let mapping: std::collections::HashMap<u32, Type> =
                free_vars.iter().map(|&id| (id, self.fresh_var())).collect();
            return EffectOpSig {
                name: op.name.clone(),
                params: op
                    .params
                    .iter()
                    .map(|(label, t)| (label.clone(), self.replace_vars(t, &mapping)))
                    .collect(),
                return_type: self.replace_vars(&op.return_type, &mapping),
            };
        }
        // Reuse cached mapping or create fresh vars
        let mapping = if let Some(cached) = self.effect_type_param_cache.get(effect_name) {
            cached.clone()
        } else {
            let mapping: std::collections::HashMap<u32, Type> = type_params
                .iter()
                .map(|&old_id| (old_id, self.fresh_var()))
                .collect();
            self.effect_type_param_cache
                .insert(effect_name.to_string(), mapping.clone());
            mapping
        };
        EffectOpSig {
            name: op.name.clone(),
            params: op
                .params
                .iter()
                .map(|(label, t)| (label.clone(), self.replace_vars(t, &mapping)))
                .collect(),
            return_type: self.replace_vars(&op.return_type, &mapping),
        }
    }

    /// Look up an effect operation by name, optionally qualified (e.g. `Cache.get`).
    /// Returns the op signature with fresh type vars for the effect's type params.
    pub(crate) fn lookup_effect_op(
        &mut self,
        op_name: &str,
        qualifier: Option<&str>,
        span: Span,
    ) -> Result<EffectOpSig, Diagnostic> {
        if let Some(effect_name) = qualifier {
            let info = self
                .effects
                .get(effect_name)
                .ok_or_else(|| {
                    Diagnostic::error_at(span, format!("undefined effect: {}", effect_name))
                })?
                .clone();
            let op = info.ops.iter().find(|o| o.name == op_name).ok_or_else(|| {
                Diagnostic::error_at(
                    span,
                    format!("effect '{}' has no operation '{}'", effect_name, op_name),
                )
            })?;
            Ok(self.instantiate_effect_op(effect_name, op, &info.type_params))
        } else {
            let mut found: Option<(String, EffectOpSig, Vec<u32>)> = None;
            for (eff_name, info) in &self.effects {
                if let Some(op) = info.ops.iter().find(|o| o.name == op_name) {
                    if found.is_some() {
                        return Err(Diagnostic::error_at(
                            span,
                            format!(
                                "ambiguous effect operation '{}': found in multiple effects",
                                op_name
                            ),
                        ));
                    }
                    found = Some((eff_name.clone(), op.clone(), info.type_params.clone()));
                }
            }
            let (eff_name, op, type_params) = found.ok_or_else(|| {
                Diagnostic::error_at(span, format!("undefined effect operation: {}", op_name))
            })?;
            Ok(self.instantiate_effect_op(&eff_name, &op, &type_params))
        }
    }
}
