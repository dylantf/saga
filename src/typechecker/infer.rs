use std::collections::HashSet;

use crate::ast::{self, BinOp, Expr, Lit, Pat, Stmt};

use super::{Checker, EffectOpSig, Scheme, Type, TypeError};
use crate::token::Span;

impl Checker {
    // --- Expression inference ---

    pub fn infer_expr(&mut self, expr: &Expr) -> Result<Type, TypeError> {
        match expr {
            Expr::Lit { value, .. } => Ok(match value {
                Lit::Int(_) => Type::int(),
                Lit::Float(_) => Type::float(),
                Lit::String(_) => Type::string(),
                Lit::Bool(_) => Type::bool(),
                Lit::Unit => Type::unit(),
            }),

            Expr::Var { name, span } => {
                if let Some(scheme) = self.env.get(name) {
                    let scheme = scheme.clone();
                    // Propagate effects from functions with known needs
                    if let Some(effects) = self.fun_effects.get(name).cloned() {
                        self.current_effects.extend(effects);
                    }
                    let (ty, constraints) = self.instantiate(&scheme);
                    for (trait_name, trait_ty) in constraints {
                        self.pending_constraints.push((trait_name, trait_ty, *span));
                    }
                    Ok(ty)
                } else {
                    Err(TypeError::at(
                        *span,
                        format!("undefined variable: {}", name),
                    ))
                }
            }

            Expr::Constructor { name, span } => {
                if let Some(scheme) = self.constructors.get(name) {
                    let scheme = scheme.clone();
                    let (ty, _) = self.instantiate(&scheme);
                    Ok(ty)
                } else {
                    Err(TypeError::at(
                        *span,
                        format!("undefined constructor: {}", name),
                    ))
                }
            }

            Expr::App { func, arg, span } => {
                let func_ty = self.infer_expr(func)?;
                let arg_ty = self.infer_expr(arg)?;
                let ret_ty = self.fresh_var();
                self.unify_at(
                    &func_ty,
                    &Type::Arrow(Box::new(arg_ty), Box::new(ret_ty.clone())),
                    *span,
                )?;
                // If the function declares its argument absorbs specific effects
                // (via EffArrow on the parameter type), subtract those from current_effects.
                // This handles HOFs like `try (fun () -> fail! ...)` where `try` absorbs Fail.
                let resolved_func = self.sub.apply(&func_ty);
                let param_ty = match resolved_func {
                    Type::Arrow(p, _) | Type::EffArrow(p, _, _) => Some(self.sub.apply(&p)),
                    _ => None,
                };
                if let Some(Type::EffArrow(_, _, needs)) = param_ty {
                    for eff in &needs {
                        self.current_effects.remove(eff);
                    }
                }
                Ok(ret_ty)
            }

            Expr::BinOp {
                op,
                left,
                right,
                span,
            } => {
                let left_ty = self.infer_expr(left)?;
                let right_ty = self.infer_expr(right)?;
                match op {
                    BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Mod => {
                        self.unify_at(&left_ty, &right_ty, *span)?;
                        self.pending_constraints
                            .push(("Num".into(), left_ty.clone(), *span));
                        Ok(left_ty)
                    }
                    BinOp::Eq | BinOp::NotEq => {
                        self.unify_at(&left_ty, &right_ty, *span)?;
                        self.pending_constraints
                            .push(("Eq".into(), left_ty.clone(), *span));
                        Ok(Type::bool())
                    }
                    BinOp::Lt | BinOp::Gt | BinOp::LtEq | BinOp::GtEq => {
                        self.unify_at(&left_ty, &right_ty, *span)?;
                        self.pending_constraints
                            .push(("Ord".into(), left_ty.clone(), *span));
                        Ok(Type::bool())
                    }
                    BinOp::And | BinOp::Or => {
                        self.unify_at(&left_ty, &Type::bool(), *span)?;
                        self.unify_at(&right_ty, &Type::bool(), *span)?;
                        Ok(Type::bool())
                    }
                    BinOp::Concat => {
                        self.unify_at(&left_ty, &Type::string(), *span)?;
                        self.unify_at(&right_ty, &Type::string(), *span)?;
                        Ok(Type::string())
                    }
                }
            }

            Expr::UnaryMinus { expr, span } => {
                let ty = self.infer_expr(expr)?;
                self.pending_constraints
                    .push(("Num".into(), ty.clone(), *span));
                Ok(ty)
            }

            Expr::If {
                cond,
                then_branch,
                else_branch,
                span,
            } => {
                let cond_ty = self.infer_expr(cond)?;
                self.unify_at(&cond_ty, &Type::bool(), cond.span())?;
                let then_ty = self.infer_expr(then_branch)?;
                let else_ty = self.infer_expr(else_branch)?;
                self.unify_at(&then_ty, &else_ty, *span)?;
                Ok(then_ty)
            }

            Expr::Block { stmts, .. } => self.infer_block(stmts),

            Expr::Lambda { params, body, .. } => {
                let saved_env = self.env.clone();
                let mut param_types = Vec::new();
                for pat in params {
                    let ty = self.fresh_var();
                    self.bind_pattern(pat, &ty)?;
                    param_types.push(ty);
                }
                // Lambda body effects propagate up to the enclosing context.
                // Effects are absorbed at function boundaries (needs declarations) or
                // by `with` handlers, same as any other expression.
                let body_ty = self.infer_expr(body)?;
                self.env = saved_env;
                // Build curried arrow: a -> b -> c -> ret
                let mut result = body_ty;
                for param_ty in param_types.into_iter().rev() {
                    result = Type::Arrow(Box::new(param_ty), Box::new(result));
                }
                Ok(result)
            }

            Expr::Case {
                scrutinee,
                arms,
                span: _,
            } => {
                let scrut_ty = self.infer_expr(scrutinee)?;
                let result_ty = self.fresh_var();

                for arm in arms {
                    let saved_env = self.env.clone();

                    self.bind_pattern(&arm.pattern, &scrut_ty)?;

                    if let Some(guard) = &arm.guard {
                        let guard_ty = self.infer_expr(guard)?;
                        self.unify_at(&guard_ty, &Type::bool(), guard.span())?;
                    }

                    let body_ty = self.infer_expr(&arm.body)?;
                    self.unify_at(&result_ty, &body_ty, arm.body.span())?;

                    self.env = saved_env;
                }

                Ok(result_ty)
            }

            Expr::RecordCreate { name, fields, span } => {
                let def = self.records.get(name).cloned().ok_or_else(|| {
                    TypeError::at(*span, format!("undefined record type: {}", name))
                })?;

                for (fname, fexpr) in fields {
                    let expected = def.iter().find(|(n, _)| n == fname).ok_or_else(|| {
                        TypeError::at(
                            fexpr.span(),
                            format!("unknown field '{}' on record {}", fname, name),
                        )
                    })?;
                    let actual = self.infer_expr(fexpr)?;
                    self.unify_at(&expected.1, &actual, fexpr.span())?;
                }

                Ok(Type::Con(name.clone(), vec![]))
            }

            Expr::FieldAccess { expr, field, span } => {
                let expr_ty = self.infer_expr(expr)?;
                let resolved = self.sub.apply(&expr_ty);

                match &resolved {
                    Type::Con(name, _) => {
                        let def = self.records.get(name).cloned().ok_or_else(|| {
                            TypeError::at(*span, format!("type {} is not a record", name))
                        })?;
                        let (_, field_ty) =
                            def.iter().find(|(n, _)| n == field).ok_or_else(|| {
                                TypeError::at(
                                    *span,
                                    format!("no field '{}' on record {}", field, name),
                                )
                            })?;
                        Ok(field_ty.clone())
                    }
                    Type::Var(_) => {
                        let candidates: Vec<_> = self
                            .records
                            .iter()
                            .filter_map(|(rname, fields)| {
                                fields
                                    .iter()
                                    .find(|(n, _)| n == field)
                                    .map(|(_, ty)| (rname.clone(), ty.clone()))
                            })
                            .collect();
                        match candidates.len() {
                            1 => {
                                let (rname, field_ty) = &candidates[0];
                                self.unify(&resolved, &Type::Con(rname.clone(), vec![]))?;
                                Ok(field_ty.clone())
                            }
                            0 => Err(TypeError::at(
                                *span,
                                format!("no record has field '{}'", field),
                            )),
                            _ => {
                                // Multiple records have this field. Narrow by intersecting
                                // with candidates already observed for this variable (from
                                // previous field accesses on the same var).
                                let id = match &resolved {
                                    Type::Var(id) => *id,
                                    _ => unreachable!(),
                                };
                                let narrowed: Vec<(String, Type)> =
                                    match self.field_candidates.get(&id) {
                                        Some((existing, _)) => candidates
                                            .into_iter()
                                            .filter(|(n, _)| existing.contains(n))
                                            .collect(),
                                        None => candidates,
                                    };
                                match narrowed.len() {
                                    0 => Err(TypeError::at(
                                        *span,
                                        format!(
                                            "no single record type has all accessed fields (including '{}')",
                                            field
                                        ),
                                    )),
                                    1 => {
                                        let (rname, field_ty) =
                                            narrowed.into_iter().next().unwrap();
                                        self.unify(&resolved, &Type::Con(rname, vec![]))?;
                                        self.field_candidates.remove(&id);
                                        Ok(field_ty)
                                    }
                                    _ => {
                                        // Still multiple candidates after narrowing. Return the
                                        // field type if all agree so we can keep checking; the
                                        // end-of-body check will error if the var stays ambiguous.
                                        let names: Vec<String> =
                                            narrowed.iter().map(|(n, _)| n.clone()).collect();
                                        let first_ty = self.sub.apply(&narrowed[0].1);
                                        let all_agree = narrowed
                                            .iter()
                                            .all(|(_, ty)| self.sub.apply(ty) == first_ty);
                                        if all_agree {
                                            self.field_candidates.insert(id, (names, *span));
                                            Ok(first_ty)
                                        } else {
                                            Err(TypeError::at(
                                                *span,
                                                format!(
                                                    "ambiguous field '{}': found in [{}] with different types; add a type annotation",
                                                    field,
                                                    names.join(", ")
                                                ),
                                            ))
                                        }
                                    }
                                }
                            }
                        }
                    }
                    _ => Err(TypeError::at(
                        *span,
                        format!("cannot access field '{}' on type {}", field, resolved),
                    )),
                }
            }

            Expr::RecordUpdate {
                record,
                fields,
                span,
            } => {
                let rec_ty = self.infer_expr(record)?;
                let mut resolved = self.sub.apply(&rec_ty);

                if matches!(&resolved, Type::Var(_))
                    && let Some((fname, _)) = fields.first()
                {
                    let candidates: Vec<_> = self
                        .records
                        .iter()
                        .filter(|(_, flds)| flds.iter().any(|(n, _)| n == fname))
                        .map(|(rname, _)| rname.clone())
                        .collect();
                    if candidates.len() == 1 {
                        self.unify(&resolved, &Type::Con(candidates[0].clone(), vec![]))?;
                        resolved = self.sub.apply(&rec_ty);
                    }
                }

                match &resolved {
                    Type::Con(name, _) => {
                        let def = self.records.get(name).cloned().ok_or_else(|| {
                            TypeError::at(*span, format!("type {} is not a record", name))
                        })?;
                        for (fname, fexpr) in fields {
                            let expected =
                                def.iter().find(|(n, _)| n == fname).ok_or_else(|| {
                                    TypeError::at(
                                        fexpr.span(),
                                        format!("unknown field '{}' on record {}", fname, name),
                                    )
                                })?;
                            let actual = self.infer_expr(fexpr)?;
                            self.unify_at(&expected.1, &actual, fexpr.span())?;
                        }
                        Ok(resolved.clone())
                    }
                    _ => Err(TypeError::at(
                        *span,
                        format!("cannot update non-record type {}", resolved),
                    )),
                }
            }

            Expr::EffectCall {
                name,
                qualifier,
                span,
                ..
            } => {
                let op_sig = self.lookup_effect_op(name, qualifier.as_deref(), *span)?;

                // Track which effect this op belongs to
                if let Some(effect_name) = self.effect_for_op(name, qualifier.as_deref()) {
                    self.current_effects.insert(effect_name);
                }

                // Build curried function type: param1 -> param2 -> ... -> return_type
                let mut ty = op_sig.return_type.clone();
                if op_sig.params.is_empty() {
                    // Zero-param ops like `get! ()` still take a Unit argument
                    ty = Type::Arrow(Box::new(Type::unit()), Box::new(ty));
                } else {
                    for param_ty in op_sig.params.iter().rev() {
                        ty = Type::Arrow(Box::new(param_ty.clone()), Box::new(ty));
                    }
                }
                Ok(ty)
            }

            Expr::With { expr, handler, .. } => self.infer_with(expr, handler),

            Expr::Resume { value, span } => {
                let val_ty = self.infer_expr(value)?;
                if let Some(expected) = &self.resume_type.clone() {
                    self.unify_at(&val_ty, expected, *span)?;
                }
                let ty = self.fresh_var();
                Ok(ty)
            }

            Expr::Tuple { elements, .. } => {
                let tys: Vec<Type> = elements
                    .iter()
                    .map(|e| self.infer_expr(e))
                    .collect::<Result<_, _>>()?;
                Ok(Type::Con("Tuple".into(), tys))
            }

            Expr::QualifiedName { module, name, span } => {
                let key = format!("{}.{}", module, name);
                match self.env.get(&key).cloned() {
                    Some(scheme) => {
                        let (ty, constraints) = self.instantiate(&scheme);
                        for (trait_name, trait_ty) in constraints {
                            self.pending_constraints.push((trait_name, trait_ty, *span));
                        }
                        Ok(ty)
                    }
                    None => Err(TypeError {
                        message: format!("unknown qualified name '{}.{}'", module, name),
                        span: Some(*span),
                    }),
                }
            }
        }
    }

    pub(crate) fn infer_block(&mut self, stmts: &[Stmt]) -> Result<Type, TypeError> {
        let mut last_ty = Type::unit();
        for stmt in stmts {
            match stmt {
                Stmt::Let {
                    pattern,
                    annotation,
                    value,
                    span,
                } => {
                    let ty = self.infer_expr(value)?;
                    if let Some(ann) = annotation {
                        let ann_ty = self.convert_type_expr(ann, &mut vec![]);
                        self.unify_at(&ty, &ann_ty, *span)?;
                    }
                    if let Pat::Var { name, .. } = pattern {
                        let scheme = self.generalize(&ty);
                        self.env.insert(name.clone(), scheme);
                    } else {
                        self.bind_pattern(pattern, &ty)?;
                    }
                    last_ty = Type::unit();
                }
                Stmt::Expr(expr) => {
                    last_ty = self.infer_expr(expr)?;
                }
            }
        }
        Ok(last_ty)
    }

    // --- Pattern binding ---

    /// Bind a pattern to a type, adding variables to the environment.
    pub(crate) fn bind_pattern(&mut self, pat: &Pat, ty: &Type) -> Result<(), TypeError> {
        match pat {
            Pat::Wildcard { .. } => Ok(()),
            Pat::Var { name, .. } => {
                self.env.insert(
                    name.clone(),
                    Scheme {
                        forall: vec![],
                        constraints: vec![],
                        ty: ty.clone(),
                    },
                );
                Ok(())
            }
            Pat::Lit { value, span } => {
                let lit_ty = match value {
                    Lit::Int(_) => Type::int(),
                    Lit::Float(_) => Type::float(),
                    Lit::String(_) => Type::string(),
                    Lit::Bool(_) => Type::bool(),
                    Lit::Unit => Type::unit(),
                };
                self.unify_at(ty, &lit_ty, *span)
            }
            Pat::Constructor { name, args, span } => {
                let ctor_scheme = self.constructors.get(name).cloned().ok_or_else(|| {
                    TypeError::at(*span, format!("undefined constructor in pattern: {}", name))
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
                            return Err(TypeError::at(
                                *span,
                                format!("constructor {} applied to too many arguments", name),
                            ));
                        }
                    }
                }
                self.unify_at(ty, &current, *span)
            }
            Pat::Record { name, fields, span } => {
                let def = self.records.get(name).cloned().ok_or_else(|| {
                    TypeError::at(*span, format!("undefined record type in pattern: {}", name))
                })?;
                self.unify_at(ty, &Type::Con(name.clone(), vec![]), *span)?;

                for (fname, alias_pat) in fields {
                    let (_, field_ty) = def.iter().find(|(n, _)| n == fname).ok_or_else(|| {
                        TypeError::at(
                            *span,
                            format!("unknown field '{}' on record {}", fname, name),
                        )
                    })?;
                    match alias_pat {
                        Some(pat) => self.bind_pattern(pat, field_ty)?,
                        None => {
                            self.env.insert(
                                fname.clone(),
                                Scheme {
                                    forall: vec![],
                                    constraints: vec![],
                                    ty: field_ty.clone(),
                                },
                            );
                        }
                    }
                }
                Ok(())
            }

            Pat::Tuple { elements, span } => {
                let elem_tys: Vec<Type> = elements.iter().map(|_| self.fresh_var()).collect();
                let tuple_ty = Type::Con("Tuple".into(), elem_tys.clone());
                self.unify_at(ty, &tuple_ty, *span)?;
                for (pat, elem_ty) in elements.iter().zip(elem_tys.iter()) {
                    self.bind_pattern(pat, elem_ty)?;
                }
                Ok(())
            }
        }
    }

    // --- Effect & handler helpers ---

    /// Infer the type of a `with` expression: `expr with handler`
    pub(crate) fn infer_with(
        &mut self,
        expr: &Expr,
        handler: &ast::Handler,
    ) -> Result<Type, TypeError> {
        let saved_effects = std::mem::take(&mut self.current_effects);

        let expr_ty = self.infer_expr(expr)?;

        let handled = self.handler_handled_effects(handler);
        for eff in &handled {
            self.current_effects.remove(eff);
        }

        let inner_effects = std::mem::replace(&mut self.current_effects, saved_effects);
        self.current_effects.extend(inner_effects);

        let with_span = expr.span();
        match handler {
            ast::Handler::Named(name) => {
                if !self.handlers.contains_key(name) && self.env.get(name).is_none() {
                    return Err(TypeError::at(
                        with_span,
                        format!("undefined handler: {}", name),
                    ));
                }
                Ok(expr_ty)
            }
            ast::Handler::Inline {
                named,
                arms,
                return_clause,
            } => {
                for name in named {
                    if !self.handlers.contains_key(name) && self.env.get(name).is_none() {
                        return Err(TypeError::at(
                            with_span,
                            format!("undefined handler: {}", name),
                        ));
                    }
                }

                for arm in arms {
                    let op_sig = self.lookup_effect_op(&arm.op_name, None, arm.span).ok();

                    let saved_env = self.env.clone();
                    let saved_resume = self.resume_type.take();

                    if let Some(ref sig) = op_sig {
                        self.resume_type = Some(sig.return_type.clone());
                        for (i, param_name) in arm.params.iter().enumerate() {
                            let param_ty = if i < sig.params.len() {
                                sig.params[i].clone()
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
                        for param_name in &arm.params {
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

                    self.infer_expr(&arm.body)?;

                    self.resume_type = saved_resume;
                    self.env = saved_env;
                }

                if let Some(ret_arm) = return_clause {
                    let saved_env = self.env.clone();
                    if let Some(param_name) = ret_arm.params.first() {
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
                    Ok(ret_ty)
                } else {
                    Ok(expr_ty)
                }
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
        for (effect_name, ops) in &self.effects {
            if ops.iter().any(|o| o.name == op_name) {
                return Some(effect_name.clone());
            }
        }
        None
    }

    /// Determine which effects a handler handles.
    pub(crate) fn handler_handled_effects(&self, handler: &ast::Handler) -> HashSet<String> {
        let mut handled = HashSet::new();
        match handler {
            ast::Handler::Named(name) => {
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

    /// Look up an effect operation by name, optionally qualified (e.g. `Cache.get`).
    pub(crate) fn lookup_effect_op(
        &mut self,
        op_name: &str,
        qualifier: Option<&str>,
        span: Span,
    ) -> Result<EffectOpSig, TypeError> {
        if let Some(effect_name) = qualifier {
            let ops = self
                .effects
                .get(effect_name)
                .ok_or_else(|| TypeError::at(span, format!("undefined effect: {}", effect_name)))?;
            let op = ops.iter().find(|o| o.name == op_name).ok_or_else(|| {
                TypeError::at(
                    span,
                    format!("effect '{}' has no operation '{}'", effect_name, op_name),
                )
            })?;
            Ok(op.clone())
        } else {
            let mut found: Option<EffectOpSig> = None;
            for ops in self.effects.values() {
                if let Some(op) = ops.iter().find(|o| o.name == op_name) {
                    if found.is_some() {
                        return Err(TypeError::at(
                            span,
                            format!(
                                "ambiguous effect operation '{}': found in multiple effects",
                                op_name
                            ),
                        ));
                    }
                    found = Some(op.clone());
                }
            }
            found.ok_or_else(|| {
                TypeError::at(span, format!("undefined effect operation: {}", op_name))
            })
        }
    }
}
