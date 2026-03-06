use std::collections::{HashMap, HashSet};

use crate::ast::{self, BinOp, Decl, Expr, Lit, Pat, Stmt};

use super::{Checker, EffectOpSig, HandlerInfo, Scheme, Type, TypeError};

impl Checker {
    // --- Expression inference ---

    pub fn infer_expr(&mut self, expr: &Expr) -> Result<Type, TypeError> {
        match expr {
            Expr::Lit { value, .. } => Ok(match value {
                Lit::Int(_) => Type::Int,
                Lit::Float(_) => Type::Float,
                Lit::String(_) => Type::String,
                Lit::Bool(_) => Type::Bool,
                Lit::Unit => Type::Unit,
            }),

            Expr::Var { name, span } => {
                if let Some(scheme) = self.env.get(name) {
                    let scheme = scheme.clone();
                    // Propagate effects from functions with known needs
                    if let Some(effects) = self.fun_effects.get(name).cloned() {
                        self.current_effects.extend(effects);
                    }
                    Ok(self.instantiate(&scheme))
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
                    Ok(self.instantiate(&scheme))
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
                        Ok(left_ty)
                    }
                    BinOp::Eq | BinOp::NotEq => {
                        self.unify_at(&left_ty, &right_ty, *span)?;
                        Ok(Type::Bool)
                    }
                    BinOp::Lt | BinOp::Gt | BinOp::LtEq | BinOp::GtEq => {
                        self.unify_at(&left_ty, &right_ty, *span)?;
                        Ok(Type::Bool)
                    }
                    BinOp::And | BinOp::Or => {
                        self.unify_at(&left_ty, &Type::Bool, *span)?;
                        self.unify_at(&right_ty, &Type::Bool, *span)?;
                        Ok(Type::Bool)
                    }
                    BinOp::Concat => {
                        self.unify_at(&left_ty, &Type::String, *span)?;
                        self.unify_at(&right_ty, &Type::String, *span)?;
                        Ok(Type::String)
                    }
                }
            }

            Expr::UnaryMinus { expr, .. } => {
                let ty = self.infer_expr(expr)?;
                Ok(ty)
            }

            Expr::If {
                cond,
                then_branch,
                else_branch,
                span,
            } => {
                let cond_ty = self.infer_expr(cond)?;
                self.unify_at(&cond_ty, &Type::Bool, cond.span())?;
                let then_ty = self.infer_expr(then_branch)?;
                let else_ty = self.infer_expr(else_branch)?;
                self.unify_at(&then_ty, &else_ty, *span)?;
                Ok(then_ty)
            }

            Expr::Block { stmts, .. } => self.infer_block(stmts),

            Expr::Lambda { params, body, .. } => {
                // For now, handle single-arm lambdas with simple var patterns
                let mut param_types = Vec::new();
                for pat in params {
                    let ty = self.fresh_var();
                    self.bind_pattern(pat, &ty)?;
                    param_types.push(ty);
                }
                // Lambda bodies are isolated: effects inside are deferred until call
                let saved_effects = std::mem::take(&mut self.current_effects);
                let body_ty = self.infer_expr(body)?;
                self.current_effects = saved_effects;
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
                        self.unify_at(&guard_ty, &Type::Bool, guard.span())?;
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
                            _ => Err(TypeError::at(
                                *span,
                                format!("ambiguous field '{}': found in multiple records", field),
                            )),
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
                let op_sig = self
                    .lookup_effect_op(name, qualifier.as_deref())
                    .map_err(|e| e.with_span(*span))?;

                // Track which effect this op belongs to
                if let Some(effect_name) = self.effect_for_op(name, qualifier.as_deref()) {
                    self.current_effects.insert(effect_name);
                }

                // Build curried function type: param1 -> param2 -> ... -> return_type
                // Args are applied via App nodes from parse_application
                let mut ty = op_sig.return_type.clone();
                if op_sig.params.is_empty() {
                    // Zero-param ops like `get! ()` still take a Unit argument
                    ty = Type::Arrow(Box::new(Type::Unit), Box::new(ty));
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
                // resume transfers control; its own type is a fresh var
                // (the handler arm body continues after resume, so this is the "result" of resume)
                let ty = self.fresh_var();
                Ok(ty)
            }
        }
    }

    fn infer_block(&mut self, stmts: &[Stmt]) -> Result<Type, TypeError> {
        let mut last_ty = Type::Unit;
        for stmt in stmts {
            match stmt {
                Stmt::Let { name, value, .. } => {
                    let ty = self.infer_expr(value)?;
                    let scheme = self.generalize(&ty);
                    self.env.insert(name.clone(), scheme);
                    last_ty = Type::Unit;
                }
                Stmt::Assign { value, .. } => {
                    self.infer_expr(value)?;
                    last_ty = Type::Unit;
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
    fn bind_pattern(&mut self, pat: &Pat, ty: &Type) -> Result<(), TypeError> {
        match pat {
            Pat::Wildcard { .. } => Ok(()),
            Pat::Var { name, .. } => {
                self.env.insert(
                    name.clone(),
                    Scheme {
                        forall: vec![],
                        ty: ty.clone(),
                    },
                );
                Ok(())
            }
            Pat::Lit { value, span } => {
                let lit_ty = match value {
                    Lit::Int(_) => Type::Int,
                    Lit::Float(_) => Type::Float,
                    Lit::String(_) => Type::String,
                    Lit::Bool(_) => Type::Bool,
                    Lit::Unit => Type::Unit,
                };
                self.unify_at(ty, &lit_ty, *span)
            }
            Pat::Constructor { name, args, span } => {
                let ctor_scheme = self.constructors.get(name).cloned().ok_or_else(|| {
                    TypeError::at(*span, format!("undefined constructor in pattern: {}", name))
                })?;
                let ctor_ty = self.instantiate(&ctor_scheme);
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
                        // No alias: bind field name as variable
                        None => {
                            self.env.insert(
                                fname.clone(),
                                Scheme {
                                    forall: vec![],
                                    ty: field_ty.clone(),
                                },
                            );
                        }
                    }
                }
                Ok(())
            }
        }
    }

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
                    name, operations, ..
                } => {
                    self.register_effect_def(name, operations)?;
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
                methods,
                span,
            } = decl
            {
                self.register_impl(trait_name, target_type, methods, *span)?;
            }
        }

        // Collect function annotations: name -> declared type, and effects
        let mut annotations: HashMap<std::string::String, Type> = HashMap::new();
        for decl in program {
            if let Decl::FunAnnotation {
                name,
                params,
                return_type,
                effects,
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
                    self.fun_effects
                        .insert(name.clone(), effects.iter().cloned().collect());
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
                self.check_fun_clauses(&name, &clauses, &fun_var, annotation.as_ref())?;
            } else {
                self.check_decl(&program[i])?;
                i += 1;
            }
        }
        Ok(())
    }

    fn check_decl(&mut self, decl: &Decl) -> Result<(), TypeError> {
        match decl {
            Decl::Let { name, value, .. } => {
                let ty = self.infer_expr(value)?;
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
                arms,
                return_clause,
                ..
            } => {
                self.register_handler(name, effect_names, arms, return_clause.as_deref())?;
                Ok(())
            }

            // Type annotations, type defs (already registered), effects, traits, impls,
            // imports, modules -- skip for now
            _ => Ok(()),
        }
    }

    /// Check a group of function clauses that share the same name.
    /// Handles recursion (pre-binds name) and multi-clause pattern matching.
    fn check_fun_clauses(
        &mut self,
        name: &str,
        clauses: &[&Decl],
        fun_var: &Type,
        annotation: Option<&Type>,
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
                    Type::Arrow(ann_param, ann_ret) => {
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

        // Save and clear effect tracking for this function body
        let saved_effects = std::mem::take(&mut self.current_effects);

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
                let guard_ty = self.infer_expr(guard)?;
                self.unify_at(&guard_ty, &Type::Bool, guard.span())?;
            }

            let body_ty = self.infer_expr(body)?;
            self.unify_at(&result_ty, &body_ty, body.span())?;

            self.env = saved_env;
        }

        // Check effect requirements against declared needs
        let body_effects = std::mem::replace(&mut self.current_effects, saved_effects);
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

        // Remove the function's own pre-bound entry before generalizing,
        // otherwise its type vars appear in env_vars and block generalization
        self.env.remove(name);
        let scheme = self.generalize(&fun_ty);
        self.env.insert(name.into(), scheme);
        Ok(())
    }

    // --- Registration helpers ---

    fn register_type_def(
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
                    ty: ctor_ty,
                },
            );
        }

        Ok(())
    }

    fn register_record_def(
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

    fn register_effect_def(
        &mut self,
        name: &str,
        operations: &[ast::EffectOp],
    ) -> Result<(), TypeError> {
        let mut ops = Vec::new();
        for op in operations {
            let mut params_list: Vec<(String, u32)> = vec![];
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
        self.effects.insert(name.into(), ops);
        Ok(())
    }

    fn register_handler(
        &mut self,
        name: &str,
        effect_names: &[String],
        arms: &[ast::HandlerArm],
        return_clause: Option<&ast::HandlerArm>,
    ) -> Result<(), TypeError> {
        let mut op_names = Vec::new();
        // Type-check each handler arm against its effect operation
        for arm in arms {
            let op_sig = self.lookup_effect_op(&arm.op_name, None)?;
            op_names.push(arm.op_name.clone());

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
                        ty: param_ty,
                    },
                );
            }

            self.infer_expr(&arm.body)?;
            self.resume_type = saved_resume;
            self.env = saved_env;
        }

        self.handlers.insert(
            name.into(),
            HandlerInfo {
                effects: effect_names.to_vec(),
                ops: op_names,
                has_return_clause: return_clause.is_some(),
            },
        );

        // Put the handler name in the env so it can be referenced
        self.env.insert(
            name.into(),
            Scheme {
                forall: vec![],
                ty: Type::Unit, // handlers don't have a meaningful standalone type
            },
        );

        Ok(())
    }

    // --- Effect & handler helpers ---

    /// Infer the type of a `with` expression: `expr with handler`
    fn infer_with(&mut self, expr: &Expr, handler: &ast::Handler) -> Result<Type, TypeError> {
        // Save outer effects, clear for inner expression
        let saved_effects = std::mem::take(&mut self.current_effects);

        let expr_ty = self.infer_expr(expr)?;

        // Determine which effects this handler handles and subtract them
        let handled = self.handler_handled_effects(handler);
        for eff in &handled {
            self.current_effects.remove(eff);
        }

        // Merge remaining (unhandled) effects back into outer set
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

                // Type-check inline arms (check bodies are well-typed, set up resume context)
                for arm in arms {
                    let op_sig = self.lookup_effect_op(&arm.op_name, None).ok();

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
                                    ty: param_ty,
                                },
                            );
                        }
                    } else {
                        // Unknown op -- bind params as fresh vars
                        for param_name in &arm.params {
                            let param_ty = self.fresh_var();
                            self.env.insert(
                                param_name.clone(),
                                Scheme {
                                    forall: vec![],
                                    ty: param_ty,
                                },
                            );
                        }
                    }

                    // Check the arm body is well-typed.
                    // We don't unify arm types with the result -- aborting handlers
                    // (no resume) can return a different type than the computation,
                    // and the runtime dispatches dynamically.
                    self.infer_expr(&arm.body)?;

                    self.resume_type = saved_resume;
                    self.env = saved_env;
                }

                // Return clause transforms the result type
                if let Some(ret_arm) = return_clause {
                    let saved_env = self.env.clone();
                    if let Some(param_name) = ret_arm.params.first() {
                        self.env.insert(
                            param_name.clone(),
                            Scheme {
                                forall: vec![],
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
    fn effect_for_op(&self, op_name: &str, qualifier: Option<&str>) -> Option<String> {
        if let Some(effect_name) = qualifier {
            if self.effects.contains_key(effect_name) {
                return Some(effect_name.to_string());
            }
        }
        for (effect_name, ops) in &self.effects {
            if ops.iter().any(|o| o.name == op_name) {
                return Some(effect_name.clone());
            }
        }
        None
    }

    /// Determine which effects a handler handles.
    fn handler_handled_effects(&self, handler: &ast::Handler) -> HashSet<String> {
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
    /// Returns a fresh copy of the op signature (type vars instantiated).
    fn lookup_effect_op(
        &mut self,
        op_name: &str,
        qualifier: Option<&str>,
    ) -> Result<EffectOpSig, TypeError> {
        if let Some(effect_name) = qualifier {
            let ops = self
                .effects
                .get(effect_name)
                .ok_or_else(|| TypeError::new(format!("undefined effect: {}", effect_name)))?;
            let op = ops.iter().find(|o| o.name == op_name).ok_or_else(|| {
                TypeError::new(format!(
                    "effect '{}' has no operation '{}'",
                    effect_name, op_name
                ))
            })?;
            Ok(op.clone())
        } else {
            let mut found: Option<EffectOpSig> = None;
            for ops in self.effects.values() {
                if let Some(op) = ops.iter().find(|o| o.name == op_name) {
                    if found.is_some() {
                        return Err(TypeError::new(format!(
                            "ambiguous effect operation '{}': found in multiple effects",
                            op_name
                        )));
                    }
                    found = Some(op.clone());
                }
            }
            found.ok_or_else(|| TypeError::new(format!("undefined effect operation: {}", op_name)))
        }
    }

    // --- Trait & impl helpers ---

    /// Replace occurrences of a trait's type param variable with a concrete type.
    /// Used when checking impl bodies: if the trait says `(x: a) -> String`
    /// and the impl is `for User`, we substitute a -> User to get `(x: User) -> String`.
    fn substitute_trait_param(&self, param_name: &str, replacement: &Type, ty: &Type) -> Type {
        match ty {
            Type::Var(id) => {
                // Check if this var corresponds to the trait's type param
                // by looking at what convert_type_expr assigned to it
                let resolved = self.sub.apply(ty);
                if resolved == *ty {
                    // Unresolved var -- check if it was the trait param
                    // We stored it during register_trait_def via convert_type_expr
                    // The TraitInfo.methods have raw type vars from that conversion.
                    // We need to check if this var id was assigned to param_name.
                    // For simplicity, just replace all free vars (trait methods only
                    // have the one type param).
                    replacement.clone()
                } else {
                    resolved
                }
            }
            Type::Arrow(a, b) => Type::Arrow(
                Box::new(self.substitute_trait_param(param_name, replacement, a)),
                Box::new(self.substitute_trait_param(param_name, replacement, b)),
            ),
            Type::Con(name, args) => Type::Con(
                name.clone(),
                args.iter()
                    .map(|a| self.substitute_trait_param(param_name, replacement, a))
                    .collect(),
            ),
            _ => ty.clone(),
        }
    }

    // --- Trait & impl registration ---

    fn register_trait_def(
        &mut self,
        name: &str,
        type_param: &str,
        supertraits: &[String],
        methods: &[ast::TraitMethod],
    ) -> Result<(), TypeError> {
        let mut method_sigs = Vec::new();

        for method in methods {
            let mut params_list: Vec<(String, u32)> = vec![];
            let param_types: Vec<Type> = method
                .params
                .iter()
                .map(|(_, texpr)| self.convert_type_expr(texpr, &mut params_list))
                .collect();
            let return_type = self.convert_type_expr(&method.return_type, &mut params_list);
            method_sigs.push((method.name.clone(), param_types, return_type));
        }

        // Add each method to the env as a polymorphic function.
        // e.g. `fun show (x: a) -> String` becomes `show : forall a. a -> String`
        for (method_name, param_types, return_type) in &method_sigs {
            let mut fun_ty = return_type.clone();
            for pt in param_types.iter().rev() {
                fun_ty = Type::Arrow(Box::new(pt.clone()), Box::new(fun_ty));
            }
            let mut forall = Vec::new();
            super::collect_free_vars(&fun_ty, &mut forall);
            self.env.insert(
                method_name.clone(),
                super::Scheme {
                    forall,
                    ty: fun_ty,
                },
            );
        }

        self.traits.insert(
            name.into(),
            super::TraitInfo {
                type_param: type_param.into(),
                supertraits: supertraits.to_vec(),
                methods: method_sigs,
            },
        );
        Ok(())
    }

    fn register_impl(
        &mut self,
        trait_name: &str,
        target_type: &str,
        methods: &[(String, Vec<ast::Pat>, ast::Expr)],
        span: crate::token::Span,
    ) -> Result<(), TypeError> {
        // Check the trait exists
        let trait_info = self.traits.get(trait_name).cloned().ok_or_else(|| {
            TypeError::at(span, format!("impl for undefined trait: {}", trait_name))
        })?;

        // Check all required methods are provided
        let provided: Vec<&str> = methods.iter().map(|(n, _, _)| n.as_str()).collect();
        for (required_name, _, _) in &trait_info.methods {
            if !provided.contains(&required_name.as_str()) {
                return Err(TypeError::at(
                    span,
                    format!(
                        "impl {} for {} is missing method '{}'",
                        trait_name, target_type, required_name
                    ),
                ));
            }
        }

        // Check for extra methods not in the trait
        for name in &provided {
            if !trait_info.methods.iter().any(|(n, _, _)| n == name) {
                return Err(TypeError::at(
                    span,
                    format!(
                        "impl {} for {} has method '{}' not defined in trait",
                        trait_name, target_type, name
                    ),
                ));
            }
        }

        // Type-check each method body against the trait's expected signature.
        // Substitute the trait's type param with the concrete target type.
        for (method_name, params, body) in methods {
            let trait_method = trait_info
                .methods
                .iter()
                .find(|(n, _, _)| n == method_name)
                .unwrap(); // already validated above

            // Build expected param types with trait type param replaced by target_type
            let target = Type::Con(target_type.into(), vec![]);
            let expected_params: Vec<Type> = trait_method
                .1
                .iter()
                .map(|t| self.substitute_trait_param(&trait_info.type_param, &target, t))
                .collect();
            let expected_return =
                self.substitute_trait_param(&trait_info.type_param, &target, &trait_method.2);

            let saved_env = self.env.clone();

            // Bind params with expected types
            for (i, pat) in params.iter().enumerate() {
                if i < expected_params.len() {
                    self.bind_pattern(pat, &expected_params[i])?;
                }
            }

            // Infer body and check it matches the expected return type
            let body_ty = self.infer_expr(body)?;
            self.unify_at(&body_ty, &expected_return, body.span()).map_err(|e| {
                TypeError::at(
                    span,
                    format!(
                        "in impl {} for {}, method '{}': {}",
                        trait_name, target_type, method_name, e.message
                    ),
                )
            })?;

            self.env = saved_env;
        }

        self.trait_impls.insert(
            (trait_name.into(), target_type.into()),
            super::ImplInfo {
                target_type: target_type.into(),
                methods: provided.iter().map(|s| s.to_string()).collect(),
            },
        );
        Ok(())
    }
}
