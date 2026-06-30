use std::collections::HashSet;

use crate::ast::{Annotated, BinOp, CaseArm, Decl, Expr, ExprKind, Lit, NodeId, Pat, Stmt};

use super::{Checker, Diagnostic, EffectRow, Scheme, Type};
use crate::token::Span;

fn collect_app_spine<'a>(
    expr: &'a Expr,
    args: &mut Vec<&'a Expr>,
    apps: &mut Vec<&'a Expr>,
) -> &'a Expr {
    match &expr.kind {
        ExprKind::App { func, arg } => {
            let head = collect_app_spine(func, args, apps);
            args.push(arg);
            apps.push(expr);
            head
        }
        _ => expr,
    }
}

/// If `expr` is a desugared list literal (a right-nested `Cons` spine
/// terminated by `Nil`), returns the element expressions in source order.
/// Otherwise returns `None`. Surface `[a, b, c]` desugars to
/// `Cons a (Cons b (Cons c Nil))` before typechecking; the empty list `[]`
/// desugars directly to a bare `Nil` constructor (no `App` wrapper) so it
/// never reaches the application chain. A hand-written `Cons x rest` where
/// `rest` is not itself a literal spine returns `None` and is processed by
/// the regular pairwise inference path.
fn collect_list_literal_elements(expr: &Expr) -> Option<Vec<&Expr>> {
    let mut elements = Vec::new();
    let mut current = expr;
    loop {
        let ExprKind::App {
            func: outer,
            arg: tail,
        } = &current.kind
        else {
            return None;
        };
        let ExprKind::App {
            func: inner,
            arg: elem,
        } = &outer.kind
        else {
            return None;
        };
        let ExprKind::Constructor { name, .. } = &inner.kind else {
            return None;
        };
        if name != "Cons" {
            return None;
        }
        elements.push(elem.as_ref());
        match &tail.kind {
            ExprKind::Constructor {
                name: tail_name, ..
            } if tail_name == "Nil" => {
                return Some(elements);
            }
            ExprKind::App { .. } => {
                current = tail.as_ref();
            }
            _ => return None,
        }
    }
}

impl Checker {
    /// When a bare `Var` lookup fails, probe `scope_map.trait_methods` with
    /// the same tier-based shadowing rule the resolver uses. Locally defined
    /// traits (canonical name prefixed by `current_module`) take precedence;
    /// imports are consulted only when no local trait contributes the name.
    /// Within the chosen tier, exactly one candidate is unambiguous and the
    /// resolver would have routed it via the canonical env entry — if we got
    /// here it means the chosen tier has >1 candidates, so emit an
    /// ambiguous-method diagnostic listing them. Returns None when neither
    /// tier contributes (the caller falls back to "undefined variable").
    fn bare_trait_method_ambiguity_diag(
        &self,
        method_name: &str,
        span: Span,
    ) -> Option<Diagnostic> {
        let candidates = self.scope_map.trait_methods.get(method_name)?;
        let local_prefix = self.current_module.as_deref().map(|m| format!("{}.", m));
        let (locals, imports): (Vec<&String>, Vec<&String>) = candidates
            .iter()
            .partition(|c| local_prefix.as_deref().is_some_and(|p| c.starts_with(p)));
        let chosen = if !locals.is_empty() { locals } else { imports };
        if chosen.len() < 2 {
            return None;
        }
        let mut names: Vec<String> = chosen.into_iter().cloned().collect();
        names.sort();
        let display = names.join(", ");
        Some(Diagnostic::error_at(
            span,
            format!(
                "ambiguous trait method '{}': found in [{}]; qualify the call (e.g. `{}.{}`)",
                method_name, display, names[0], method_name
            ),
        ))
    }

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
                let resolved_name = self.resolved_value_name(node_id, name);
                let env_lookup = self.env.get(&resolved_name);
                if let Some(scheme) = env_lookup {
                    let scheme = scheme.clone();
                    // Propagate effect type params from callee's annotations.
                    let effect_key = if self
                        .effect_meta
                        .fun_type_constraints
                        .contains_key(&resolved_name)
                    {
                        resolved_name.clone()
                    } else {
                        name.clone()
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
                    let def_id = self.env.def_id(&resolved_name);
                    if let Some(def_id) = def_id {
                        self.record_reference(node_id, span, def_id);
                    }
                    Ok(ty)
                } else if let Some(diag) = self.bare_trait_method_ambiguity_diag(name, span) {
                    Err(diag)
                } else {
                    Err(Diagnostic::error_at(
                        span,
                        format!("undefined variable: {}", name),
                    ))
                }
            }

            ExprKind::Constructor { name, .. } => {
                let resolved_ctor = self.resolved_constructor_name(node_id, name);
                let ctor_lookup = self.constructors.get(&resolved_ctor);
                if let Some(scheme) = ctor_lookup {
                    let scheme = scheme.clone();
                    let (ty, _) = self.instantiate(&scheme);
                    self.record_type(node_id, &ty);
                    let def_id = self.lsp.constructor_def_ids.get(&resolved_ctor).copied();
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

            ExprKind::App { .. } => self.infer_app_chain_with_expected(expr, None),

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
                // Join rather than pairwise unify so the two branches'
                // effect rows (when both are function-valued) union into
                // a single row variable instead of pinning to one side.
                // For non-function types `join_branch_types` falls back to
                // plain unification.
                self.join_branch_types(&[then_ty, else_ty], span)
            }

            ExprKind::Block { stmts, .. } => self.infer_block(stmts),

            ExprKind::Lambda { params, body, .. } => {
                let ty = self.infer_lambda(params, body)?;
                self.record_type(node_id, &ty);
                Ok(ty)
            }

            ExprKind::Case {
                scrutinee, arms, ..
            } => {
                let scrut_ty = self.infer_expr(scrutinee)?;
                let mut arm_tys: Vec<Type> = Vec::with_capacity(arms.len());

                for arm in arms {
                    let arm = &arm.node;
                    let saved_env = self.env.clone();
                    self.bind_pattern(&arm.pattern, &scrut_ty)?;

                    if let Some(guard) = &arm.guard {
                        self.check_guard(guard)?;
                    }

                    let body_ty = self.infer_expr(&arm.body)?;
                    arm_tys.push(body_ty);
                    self.env = saved_env;
                }

                // Join arm body types: when arms return function values
                // with heterogeneous effect rows, the result type's row
                // is the union rather than being pinned to the first arm.
                // For non-function bodies this degrades to pairwise unify.
                let result_ty = self.join_branch_types(&arm_tys, span)?;

                self.check_exhaustiveness(arms, &scrut_ty, span)?;
                Ok(result_ty)
            }

            ExprKind::RecordCreate { name, fields, .. } => {
                let resolved_name = self.resolved_record_type_name(node_id, name);
                let ty = self.infer_record_create(&resolved_name, fields, span)?;
                // Pin the node's record type so a field access directly on the
                // literal (`Rec { ... }.f`) can resolve its record name during
                // elaboration. Without this the field-access lowering can only
                // resolve the field index for fully-constant literals that the
                // optimizer folds away before lowering.
                self.record_type(node_id, &ty);
                Ok(ty)
            }

            ExprKind::AnonRecordCreate { fields, .. } => {
                let ty = self.infer_anon_record_create(fields)?;
                self.record_type(node_id, &ty);
                Ok(ty)
            }

            ExprKind::RecordBuild { record, fields, .. } => {
                self.infer_record_build(node_id, record.as_deref(), fields, span)
            }

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
                let resolved_effect_op = self.resolution.effect_call(node_id).cloned();
                let resolved_qualifier = self
                    .resolution
                    .effect_call(node_id)
                    .map(|resolved| resolved.effect.as_str())
                    .or(qualifier.as_deref())
                    .map(|s| s.to_string());
                let op_sig = self.lookup_effect_op(name, resolved_qualifier.as_deref(), span)?;
                for (trait_name, var_id, extra_types) in &op_sig.constraints {
                    self.trait_state.pending_constraints.push((
                        trait_name.clone(),
                        extra_types.clone(),
                        Type::Var(*var_id),
                        span,
                        node_id,
                    ));
                }

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
                for (i, (_, param_ty)) in op_sig.params.iter().rev().enumerate() {
                    let row = if i == op_sig.params.len() - 1 {
                        // Outermost arrow carries the needs
                        needs_row.clone()
                    } else {
                        EffectRow::empty()
                    };
                    ty = Type::Fun(Box::new(param_ty.clone()), Box::new(ty), row);
                }
                // Emit the effect onto the accumulator.
                if let Some(effect_name) = resolved_effect_op
                    .map(|resolved| resolved.effect)
                    .or_else(|| self.effect_for_op(name, resolved_qualifier.as_deref()))
                {
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

            ExprKind::QualifiedName { module, name, .. } => {
                if name.is_empty() {
                    return Ok(self.fresh_var());
                }
                let key = self.resolved_value_name(node_id, &format!("{}.{}", module, name));
                match self.env.get(&key).cloned() {
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
                        let def_id = self.env.def_id(&key);
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
                // The handler's `needs {X}` declares effects its arm bodies
                // perform at runtime. Those handlers must be captured at the
                // construction site; i.e. the surrounding scope must have
                // them in scope so its evidence carries them. Emit them to
                // the current effect row so the enclosing function declares
                // (or handles) them. Without this, a handler factory like
                // `make_inner () = handler for Inner needs {Outer} { ... }`
                // would typecheck silently and the lowerer would later ICE
                // because Outer isn't in the construction site's evidence.
                let needs = self
                    .handlers
                    .get(&synthetic_name)
                    .map(|info| info.needs_effects.clone())
                    .unwrap_or_else(super::EffectRow::empty);
                if !needs.effects.is_empty() {
                    self.emit_effects(&needs);
                }
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
            | ExprKind::DictSuperAccess { .. }
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

        // SPIKE: a closure is a value — defining it performs nothing. Its
        // effects live in the arrow type above and are realized only when it is
        // applied. (Was: self.emit_effects(&body_effs), which leaked them.)
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

        // SPIKE: see infer_lambda — closures don't perform effects at definition.
        Ok(Some(ty))
    }

    fn infer_app_chain_with_expected(
        &mut self,
        expr: &Expr,
        expected_result: Option<&Type>,
    ) -> Result<Type, Diagnostic> {
        // Desugared list literals (`Cons e1 (Cons e2 ... Nil)`) need row
        // widening across elements: a list of heterogeneous-effect functions
        // should produce `List (T needs {union of element rows})`, not pin
        // the row to the first element. Detect the spine here and route
        // through a join-aware path; everything else falls through to the
        // existing pairwise unification chain.
        if let Some(elements) = collect_list_literal_elements(expr) {
            return self.infer_list_literal_spine(expr, &elements, expected_result);
        }

        #[derive(Clone)]
        struct DeferredLambda<'a> {
            arg_expr: &'a Expr,
            params: &'a [Pat],
            body: &'a Expr,
            param_ty: Type,
        }

        let mut args = Vec::new();
        let mut apps = Vec::new();
        let head = collect_app_spine(expr, &mut args, &mut apps);
        let mut current_ty = self.infer_expr(head)?;
        let mut deferred = Vec::<DeferredLambda<'_>>::new();

        // Effects performed by the saturated call must be emitted *after* every
        // deferred lambda argument has been inferred: a deferred lambda binds the
        // HOF's open effect row (`..e`), and that binding isn't visible until its
        // body is checked below. Emitting at the saturating arg inside this loop
        // would read an unbound row and silently drop the callback's effects
        // (e.g. `flat_map (fun x -> risky x) xs` where the list is the saturating
        // arg). So we record the callee type at the saturation point and the
        // absorbed entries from *all* callback args, then emit once at the end.
        let mut saturation_callee: Option<Type> = None;
        let mut absorbed_entries = Vec::<super::EffectEntry>::new();

        for (idx, (arg, app_expr)) in args.iter().zip(apps.iter()).enumerate() {
            let callee_ty = current_ty.clone();
            let (param_ty, ret_ty) =
                self.expect_function_type_for_app(&callee_ty, app_expr.span, app_expr)?;
            let resolved_param = self.sub.apply(&param_ty);
            let is_last = idx + 1 == args.len();
            let saturates = is_last && !matches!(self.sub.apply(&ret_ty), Type::Fun(_, _, _));

            if let ExprKind::Lambda { params, body } = &arg.kind
                && matches!(resolved_param, Type::Fun(_, _, _))
            {
                deferred.push(DeferredLambda {
                    arg_expr: arg,
                    params,
                    body,
                    param_ty: param_ty.clone(),
                });
                self.record_type(app_expr.id, &ret_ty);
                current_ty = ret_ty;
                if saturates {
                    saturation_callee = Some(callee_ty);
                }
                continue;
            }

            let arg_ty = self.infer_arg_against(arg, &param_ty)?;
            let arg_ty_pre = arg_ty.clone();
            self.unify_arg_with_param(&arg_ty, &arg_ty_pre, &param_ty, arg.span)?;
            absorbed_entries.extend(self.apply_callback_argument_effects(
                &arg_ty_pre,
                &param_ty,
                arg.span,
            )?);
            self.record_type(app_expr.id, &ret_ty);
            current_ty = ret_ty.clone();

            if saturates {
                saturation_callee = Some(callee_ty);
            }
        }

        if let Some(expected_result) = expected_result {
            self.unify_at(&current_ty, expected_result, expr.span)?;
        }

        for deferred_lambda in deferred {
            let expected_param = self.sub.apply(&deferred_lambda.param_ty);
            let arg_ty = match self.infer_lambda_against(
                deferred_lambda.params,
                deferred_lambda.body,
                &expected_param,
            )? {
                Some(ty) => ty,
                None => self.infer_expr(deferred_lambda.arg_expr)?,
            };
            let arg_ty_pre = arg_ty.clone();
            self.unify_arg_with_param(
                &arg_ty,
                &arg_ty_pre,
                &deferred_lambda.param_ty,
                deferred_lambda.arg_expr.span,
            )?;
            absorbed_entries.extend(self.apply_callback_argument_effects(
                &arg_ty_pre,
                &deferred_lambda.param_ty,
                deferred_lambda.arg_expr.span,
            )?);
        }

        // Now that deferred lambdas have bound any open effect rows, emit the
        // saturated call's effects (callee row minus everything absorbed).
        if let Some(callee_ty) = saturation_callee {
            self.emit_saturated_call_effects(&callee_ty, &absorbed_entries);
            self.emit_concrete_trait_impl_effects(head);
        }

        Ok(current_ty)
    }

    /// Infer a desugared list literal spine `Cons e1 (Cons e2 ... Nil)`
    /// using the row-joining path. Element types are joined via
    /// `join_branch_types`, which widens effect rows across heterogeneous
    /// elements (the whole point of this code path). The resulting `List`
    /// type is then unified against the expected result, if any.
    ///
    /// Records types for each `App` and constructor node in the spine so
    /// LSP type-at-span / hover queries still find them, and threads the
    /// joined element type back to each `Cons` instantiation so trait
    /// constraints and type-arg unifications come out consistent.
    ///
    /// Absorbs effects declared on the joined element type, mirroring the
    /// call-site half of HOF absorption that the pairwise Cons chain
    /// performs via `apply_callback_argument_effects` at each element.
    /// Without this, effects emitted by element-defining lambdas (which
    /// propagate to the enclosing scope on lambda inference) would leak
    /// into the enclosing function's body effect row.
    fn infer_list_literal_spine(
        &mut self,
        expr: &Expr,
        elements: &[&Expr],
        expected_result: Option<&Type>,
    ) -> Result<Type, Diagnostic> {
        let mut elem_tys: Vec<Type> = Vec::with_capacity(elements.len());
        for elem in elements {
            elem_tys.push(self.infer_expr(elem)?);
        }

        let joined_elem = self.join_branch_types(&elem_tys, expr.span)?;

        // SPIKE: no element-effect absorption (closures no longer leak at
        // definition, so list elements that are effectful closures contribute
        // nothing to the ambient row just by being listed).

        let list_ty = Type::Con(
            super::canonicalize_type_name("List").into(),
            vec![joined_elem.clone()],
        );
        // Type of a partially-applied Cons after its first arg:
        // `List joined -> List joined`. The result is always pure.
        let cons_partial_ty = Type::Fun(
            Box::new(list_ty.clone()),
            Box::new(list_ty.clone()),
            EffectRow::empty(),
        );
        // Type of a fully-instantiated Cons: `joined -> List joined -> List joined`.
        let cons_full_ty = Type::Fun(
            Box::new(joined_elem.clone()),
            Box::new(cons_partial_ty.clone()),
            EffectRow::empty(),
        );

        let mut current = expr;
        loop {
            let ExprKind::App {
                func: outer,
                arg: tail,
            } = &current.kind
            else {
                break;
            };
            let ExprKind::App { func: inner, .. } = &outer.kind else {
                break;
            };
            // Infer the Cons constructor for its LSP side effects (references,
            // type recording on the constructor node), then constrain it to
            // the joined Cons shape.
            let cons_ty = self.infer_expr(inner)?;
            self.unify_at(&cons_ty, &cons_full_ty, inner.span)?;
            self.record_type(outer.id, &cons_partial_ty);
            self.record_type(current.id, &list_ty);

            match &tail.kind {
                ExprKind::Constructor { .. } => {
                    // Nil terminator: must have type `List joined`.
                    let nil_ty = self.infer_expr(tail)?;
                    self.unify_at(&nil_ty, &list_ty, tail.span)?;
                    break;
                }
                ExprKind::App { .. } => {
                    current = tail.as_ref();
                }
                _ => break,
            }
        }

        if let Some(expected) = expected_result {
            self.unify_at(&list_ty, expected, expr.span)?;
        }

        Ok(list_ty)
    }

    pub(crate) fn infer_expr_against(
        &mut self,
        expr: &Expr,
        expected: &Type,
    ) -> Result<Type, Diagnostic> {
        match &expr.kind {
            ExprKind::App { .. } => self.infer_app_chain_with_expected(expr, Some(expected)),
            ExprKind::Lambda { params, body } => {
                let resolved_expected = self.sub.apply(expected);
                if matches!(resolved_expected, Type::Fun(_, _, _))
                    && let Some(ty) = self.infer_lambda_against(params, body, &resolved_expected)?
                {
                    self.record_type(expr.id, &ty);
                    return Ok(ty);
                }
                let ty = self.infer_expr(expr)?;
                self.unify_at(&ty, expected, expr.span)?;
                Ok(ty)
            }
            _ => {
                let ty = self.infer_expr(expr)?;
                self.unify_at(&ty, expected, expr.span)?;
                Ok(ty)
            }
        }
    }

    fn infer_arg_against(&mut self, arg: &Expr, expected_param: &Type) -> Result<Type, Diagnostic> {
        match &arg.kind {
            ExprKind::Lambda { params, body } => {
                let resolved_param = self.sub.apply(expected_param);
                if matches!(resolved_param, Type::Fun(_, _, _)) {
                    match self.infer_lambda_against(params, body, &resolved_param)? {
                        Some(ty) => {
                            self.record_type(arg.id, &ty);
                            Ok(ty)
                        }
                        None => self.infer_expr(arg),
                    }
                } else {
                    self.infer_expr(arg)
                }
            }
            // For tuples and anonymous records passed to a function whose
            // parameter type carries row variables shared across multiple
            // positions, pre-widen those shared variables to the union of
            // the actual element rows. Without this, pairwise unification
            // pins the shared var to the first element's row and rejects
            // the rest. Falls back to normal inference when the expected
            // shape doesn't match.
            ExprKind::Tuple { elements, .. } => {
                if let Some(ty) =
                    self.try_infer_tuple_against(elements, expected_param, arg.span)?
                {
                    self.record_type(arg.id, &ty);
                    Ok(ty)
                } else {
                    self.infer_expr(arg)
                }
            }
            ExprKind::AnonRecordCreate { fields, .. } => {
                if let Some(ty) =
                    self.try_infer_anon_record_against(fields, expected_param, arg.span)?
                {
                    self.record_type(arg.id, &ty);
                    Ok(ty)
                } else {
                    self.infer_expr(arg)
                }
            }
            _ => self.infer_expr(arg),
        }
    }

    /// Tuple inference against an expected tuple type, with shared-row-var
    /// pre-widening. Returns `None` when the expected isn't a tuple of
    /// matching arity (caller falls back to plain `infer_expr`).
    fn try_infer_tuple_against(
        &mut self,
        elements: &[Expr],
        expected: &Type,
        span: Span,
    ) -> Result<Option<Type>, Diagnostic> {
        let resolved = self.sub.apply(expected);
        let Type::Con(name, expected_elem_tys) = &resolved else {
            return Ok(None);
        };
        if super::bare_type_name(name) != "Tuple" || expected_elem_tys.len() != elements.len() {
            return Ok(None);
        }

        let mut actual_tys: Vec<Type> = Vec::with_capacity(elements.len());
        for elem in elements {
            actual_tys.push(self.infer_expr(elem)?);
        }
        self.prewiden_shared_rows(&actual_tys, expected_elem_tys, span)?;
        Ok(Some(Type::Con(
            super::canonicalize_type_name("Tuple").into(),
            actual_tys,
        )))
    }

    /// Anonymous-record inference against an expected anonymous-record
    /// type, with shared-row-var pre-widening. Returns `None` when the
    /// expected isn't a matching `Type::Record` or fields don't line up
    /// (caller falls back to plain `infer_expr`).
    ///
    /// Anonymous record types use sorted-by-name field order canonically;
    /// element positions are taken from the expected type's order.
    fn try_infer_anon_record_against(
        &mut self,
        fields: &[(String, Span, Expr)],
        expected: &Type,
        span: Span,
    ) -> Result<Option<Type>, Diagnostic> {
        let resolved = self.sub.apply(expected);
        let Type::Record(expected_fields) = &resolved else {
            return Ok(None);
        };
        if expected_fields.len() != fields.len() {
            return Ok(None);
        }

        // Index actual fields by name for positional matching.
        let field_map: std::collections::HashMap<&str, &Expr> = fields
            .iter()
            .map(|(name, _, expr)| (name.as_str(), expr))
            .collect();

        let mut actual_tys: Vec<Type> = Vec::with_capacity(expected_fields.len());
        let mut expected_pos_tys: Vec<Type> = Vec::with_capacity(expected_fields.len());
        for (fname, expected_ty) in expected_fields {
            let Some(fexpr) = field_map.get(fname.as_str()) else {
                return Ok(None);
            };
            actual_tys.push(self.infer_expr(fexpr)?);
            expected_pos_tys.push(expected_ty.clone());
        }
        self.prewiden_shared_rows(&actual_tys, &expected_pos_tys, span)?;

        let typed_fields: Vec<(String, Type)> = expected_fields
            .iter()
            .map(|(n, _)| n.clone())
            .zip(actual_tys)
            .collect();
        Ok(Some(Type::Record(typed_fields)))
    }

    fn expect_function_type_for_app(
        &mut self,
        callee_ty: &Type,
        span: Span,
        app_expr: &Expr,
    ) -> Result<(Type, Type), Diagnostic> {
        let resolved = self.sub.apply(callee_ty);
        match resolved {
            Type::Fun(param_ty, ret_ty, _) => Ok((*param_ty, *ret_ty)),
            _ => {
                let param_ty = self.fresh_var();
                let ret_ty = self.fresh_var();
                let eff_row_var = self.fresh_var();
                if self
                    .unify_at(
                        callee_ty,
                        &Type::Fun(
                            Box::new(param_ty.clone()),
                            Box::new(ret_ty.clone()),
                            EffectRow {
                                effects: vec![],
                                tails: vec![eff_row_var],
                            },
                        ),
                        span,
                    )
                    .is_err()
                {
                    let resolved = self.sub.apply(callee_ty);
                    let display = self.prettify_type(&resolved);
                    let func_span = match &app_expr.kind {
                        ExprKind::App { func, .. } => func.span,
                        _ => span,
                    };
                    return Err(Diagnostic::error_at(
                        func_span,
                        format!("{} is not a function", display),
                    ));
                }
                Ok((param_ty, ret_ty))
            }
        }
    }

    fn unify_arg_with_param(
        &mut self,
        arg_ty: &Type,
        arg_ty_pre: &Type,
        param_ty: &Type,
        arg_span: Span,
    ) -> Result<(), Diagnostic> {
        if let Err(orig) = self.unify_at(arg_ty, param_ty, arg_span) {
            // Preserve specific, actionable row-ambiguity errors (e.g. an
            // argument forcing a named effect into one of several open tails)
            // rather than collapsing them into a generic type mismatch.
            if orig.message.contains("ambiguous effect row") {
                return Err(orig);
            }
            return Err(Diagnostic::error_at(
                arg_span,
                self.format_type_mismatch(&self.sub.apply(param_ty), arg_ty_pre),
            ));
        }
        Ok(())
    }

    fn apply_callback_argument_effects(
        &mut self,
        actual_arg: &Type,
        expected_param: &Type,
        arg_span: Span,
    ) -> Result<Vec<super::EffectEntry>, Diagnostic> {
        let resolved_param = self.sub.apply(expected_param);
        if let Type::Fun(_, _, _) = &resolved_param {
            self.check_callback_effect_subtype(actual_arg, &resolved_param, arg_span)?;
        }

        // Closures no longer leak their effects at definition, so there is
        // nothing to subtract from the *caller's* row. The one adjustment still
        // required is to the HOF's *result* row: a HOF that names a concrete
        // effect on both its callback parameter and its result (e.g.
        // `run_forward : (Unit -> a needs {E,..e}) -> a needs {E,..e}`) only
        // performs that effect by *running the callback*. If the actual lambda
        // handled `E` internally (at a `with` inside the lambda), the HOF never
        // performs `E` for this call, so `E` must be removed from the result
        // row emitted at the saturated call site.
        //
        // Absorbed = effects the callback parameter is *declared* to accept
        // minus effects the *actual* lambda still performs. Effects the lambda
        // genuinely performs flow through the result row untouched; the caller's
        // own direct uses of the same effect are never touched (we don't subtract
        // from `effect_row`).
        let declared = self.arrow_effect_entries(self.sub.resolve_var(expected_param));
        let actual = self.arrow_effect_entries(self.sub.resolve_var(actual_arg));
        let absorbed: Vec<super::EffectEntry> = declared
            .into_iter()
            .filter(|d| !actual.iter().any(|a| a.same_instantiation(d)))
            .collect();
        Ok(absorbed)
    }

    /// Collect the effect entries on every arrow along a function type's spine
    /// (deduped by instantiation). Empty for non-function types.
    fn arrow_effect_entries(&self, ty: &Type) -> Vec<super::EffectEntry> {
        let mut out: Vec<super::EffectEntry> = Vec::new();
        let mut t = self.sub.apply(ty);
        while let Type::Fun(_, ret, row) = t {
            for entry in &row.effects {
                let applied = super::EffectEntry {
                    name: entry.name.clone(),
                    args: entry.args.iter().map(|arg| self.sub.apply(arg)).collect(),
                };
                if !out.iter().any(|seen| seen.same_instantiation(&applied)) {
                    out.push(applied);
                }
            }
            t = self.sub.apply(&ret);
        }
        out
    }

    fn emit_saturated_call_effects(
        &mut self,
        callee_ty: &Type,
        absorbed_entries: &[super::EffectEntry],
    ) {
        let resolved_func = self.sub.apply(callee_ty);
        if let Type::Fun(_, _, row) = &resolved_func {
            let applied_row = self.sub.apply_effect_row(row);
            let emitted_row = applied_row.subtract_entries(absorbed_entries);
            self.emit_effects(&emitted_row);
        }
    }

    /// Trait-effect propagation (the bugfix): when a saturated call's head
    /// carries trait constraints whose self type has resolved to a concrete
    /// `Type::Con`, emit the selected impl's effects into the caller's row.
    ///
    /// Without this, effects declared on an impl are checked locally against the
    /// method body but never reach the caller — a concrete `foo 42` whose `Foo
    /// Int` impl needs `Config` would type-check as pure, then hit an unhandled
    /// effect at runtime. Emitting here (at the call site, during inference)
    /// routes through the normal accumulator, so `with` subtraction and the
    /// handler-necessity check see it.
    ///
    /// Per-method precision: if the head names a method of the constrained trait
    /// (a direct trait-method call), only that method's effects are emitted, so
    /// a pure sibling of an effectful impl stays pure. Otherwise (a where-bound
    /// function whose internal method use isn't visible from the signature yet),
    /// the union of the impl's method effects is emitted. The precise
    /// per-constraint row variable that would replace the union is Phase B
    /// (see docs/planning/effect-polymorphic-traits.md).
    fn emit_concrete_trait_impl_effects(&mut self, head: &Expr) {
        let head_id = head.id;
        // Bare method name from the head, for per-method precision on direct
        // trait-method calls (`foo 42` → "foo").
        let head_method: Option<String> = match &head.kind {
            ExprKind::Var { name, .. } => Some(name.rsplit('.').next().unwrap_or(name).to_string()),
            _ => None,
        };
        // Constraints recorded for this call head (cloned to drop the borrow).
        let constraints: Vec<(String, Type)> = self
            .trait_state
            .pending_constraints
            .iter()
            .filter(|(_, _, _, _, nid)| *nid == head_id)
            .map(|(trait_name, _extra, self_ty, _, _)| (trait_name.clone(), self_ty.clone()))
            .collect();
        for (trait_name, self_ty) in constraints {
            let resolved = self.sub.apply(&self_ty);
            // Abstract self (a where-bound type variable): the impl's concrete
            // effects are unknowable here. For an *open-row* trait method, surface
            // the constraint's effects as the row variable `..a` (the type var's
            // own id) and require the enclosing function to forward it. This is
            // the open-row analog of the concrete-discharge case below; closed and
            // pure trait methods propagate (or don't) through the normal type row,
            // so they are left untouched. See
            // docs/planning/effect-polymorphic-traits.md.
            if let Type::Var(var_id) = &resolved {
                if self.trait_call_forwards_open_row(&trait_name, head_method.as_deref()) {
                    let tail = Type::Var(*var_id);
                    if !self.effect_row.tails.iter().any(|t| t == &tail) {
                        self.effect_row.tails.push(tail);
                    }
                    self.trait_forward_row_vars
                        .entry(*var_id)
                        .or_insert_with(|| trait_name.clone());
                }
                continue;
            }
            let Type::Con(type_name, args) = &resolved else {
                continue;
            };
            // Single-param trait lookup: arity-keyed target first (tuples),
            // then the bare canonical name. Multi-param traits (non-empty
            // trait_type_args) are not handled here yet.
            let arity_key = super::arity_keyed_target_name(type_name, args.len());
            let info = self
                .trait_state
                .impls
                .get(&(trait_name.clone(), vec![], arity_key))
                .or_else(|| {
                    self.trait_state
                        .impls
                        .get(&(trait_name.clone(), vec![], type_name.clone()))
                })
                .cloned();
            let Some(info) = info else {
                continue;
            };
            if info.method_effects.is_empty() {
                continue;
            }
            // Only *open-row* trait methods need concrete discharge. Their
            // effects are NOT in the method's declared type, so the normal
            // row-tracking never sees them and an enclosing `with` cannot
            // subtract them -- concrete discharge is what surfaces them at the
            // concrete call site. A closed-named method (`to_json : a -> Json
            // needs {JsonOptions}`) already carries its effect in the type: it
            // propagates -- and gets subtracted by an enclosing handler --
            // through the normal path. Re-emitting it here would resurrect an
            // effect the callee already handled (e.g. `serialize x =
            // serialize_with x with json_defaults`, where `serialize` is pure
            // but PersonD's `ToJson` impl performs `JsonOptions`).
            let open_row_methods: std::collections::HashSet<&str> = self
                .trait_state
                .traits
                .get(&trait_name)
                .map(|t| {
                    t.methods
                        .iter()
                        .filter(|m| m.effect_sig.is_open_row)
                        .map(|m| m.name.as_str())
                        .collect()
                })
                .unwrap_or_default();
            if open_row_methods.is_empty() {
                continue;
            }
            let names: Vec<String> = match &head_method {
                // Direct trait-method call: discharge only if THAT method is
                // open-row (a pure/closed sibling of an open-row method stays on
                // the normal path).
                Some(m) if info.method_effects.contains_key(m) => {
                    if open_row_methods.contains(m.as_str()) {
                        info.method_effects.get(m).cloned().unwrap_or_default()
                    } else {
                        continue;
                    }
                }
                // Where-bound function call (`count_foos 42`): union the effects
                // of the trait's open-row methods only.
                _ => {
                    let mut set: std::collections::BTreeSet<String> =
                        std::collections::BTreeSet::new();
                    for (mname, effs) in &info.method_effects {
                        if open_row_methods.contains(mname.as_str()) {
                            set.extend(effs.iter().cloned());
                        }
                    }
                    set.into_iter().collect()
                }
            };
            for name in names {
                self.emit_effect(name, vec![]);
            }
        }
    }

    /// Whether a call carrying a constraint on `trait_name` forwards an open
    /// effect row (`..a`) when its `self` is abstract. Per-method precision for
    /// direct trait-method calls: only the named method's open-row-ness counts,
    /// so a pure sibling of an open-row method does not force forwarding. For a
    /// where-bound function call (the head is not a trait method), fall back to
    /// the per-trait union: any open-row method in the trait forwards. A trait
    /// with no open-row method (e.g. `Show`/`Eq`) never forwards.
    fn trait_call_forwards_open_row(&self, trait_name: &str, head_method: Option<&str>) -> bool {
        let Some(info) = self.trait_state.traits.get(trait_name) else {
            return false;
        };
        match head_method {
            Some(m) if info.methods.iter().any(|tm| tm.name == m) => info
                .methods
                .iter()
                .any(|tm| tm.name == m && tm.effect_sig.is_open_row),
            _ => info.methods.iter().any(|tm| tm.effect_sig.is_open_row),
        }
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
                    tails: vec![],
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
                        // Also record under the pattern's NodeId in a persistent
                        // map so the lowerer can recover the info after the
                        // per-clause `handlers` save/restore wipes the entry.
                        if let Some(info) = self.extract_handler_info(value) {
                            self.handlers.insert(name.clone(), info.clone());
                            self.let_binding_handlers.insert(*pat_id, info);
                        } else if let Some(info) = self.handler_info_from_type(&ty) {
                            self.handlers.insert(name.clone(), info.clone());
                            self.let_binding_handlers.insert(*pat_id, info);
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

    /// Type-variable IDs held rigid by an enclosing `where`-bound (resolved
    /// through the substitution). A `let` binding must not generalize over a
    /// variable the surrounding function/handler holds fixed, so these are
    /// excluded from let-generalization.
    fn rigid_where_bound_vars(&self) -> std::collections::HashSet<u32> {
        let mut determined = std::collections::HashSet::new();
        for &bound_id in self.trait_state.where_bounds.keys() {
            if let Type::Var(resolved) = self.sub.apply(&Type::Var(bound_id)) {
                determined.insert(resolved);
            }
        }
        determined
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

        // A variable held rigid by an enclosing `where`-bound must not be
        // generalized: the surrounding function/handler holds it fixed, so
        // generalizing would hand each use of this binding a fresh variable.
        let rigid_vars = self.rigid_where_bound_vars();
        if !rigid_vars.is_empty() {
            scheme.forall.retain(|id| !rigid_vars.contains(id));
        }

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
                        resolved_record_type: None,
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

        let resolved_ty = self.sub.apply(ty);
        let effects: HashSet<String> = super::effects_from_type(&resolved_ty);
        self.env.insert_with_def(name.to_string(), scheme, pat_id);
        if has_deferred_effects && !effects.is_empty() {
            let mut sorted: Vec<String> = effects.into_iter().collect();
            sorted.sort();
            self.effect_meta
                .known_let_bindings
                .insert(name.to_string(), sorted);
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
            if actual_row.tails.is_empty() && expected_row.tails.is_empty() {
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
