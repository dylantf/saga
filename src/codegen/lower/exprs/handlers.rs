use crate::ast::{CaseArm, Expr, ExprKind, Pat};
use crate::codegen::cerl::{CArm, CExpr, CPat};
use crate::codegen::lower::util::*;
use crate::codegen::lower::*;
use crate::typechecker::Type;
use std::collections::HashSet;

type DynamicHandlerVarInfo = (String, Vec<String>, bool);
type SavedDynamicHandlerPatternVars = Vec<(String, Option<DynamicHandlerVarInfo>)>;

impl<'a> Lowerer<'a> {
    pub(crate) fn register_dynamic_handler_pattern_vars(
        &mut self,
        pat: &Pat,
    ) -> SavedDynamicHandlerPatternVars {
        let mut saved = Vec::new();
        self.register_dynamic_handler_pattern_vars_inner(pat, &mut saved);
        saved
    }

    fn register_dynamic_handler_pattern_vars_inner(
        &mut self,
        pat: &Pat,
        saved: &mut SavedDynamicHandlerPatternVars,
    ) {
        match pat {
            Pat::Var { id, name, .. } => {
                if let Some(ty) = self.semantic_type_at_node(*id)
                    && let Some(effects) = self.dynamic_handler_info_from_type(ty)
                {
                    let previous = self
                        .handle_dynamic_vars
                        .insert(name.clone(), (core_var(name), effects, false));
                    saved.push((name.clone(), previous));
                }
            }
            Pat::Tuple { elements, .. } => {
                for element in elements {
                    self.register_dynamic_handler_pattern_vars_inner(element, saved);
                }
            }
            Pat::Constructor { args, .. } => {
                for arg in args {
                    self.register_dynamic_handler_pattern_vars_inner(arg, saved);
                }
            }
            Pat::Record { fields, .. } | Pat::AnonRecord { fields, .. } => {
                for (_, field_pat) in fields {
                    if let Some(field_pat) = field_pat {
                        self.register_dynamic_handler_pattern_vars_inner(field_pat, saved);
                    }
                }
            }
            Pat::StringPrefix { rest, .. } => {
                self.register_dynamic_handler_pattern_vars_inner(rest, saved);
            }
            Pat::BitStringPat { segments, .. } => {
                for segment in segments {
                    self.register_dynamic_handler_pattern_vars_inner(&segment.value, saved);
                }
            }
            Pat::Or { patterns, .. } => {
                for pattern in patterns {
                    self.register_dynamic_handler_pattern_vars_inner(pattern, saved);
                }
            }
            Pat::Wildcard { .. } | Pat::Lit { .. } | Pat::ListPat { .. } | Pat::ConsPat { .. } => {}
        }
    }

    pub(crate) fn restore_dynamic_handler_pattern_vars(
        &mut self,
        saved: SavedDynamicHandlerPatternVars,
    ) {
        for (name, previous) in saved.into_iter().rev() {
            if let Some(previous) = previous {
                self.handle_dynamic_vars.insert(name, previous);
            } else {
                self.handle_dynamic_vars.remove(&name);
            }
        }
    }

    /// Bind each element to a fresh variable, then build a tuple.
    /// Used for both tuple literals and record/constructor field lists.
    /// Lower a `do { Pat <- expr ... success } else { arms }` expression.
    ///
    /// Desugars to nested case expressions: each binding is a case on the
    /// scrutinee; a successful pattern match continues to the next binding,
    /// a mismatch routes the raw value to the else arms.
    pub(crate) fn lower_do(
        &mut self,
        bindings: &[(Pat, Expr)],
        success: &Expr,
        else_arms: &[CaseArm],
    ) -> CExpr {
        // Pre-lower the else arms once; clone them at each failure point.
        let else_arms_ce: Vec<CArm> = else_arms
            .iter()
            .map(|arm| CArm {
                pat: self.lower_pat(
                    &arm.pattern,
                    &self.constructor_atoms,
                    self.handler_origin_module(),
                ),
                guard: arm.guard.as_ref().map(|g| self.lower_expr_value(g)),
                body: self.lower_expr(&arm.body),
            })
            .collect();

        // Build from the innermost binding outward.
        let mut inner = self.lower_expr(success);

        for (pat, expr) in bindings.iter().rev() {
            let scrut_var = self.fresh();
            let fail_var = self.fresh();
            let val_ce = self.lower_expr_value(expr);

            let success_pat =
                self.lower_pat(pat, &self.constructor_atoms, self.handler_origin_module());
            // If the success pattern is a catch-all (e.g. Just(x) lowers to a
            // bare variable), put the else arms first so they get a chance to
            // match before the catch-all swallows everything.
            let is_catchall = matches!(success_pat, CPat::Var(_));
            let success_arm = CArm {
                pat: success_pat,
                guard: None,
                body: inner,
            };
            let mut else_with_fallthrough: Vec<CArm> = else_arms_ce.clone();
            let has_catchall = else_with_fallthrough
                .iter()
                .any(|arm| arm.guard.is_none() && matches!(arm.pat, CPat::Var(_) | CPat::Wildcard));
            if !has_catchall {
                else_with_fallthrough.push(CArm {
                    pat: CPat::Var(fail_var.clone()),
                    guard: None,
                    body: CExpr::Var(fail_var),
                });
            }
            let fail_arm = CArm {
                pat: CPat::Var(self.fresh()),
                guard: None,
                body: CExpr::Case(
                    Box::new(CExpr::Var(scrut_var.clone())),
                    else_with_fallthrough,
                ),
            };
            let arms = if is_catchall {
                // Else arms first, then success as fallback
                let mut arms: Vec<CArm> = else_arms_ce
                    .iter()
                    .map(|arm| CArm {
                        pat: arm.pat.clone(),
                        guard: arm.guard.clone(),
                        body: arm.body.clone(),
                    })
                    .collect();
                arms.push(success_arm);
                arms
            } else {
                vec![success_arm, fail_arm]
            };
            let case_expr = CExpr::Case(Box::new(CExpr::Var(scrut_var.clone())), arms);
            inner = CExpr::Let(scrut_var, Box::new(val_ce), Box::new(case_expr));
        }

        inner
    }

    /// Check if an expression produces a handler value.
    pub(crate) fn is_handler_value(&self, expr: &Expr) -> bool {
        match &expr.kind {
            ExprKind::HandlerExpr { .. } => true,
            ExprKind::Var { name } => {
                self.known_handler_binding_name(expr.id, name)
                    .is_some_and(|resolved_name| {
                        self.check_result.handlers.contains_key(&resolved_name)
                            || self.handler_defs.contains_key(&resolved_name)
                            || self.handle_dynamic_vars.contains_key(&resolved_name)
                            || self.handle_cond_vars.contains_key(&resolved_name)
                    })
            }
            ExprKind::If {
                then_branch,
                else_branch,
                ..
            } => self.is_handler_value(then_branch) || self.is_handler_value(else_branch),
            _ => self.dynamic_handler_info_from_expr(expr).is_some(),
        }
    }

    pub(crate) fn lower_tuple_elems(&mut self, elems: &[Expr]) -> CExpr {
        let mut vars: Vec<String> = Vec::new();
        let mut bindings: Vec<(String, CExpr)> = Vec::new();
        for elem in elems {
            let var = self.fresh();
            let val = self.lower_expr_value(elem);
            vars.push(var.clone());
            bindings.push((var, val));
        }
        let tuple = CExpr::Tuple(vars.iter().map(|v| CExpr::Var(v.clone())).collect());
        bindings.into_iter().rev().fold(tuple, |body, (var, val)| {
            CExpr::Let(var, Box::new(val), Box::new(body))
        })
    }

    /// Lower a handle binding statement. Routes the binding into one of four
    /// metadata stores depending on the RHS shape; `lower_with` later picks
    /// the matching compilation strategy based on which store the name is in.
    ///
    /// Although evidence-wrapping itself only happens at the `with` boundary
    /// (see [`Self::lower_with`]), the four paths still need to remain
    /// distinct because each captures a different *source* of handler
    /// information:
    ///
    /// - **Static alias** (`Var`): compile-time resolved canonical name in
    ///   `handler_canonical`. The handler's arms are already in
    ///   `handler_defs` from registration.
    /// - **HandlerExpr**: arms are in the `value` expression itself; we
    ///   register them under a synthetic name in `handler_defs`.
    /// - **Conditional** (`If`): both branches resolve statically; we store
    ///   the lowered condition + both canonicals in `handle_cond_vars` so
    ///   `lower_with` can emit a runtime case-split.
    /// - **Dynamic**: arbitrary RHS; we store the value's effect signature
    ///   from the typechecker in `handle_dynamic_vars` so `lower_with` can
    ///   emit a closure-call dispatch.
    ///
    /// Collapsing the four paths into one would hide these distinct
    /// metadata flows behind a uniform interface without reducing branching
    /// at the `with` boundary.
    pub(crate) fn lower_handle_binding(
        &mut self,
        name: &str,
        pat_id: Option<crate::ast::NodeId>,
        value: &Expr,
    ) {
        self.handler_canonical.remove(name);
        self.handle_dynamic_vars.remove(name);
        self.handle_cond_vars.remove(name);

        // Direct handler reference: compile-time alias
        if let ExprKind::Var { name: handler_name } = &value.kind
            && let Some(canonical) = self.known_handler_binding_name(value.id, handler_name)
        {
            self.handler_canonical.insert(name.to_string(), canonical);
            return;
        }
        // Handler expression: register arms directly under synthetic name
        if let ExprKind::HandlerExpr { body } = &value.kind {
            let synthetic = format!("__handler_expr_{}", value.id.0);
            let semantic_module_name = self.current_semantic_module_name().to_string();
            let canonical_effects = self
                .semantic_type_at_node(value.id)
                .and_then(|ty| self.dynamic_handler_info_from_type(ty))
                .unwrap_or_else(|| {
                    self.resolved_effect_refs_for_module(&semantic_module_name, &body.effects)
                });
            self.handler_defs.insert(
                synthetic.clone(),
                crate::codegen::lower::HandlerInfo {
                    effects: canonical_effects,
                    arms: body.arms.iter().map(|a| a.node.clone()).collect(),
                    return_clause: body.return_clause.clone(),
                    source_module: None,
                    captures: Vec::new(),
                },
            );
            self.handler_canonical.insert(name.to_string(), synthetic);
            return;
        }
        if let Some(synthetic) = self.recover_handler_factory_binding(value) {
            self.handler_canonical.insert(name.to_string(), synthetic);
            return;
        }
        // Conditional: generate runtime dispatch
        if let ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } = &value.kind
        {
            let then_canonical = self.resolve_handle_value(then_branch);
            let else_canonical = self.resolve_handle_value(else_branch);

            if let (Some(then_c), Some(else_c)) = (then_canonical, else_canonical) {
                let cond_ce = self.lower_expr_value(cond);
                let cond_var = self.fresh();
                self.handle_cond_vars.insert(
                    name.to_string(),
                    (cond_var, cond_ce, then_c.clone(), else_c),
                );
                // Alias to then-branch for static resolution; conditional
                // dispatch is handled in lower_with
                self.handler_canonical.insert(name.to_string(), then_c);
                return;
            }
        }

        // Dynamic handler: RHS is an arbitrary expression (e.g. function call).
        // Look up effect names from the typechecker's check result. Prefer the
        // pat-id-keyed entry, which survives the per-clause `handlers`
        // save/restore in the typechecker.
        let dynamic_info = pat_id
            .and_then(|id| self.check_result.let_binding_handlers.get(&id))
            .or_else(|| self.check_result.handlers.get(name))
            .map(|info| {
                let effects = if info.effect_entries.is_empty() {
                    info.effects
                        .iter()
                        .map(|e| self.canonicalize_effect(e))
                        .collect()
                } else {
                    info.effect_entries
                        .iter()
                        .map(crate::typechecker::applied_effect_key)
                        .map(|effect| self.canonicalize_effect(&effect))
                        .collect()
                };
                let has_return = info.return_type.is_some();
                (effects, has_return)
            })
            .or_else(|| {
                self.semantic_type_at_node(value.id)
                    .and_then(|ty| self.dynamic_handler_info_from_type(ty))
                    .map(|effects| (effects, false))
            });
        let dynamic_info = dynamic_info.or_else(|| self.dynamic_handler_info_from_expr(value));
        if let Some((effects, has_return)) = dynamic_info {
            // A dynamic handler is still an ordinary first-class value. Bind
            // it under the pattern variable's Core name so uses outside a
            // `with` boundary (for example returning two handlers in a tuple)
            // reference the value actually produced by the factory call.
            // `handle_dynamic_vars` then points `with name` at that same
            // binding instead of a lowering-only temporary.
            let var = core_var(name);
            self.handle_dynamic_vars
                .insert(name.to_string(), (var, effects, has_return));
        }
    }

    pub(crate) fn recover_handler_factory_binding(&mut self, value: &Expr) -> Option<String> {
        let (factory_name, _head, args) = collect_fun_call(value)?;
        let factory = self.handler_factory_defs.get(factory_name)?.clone();
        if factory.params.len() != args.len() {
            return None;
        }
        if !args
            .iter()
            .all(|arg| Self::handler_factory_arg_supported(arg))
        {
            return None;
        }
        if factory.body.return_clause.is_some() {
            return None;
        }
        let captures: Vec<(String, Expr)> = factory
            .params
            .iter()
            .cloned()
            .zip(args.iter().map(|arg| (*arg).clone()))
            .collect();
        if Self::handler_factory_capture_collides(&captures, &factory.body) {
            return None;
        }

        let synthetic = format!("__handler_factory_{}", value.id.0);
        let source_module = factory
            .source_module
            .as_deref()
            .unwrap_or_else(|| self.current_semantic_module_name());
        let canonical_effects = self
            .semantic_type_at_node(value.id)
            .and_then(|ty| self.dynamic_handler_info_from_type(ty))
            .unwrap_or_else(|| {
                self.resolved_effect_refs_for_module(source_module, &factory.body.effects)
            });
        self.handler_defs.insert(
            synthetic.clone(),
            crate::codegen::lower::HandlerInfo {
                effects: canonical_effects,
                arms: factory.body.arms.iter().map(|a| a.node.clone()).collect(),
                return_clause: None,
                source_module: factory.source_module,
                captures,
            },
        );
        Some(synthetic)
    }

    pub(crate) fn handler_factory_arg_supported(expr: &Expr) -> bool {
        match &expr.kind {
            ExprKind::Lit { .. }
            | ExprKind::Var { .. }
            | ExprKind::Constructor { .. }
            | ExprKind::QualifiedName { .. }
            | ExprKind::DictRef { .. } => true,
            ExprKind::Ascription { expr, .. } => Self::handler_factory_arg_supported(expr),
            ExprKind::Tuple { elements } => {
                elements.iter().all(Self::handler_factory_arg_supported)
            }
            ExprKind::ListLit { elements, .. } => elements
                .iter()
                .all(|element| Self::handler_factory_arg_supported(&element.node)),
            _ => false,
        }
    }

    pub(crate) fn handler_factory_capture_collides(
        captures: &[(String, Expr)],
        body: &crate::ast::HandlerBody,
    ) -> bool {
        let capture_names: HashSet<&str> = captures.iter().map(|(name, _)| name.as_str()).collect();
        body.arms
            .iter()
            .flat_map(|arm| arm.node.params.iter())
            .chain(body.return_clause.iter().flat_map(|arm| arm.params.iter()))
            .any(|param| match param {
                Pat::Var { name, .. } => capture_names.contains(name.as_str()),
                _ => false,
            })
    }

    pub(crate) fn dynamic_handler_info_from_expr(
        &self,
        expr: &Expr,
    ) -> Option<(Vec<String>, bool)> {
        let cr = &self.check_result;
        if let Some(ty) = self.semantic_type_at_node(expr.id)
            && let Some(effects) = self.dynamic_handler_info_from_type(ty)
        {
            return Some((effects, false));
        }

        if let ExprKind::Var { name } = &expr.kind
            && let Some(scheme) = cr.env.get(&self.resolved_env_lookup_name(expr.id, name))
            && let Some(effects) = self.dynamic_handler_info_from_type(&scheme.ty)
        {
            return Some((effects, false));
        }

        if let Some((func_name, head_expr, args)) = collect_fun_call(expr)
            && let Some(scheme) = cr
                .env
                .get(&self.resolved_env_lookup_name(head_expr.id, func_name))
        {
            let mut ty = scheme.ty.clone();
            let arg_count = args.len();
            for _ in 0..arg_count {
                match ty {
                    Type::Fun(_, ret, _) => ty = *ret,
                    _ => break,
                }
            }
            if let Some(effects) = self.dynamic_handler_info_from_type(&ty) {
                return Some((effects, false));
            }
        }

        None
    }

    pub(crate) fn dynamic_handler_info_from_type(&self, ty: &Type) -> Option<Vec<String>> {
        if let Type::Con(name, args) = ty
            && name == crate::typechecker::canonicalize_type_name("Handler")
        {
            let effects: Vec<String> = args
                .iter()
                .filter_map(|arg| {
                    if let Type::Con(effect_name, effect_args) = arg {
                        let key = crate::typechecker::applied_effect_key(
                            &crate::typechecker::EffectEntry {
                                name: effect_name.clone(),
                                args: effect_args.clone(),
                            },
                        );
                        Some(self.canonicalize_effect(&key))
                    } else {
                        None
                    }
                })
                .collect();
            if effects.is_empty() {
                None
            } else {
                Some(effects)
            }
        } else {
            None
        }
    }

    /// Resolve a handle binding's RHS to a canonical handler name.
    /// Walks through variable references, if/else branches, and handler expressions.
    pub(crate) fn resolve_handle_value(&self, expr: &Expr) -> Option<String> {
        match &expr.kind {
            ExprKind::Var { name } => self.known_handler_binding_name(expr.id, name),
            ExprKind::HandlerExpr { .. } => {
                // Handler expressions registered under synthetic name
                let synthetic = format!("__handler_expr_{}", expr.id.0);
                if self.handler_defs.contains_key(&synthetic) {
                    Some(synthetic)
                } else {
                    None
                }
            }
            ExprKind::If {
                then_branch,
                else_branch,
                ..
            } => self
                .resolve_handle_value(then_branch)
                .or_else(|| self.resolve_handle_value(else_branch)),
            _ => None,
        }
    }
}
