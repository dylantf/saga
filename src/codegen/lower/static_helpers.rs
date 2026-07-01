use crate::ast::{self, Expr, ExprKind, Pat, Stmt};
use crate::codegen::cerl::CExpr;

use super::pats;
use super::util::{collect_ctor_call, collect_effect_call_expr, collect_fun_call, core_var};
use super::{GeneratedHelperVariant, Lowerer, StaticTailResumeOp};

#[derive(Clone)]
struct StaticHelperCapture {
    name: String,
    arg: Expr,
}

impl<'a> Lowerer<'a> {
    fn helper_lookup_candidates(
        &self,
        lookup_name: &str,
        head_id: crate::ast::NodeId,
    ) -> Vec<String> {
        let mut candidates = Vec::new();
        if let Some(resolved) = self.resolved.get(&head_id) {
            candidates.push(resolved.canonical_name.clone());
        }
        candidates.push(lookup_name.to_string());
        candidates.dedup();
        candidates
    }

    fn helper_key_for_call(
        &self,
        lookup_name: &str,
        head_id: crate::ast::NodeId,
    ) -> Option<String> {
        self.helper_lookup_candidates(lookup_name, head_id)
            .into_iter()
            .find(|candidate| self.local_helper_defs.contains_key(candidate))
    }

    pub(super) fn try_inline_static_helper_call(
        &mut self,
        lookup_name: &str,
        head: &Expr,
        args: &[&Expr],
        return_k: Option<CExpr>,
    ) -> Option<CExpr> {
        let helper_key = self.helper_key_for_call(lookup_name, head.id)?;
        let helper = self.local_helper_defs.get(&helper_key)?.clone();
        if helper.source_module != self.current_semantic_module_name()
            || self
                .helper_inline_stack
                .iter()
                .any(|name| name == &helper_key)
            || !self.static_helper_call_supported(&helper_key, args, &mut Vec::new())
        {
            return None;
        }

        let param_types = self
            .resolved_fun_info(head.id, lookup_name)
            .map(|f| f.expected_arg_types(args.len()));
        let (arg_vars, arg_bindings) =
            self.lower_call_args_with_expected_types(args, param_types.as_deref());
        let params = pats::lower_params(&helper.params);
        if params.len() != arg_vars.len() {
            return None;
        }

        self.helper_inline_stack.push(helper_key);
        let body = self.lower_expr_with_installed_return_k(&helper.body, return_k);
        self.helper_inline_stack.pop();

        let body = params
            .into_iter()
            .zip(arg_vars)
            .rev()
            .fold(body, |body, (param, arg)| {
                CExpr::Let(param, Box::new(CExpr::Var(arg)), Box::new(body))
            });
        Some(self.wrap_let_bindings(arg_bindings, body))
    }

    fn direct_value_with_return_k(&mut self, value: CExpr, return_k: Option<CExpr>) -> CExpr {
        if let Some(k) = return_k {
            match k {
                CExpr::Fun(params, body) if params.len() == 1 => {
                    CExpr::Let(params[0].clone(), Box::new(value), body)
                }
                other => {
                    let result_var = self.fresh();
                    CExpr::Let(
                        result_var.clone(),
                        Box::new(value),
                        Box::new(CExpr::Apply(Box::new(other), vec![CExpr::Var(result_var)])),
                    )
                }
            }
        } else {
            value
        }
    }

    fn generated_helper_variant_name(&mut self, lookup_name: &str) -> String {
        let safe = lookup_name
            .chars()
            .map(|ch| if ch.is_ascii_alphanumeric() { ch } else { '_' })
            .collect::<String>();
        format!("__saga_static_helper_{}_{}", safe, self.fresh())
    }

    fn generated_helper_capture_param_name(name: &str) -> String {
        format!("_StaticCapture_{}", core_var(name))
    }

    pub(super) fn try_imported_static_helper_variant_call(
        &mut self,
        lookup_name: &str,
        head: &Expr,
        args: &[&Expr],
        return_k: Option<CExpr>,
    ) -> Option<CExpr> {
        let helper_key = self.helper_key_for_call(lookup_name, head.id)?;
        let helper = self.local_helper_defs.get(&helper_key)?.clone();
        if helper.source_module == self.current_semantic_module_name()
            || self
                .helper_inline_stack
                .iter()
                .any(|name| name == &helper_key)
            || !self.imported_static_helper_call_supported(&helper_key, args)
        {
            return None;
        }
        let captures = self.imported_static_helper_variant_captures(&helper_key)?;

        let param_types = self
            .resolved_fun_info(head.id, &helper_key)
            .or_else(|| self.resolved_fun_info(head.id, lookup_name))
            .map(|f| {
                f.param_types
                    .iter()
                    .take(args.len())
                    .cloned()
                    .collect::<Vec<_>>()
            });
        let (arg_vars, arg_bindings) =
            self.lower_call_args_with_expected_types(args, param_types.as_deref());
        let params = pats::lower_params(&helper.params);
        if params.len() != arg_vars.len() {
            return None;
        }
        let capture_param_names: Vec<String> = captures
            .iter()
            .map(|capture| Self::generated_helper_capture_param_name(&capture.name))
            .collect();
        let mut capture_arg_bindings = Vec::new();
        let mut capture_arg_vars = Vec::new();
        for capture in &captures {
            let var = self.fresh();
            let ce = self.lower_expr_value(&capture.arg);
            capture_arg_bindings.push((var.clone(), ce));
            capture_arg_vars.push(var);
        }

        let variant_name = self.generated_helper_variant_name(&helper_key);
        let saved_source_module = self.current_handler_source_module.clone();
        let saved_function = self.current_function.clone();
        let saved_evidence = self.current_evidence.clone();
        let saved_resolved = self.resolved.clone();
        let saved_static_tail_resume_ops = self.static_tail_resume_ops.clone();
        let saved_variant_capture_bindings =
            std::mem::take(&mut self.static_helper_variant_capture_bindings);
        self.current_handler_source_module = Some(helper.source_module.clone());
        self.current_function = variant_name.clone();
        self.current_evidence = None;
        self.static_helper_variant_capture_bindings = captures
            .iter()
            .zip(capture_param_names.iter())
            .map(|(capture, param_name)| (capture.name.clone(), param_name.clone()))
            .collect();
        for plan in self.static_tail_resume_ops.values_mut() {
            plan.captures.clear();
        }
        if let Some(module_semantics) = self.ctx.module_semantics(&helper.source_module) {
            self.resolved = module_semantics.resolution.clone();
        }
        self.helper_inline_stack.push(helper_key);
        let body = self.lower_expr_with_installed_return_k(&helper.body, None);
        self.helper_inline_stack.pop();
        self.resolved = saved_resolved;
        self.static_tail_resume_ops = saved_static_tail_resume_ops;
        self.static_helper_variant_capture_bindings = saved_variant_capture_bindings;
        self.current_handler_source_module = saved_source_module;
        self.current_function = saved_function;
        self.current_evidence = saved_evidence;

        let mut variant_params = params;
        variant_params.extend(capture_param_names);
        let arity = variant_params.len();
        self.generated_helper_variants.push(GeneratedHelperVariant {
            name: variant_name.clone(),
            arity,
            body: CExpr::Fun(variant_params, Box::new(body)),
        });

        let mut call_args: Vec<CExpr> = arg_vars.into_iter().map(CExpr::Var).collect();
        call_args.extend(capture_arg_vars.into_iter().map(CExpr::Var));
        let call = CExpr::Apply(Box::new(CExpr::FunRef(variant_name, arity)), call_args);
        let call = self.direct_value_with_return_k(call, return_k);
        let call = self.wrap_let_bindings(capture_arg_bindings, call);
        Some(self.wrap_let_bindings(arg_bindings, call))
    }

    fn static_helper_call_supported(
        &self,
        lookup_name: &str,
        args: &[&Expr],
        stack: &mut Vec<String>,
    ) -> bool {
        let Some(helper) = self.local_helper_defs.get(lookup_name) else {
            return false;
        };
        if helper.source_module != self.current_semantic_module_name()
            || stack.iter().any(|name| name == lookup_name)
            || !Self::static_helper_params_supported(&helper.params)
            || helper.params.len() != args.len()
            || args.iter().any(|arg| {
                self.branch_is_effectful(arg) || !self.static_helper_expr_supported(arg, stack)
            })
        {
            return false;
        }

        stack.push(lookup_name.to_string());
        let supported = self.static_helper_expr_supported(&helper.body, stack);
        stack.pop();
        supported && self.static_helper_call_contains_covered_effect(lookup_name, &mut Vec::new())
    }

    fn static_helper_call_contains_covered_effect(
        &self,
        lookup_name: &str,
        stack: &mut Vec<String>,
    ) -> bool {
        let Some(helper) = self.local_helper_defs.get(lookup_name) else {
            return false;
        };
        if stack.iter().any(|name| name == lookup_name) {
            return false;
        }
        stack.push(lookup_name.to_string());
        let contains = self.static_helper_expr_contains_covered_effect(&helper.body, stack);
        stack.pop();
        contains
    }

    fn static_helper_expr_contains_covered_effect(
        &self,
        expr: &Expr,
        stack: &mut Vec<String>,
    ) -> bool {
        if let Some((head, op_name, qualifier, _args)) = collect_effect_call_expr(expr) {
            return self
                .resolved_effect_call_name(head.id, op_name, qualifier)
                .map(|effect_name| {
                    self.static_tail_resume_ops
                        .contains_key(&format!("{}.{}", effect_name, op_name))
                })
                .unwrap_or(false);
        }

        if self.expr_is_effectful_call(expr) {
            return collect_fun_call(expr)
                .map(|(callee, _, _)| {
                    self.static_helper_call_contains_covered_effect(callee, stack)
                })
                .unwrap_or(false);
        }

        match &expr.kind {
            ExprKind::App { func, arg } => {
                self.static_helper_expr_contains_covered_effect(func, stack)
                    || self.static_helper_expr_contains_covered_effect(arg, stack)
            }
            ExprKind::BinOp { left, right, .. } => {
                self.static_helper_expr_contains_covered_effect(left, stack)
                    || self.static_helper_expr_contains_covered_effect(right, stack)
            }
            ExprKind::UnaryMinus { expr } | ExprKind::FieldAccess { expr, .. } => {
                self.static_helper_expr_contains_covered_effect(expr, stack)
            }
            ExprKind::Tuple { elements } | ExprKind::ListLit { elements } => elements
                .iter()
                .any(|element| self.static_helper_expr_contains_covered_effect(element, stack)),
            ExprKind::RecordCreate { fields, .. } | ExprKind::AnonRecordCreate { fields } => fields
                .iter()
                .any(|(_, _, field)| self.static_helper_expr_contains_covered_effect(field, stack)),
            ExprKind::RecordUpdate { record, fields, .. } => {
                self.static_helper_expr_contains_covered_effect(record, stack)
                    || fields.iter().any(|(_, _, field)| {
                        self.static_helper_expr_contains_covered_effect(field, stack)
                    })
            }
            ExprKind::Ascription { expr, .. } => {
                self.static_helper_expr_contains_covered_effect(expr, stack)
            }
            ExprKind::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => {
                self.static_helper_expr_contains_covered_effect(cond, stack)
                    || self.static_helper_expr_contains_covered_effect(then_branch, stack)
                    || self.static_helper_expr_contains_covered_effect(else_branch, stack)
            }
            ExprKind::Case {
                scrutinee, arms, ..
            } => {
                self.static_helper_expr_contains_covered_effect(scrutinee, stack)
                    || arms.iter().any(|arm| {
                        arm.node.guard.as_ref().is_some_and(|guard| {
                            self.static_helper_expr_contains_covered_effect(guard, stack)
                        }) || self.static_helper_expr_contains_covered_effect(&arm.node.body, stack)
                    })
            }
            ExprKind::Block { stmts, .. } => stmts.iter().any(|stmt| match &stmt.node {
                Stmt::Let { value, .. } => {
                    self.static_helper_expr_contains_covered_effect(value, stack)
                }
                Stmt::Expr(expr) => self.static_helper_expr_contains_covered_effect(expr, stack),
                Stmt::LetFun { .. } => false,
            }),
            ExprKind::StringInterp { parts, .. } => parts.iter().any(|part| match part {
                ast::StringPart::Lit(_) => false,
                ast::StringPart::Expr(expr) => {
                    self.static_helper_expr_contains_covered_effect(expr, stack)
                }
            }),
            ExprKind::DictMethodAccess { dict, .. } | ExprKind::DictSuperAccess { dict, .. } => {
                self.static_helper_expr_contains_covered_effect(dict, stack)
            }
            ExprKind::ForeignCall { args, .. } => args
                .iter()
                .any(|arg| self.static_helper_expr_contains_covered_effect(arg, stack)),
            _ => false,
        }
    }

    fn static_helper_params_supported(params: &[Pat]) -> bool {
        params.iter().all(|param| {
            matches!(
                param,
                Pat::Var { .. }
                    | Pat::Wildcard { .. }
                    | Pat::Lit {
                        value: ast::Lit::Unit,
                        ..
                    }
            )
        })
    }

    fn static_helper_direct_effect_call_supported(
        &self,
        head: &Expr,
        op_name: &str,
        qualifier: Option<&str>,
        args: &[&Expr],
        stack: &mut Vec<String>,
    ) -> bool {
        let Some(effect_name) = self.resolved_effect_call_name(head.id, op_name, qualifier) else {
            return false;
        };
        let key = format!("{}.{}", effect_name, op_name);
        self.static_tail_resume_ops.contains_key(&key)
            && args.iter().all(|arg| {
                !self.branch_is_effectful(arg) && self.static_helper_expr_supported(arg, stack)
            })
    }

    fn static_helper_expr_supported(&self, expr: &Expr, stack: &mut Vec<String>) -> bool {
        if let Some((head, op_name, qualifier, args)) = collect_effect_call_expr(expr) {
            return self.static_helper_direct_effect_call_supported(
                head, op_name, qualifier, &args, stack,
            );
        }

        if self.expr_is_effectful_call(expr) {
            let Some((callee, _head, args)) = collect_fun_call(expr) else {
                return false;
            };
            return self.static_helper_call_supported(callee, &args, stack);
        }

        match &expr.kind {
            ExprKind::Lit { .. }
            | ExprKind::Var { .. }
            | ExprKind::Constructor { .. }
            | ExprKind::QualifiedName { .. }
            | ExprKind::DictRef { .. } => true,
            ExprKind::App { func, arg } => {
                self.static_helper_expr_supported(func, stack)
                    && self.static_helper_expr_supported(arg, stack)
            }
            ExprKind::BinOp { left, right, .. } => {
                self.static_helper_expr_supported(left, stack)
                    && self.static_helper_expr_supported(right, stack)
            }
            ExprKind::UnaryMinus { expr } | ExprKind::FieldAccess { expr, .. } => {
                self.static_helper_expr_supported(expr, stack)
            }
            ExprKind::Tuple { elements } | ExprKind::ListLit { elements } => elements
                .iter()
                .all(|element| self.static_helper_expr_supported(element, stack)),
            ExprKind::RecordCreate { fields, .. }
            | ExprKind::AnonRecordCreate { fields }
            | ExprKind::RecordBuild { fields, .. } => fields
                .iter()
                .all(|(_, _, field)| self.static_helper_expr_supported(field, stack)),
            ExprKind::RecordUpdate { record, fields, .. } => {
                self.static_helper_expr_supported(record, stack)
                    && fields
                        .iter()
                        .all(|(_, _, field)| self.static_helper_expr_supported(field, stack))
            }
            ExprKind::Ascription { expr, .. } => self.static_helper_expr_supported(expr, stack),
            ExprKind::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => {
                self.static_helper_expr_supported(cond, stack)
                    && self.static_helper_expr_supported(then_branch, stack)
                    && self.static_helper_expr_supported(else_branch, stack)
            }
            ExprKind::Case {
                scrutinee, arms, ..
            } => {
                self.static_helper_expr_supported(scrutinee, stack)
                    && arms.iter().all(|arm| {
                        arm.node
                            .guard
                            .as_ref()
                            .is_none_or(|guard| self.static_helper_expr_supported(guard, stack))
                            && self.static_helper_expr_supported(&arm.node.body, stack)
                    })
            }
            ExprKind::Block { stmts, .. } => stmts.iter().all(|stmt| match &stmt.node {
                Stmt::Let { value, .. } => self.static_helper_expr_supported(value, stack),
                Stmt::Expr(expr) => self.static_helper_expr_supported(expr, stack),
                Stmt::LetFun { .. } => false,
            }),
            ExprKind::StringInterp { parts, .. } => parts.iter().all(|part| match part {
                ast::StringPart::Lit(_) => true,
                ast::StringPart::Expr(expr) => self.static_helper_expr_supported(expr, stack),
            }),
            ExprKind::DictMethodAccess { dict, .. } | ExprKind::DictSuperAccess { dict, .. } => {
                self.static_helper_expr_supported(dict, stack)
            }
            ExprKind::ForeignCall { args, .. } => args
                .iter()
                .all(|arg| self.static_helper_expr_supported(arg, stack)),
            ExprKind::Lambda { .. }
            | ExprKind::With { .. }
            | ExprKind::Resume { .. }
            | ExprKind::Do { .. }
            | ExprKind::Receive { .. }
            | ExprKind::BitString { .. }
            | ExprKind::HandlerExpr { .. }
            | ExprKind::Pipe { .. }
            | ExprKind::BinOpChain { .. }
            | ExprKind::PipeBack { .. }
            | ExprKind::ComposeForward { .. }
            | ExprKind::Cons { .. }
            | ExprKind::ListComprehension { .. }
            | ExprKind::EffectCall { .. } => false,
        }
    }

    fn imported_static_helper_call_supported(&self, lookup_name: &str, args: &[&Expr]) -> bool {
        self.imported_static_helper_call_supported_inner(lookup_name, args, &mut Vec::new())
    }

    fn imported_static_helper_call_supported_inner(
        &self,
        lookup_name: &str,
        args: &[&Expr],
        stack: &mut Vec<String>,
    ) -> bool {
        let Some(helper) = self.local_helper_defs.get(lookup_name) else {
            return false;
        };
        if helper.source_module == self.current_semantic_module_name()
            || stack.iter().any(|name| name == lookup_name)
            || !Self::static_helper_params_supported(&helper.params)
            || helper.params.len() != args.len()
            || args.iter().any(|arg| {
                self.branch_is_effectful(arg) || !self.imported_static_helper_arg_supported(arg)
            })
        {
            return false;
        }

        stack.push(lookup_name.to_string());
        let body_supported =
            self.imported_static_helper_expr_supported(&helper.body, &helper.source_module, stack);
        stack.pop();
        let contains_covered = self
            .imported_static_helper_used_static_ops(lookup_name)
            .is_some_and(|ops| !ops.is_empty());
        body_supported && contains_covered
    }

    fn imported_static_helper_variant_captures(
        &self,
        lookup_name: &str,
    ) -> Option<Vec<StaticHelperCapture>> {
        let used_ops = self.imported_static_helper_used_static_ops(lookup_name)?;
        let mut captures = std::collections::BTreeMap::new();
        for op_key in used_ops {
            let plan = self.static_tail_resume_ops.get(&op_key)?;
            Self::collect_static_tail_resume_plan_captures(plan, &mut captures)?;
        }
        Some(
            captures
                .into_iter()
                .map(|(name, arg)| StaticHelperCapture { name, arg })
                .collect(),
        )
    }

    fn imported_static_helper_used_static_ops(
        &self,
        lookup_name: &str,
    ) -> Option<std::collections::BTreeSet<String>> {
        let mut used_ops = std::collections::BTreeSet::new();
        self.imported_static_helper_used_static_ops_inner(
            lookup_name,
            &mut Vec::new(),
            &mut used_ops,
        )?;
        Some(used_ops)
    }

    fn imported_static_helper_used_static_ops_inner(
        &self,
        lookup_name: &str,
        stack: &mut Vec<String>,
        used_ops: &mut std::collections::BTreeSet<String>,
    ) -> Option<()> {
        let helper = self.local_helper_defs.get(lookup_name)?;
        if stack.iter().any(|name| name == lookup_name) {
            return None;
        }
        stack.push(lookup_name.to_string());
        self.imported_static_helper_expr_used_static_ops(
            &helper.body,
            &helper.source_module,
            stack,
            used_ops,
        )?;
        stack.pop();
        Some(())
    }

    fn imported_static_helper_expr_used_static_ops(
        &self,
        expr: &Expr,
        source_module: &str,
        stack: &mut Vec<String>,
        used_ops: &mut std::collections::BTreeSet<String>,
    ) -> Option<()> {
        if let Some((head, op_name, _qualifier, _args)) = collect_effect_call_expr(expr) {
            let effect_name = self.resolved_effect_call_name_for_module(source_module, head.id)?;
            let key = format!("{}.{}", effect_name, op_name);
            if self.static_tail_resume_ops.contains_key(&key) {
                used_ops.insert(key);
            }
            return Some(());
        }
        if let Some((callee, _head, args)) = collect_fun_call(expr)
            && !args.is_empty()
        {
            let nested_key = format!("{}.{}", source_module, callee);
            if self.local_helper_defs.contains_key(&nested_key) {
                return self.imported_static_helper_used_static_ops_inner(
                    &nested_key,
                    stack,
                    used_ops,
                );
            }
        }
        if let Some((_ctor, args)) = collect_ctor_call(expr) {
            for arg in args {
                self.imported_static_helper_expr_used_static_ops(
                    arg,
                    source_module,
                    stack,
                    used_ops,
                )?;
            }
            return Some(());
        }

        match &expr.kind {
            ExprKind::App { .. } => Some(()),
            ExprKind::BinOp { left, right, .. } => {
                self.imported_static_helper_expr_used_static_ops(
                    left,
                    source_module,
                    stack,
                    used_ops,
                )?;
                self.imported_static_helper_expr_used_static_ops(
                    right,
                    source_module,
                    stack,
                    used_ops,
                )
            }
            ExprKind::UnaryMinus { expr } | ExprKind::FieldAccess { expr, .. } => self
                .imported_static_helper_expr_used_static_ops(expr, source_module, stack, used_ops),
            ExprKind::Tuple { elements } | ExprKind::ListLit { elements } => {
                for element in elements {
                    self.imported_static_helper_expr_used_static_ops(
                        element,
                        source_module,
                        stack,
                        used_ops,
                    )?;
                }
                Some(())
            }
            ExprKind::RecordCreate { fields, .. } | ExprKind::AnonRecordCreate { fields } => {
                for (_, _, field) in fields {
                    self.imported_static_helper_expr_used_static_ops(
                        field,
                        source_module,
                        stack,
                        used_ops,
                    )?;
                }
                Some(())
            }
            ExprKind::RecordUpdate { record, fields, .. } => {
                self.imported_static_helper_expr_used_static_ops(
                    record,
                    source_module,
                    stack,
                    used_ops,
                )?;
                for (_, _, field) in fields {
                    self.imported_static_helper_expr_used_static_ops(
                        field,
                        source_module,
                        stack,
                        used_ops,
                    )?;
                }
                Some(())
            }
            ExprKind::Ascription { expr, .. } => self.imported_static_helper_expr_used_static_ops(
                expr,
                source_module,
                stack,
                used_ops,
            ),
            ExprKind::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => {
                self.imported_static_helper_expr_used_static_ops(
                    cond,
                    source_module,
                    stack,
                    used_ops,
                )?;
                self.imported_static_helper_expr_used_static_ops(
                    then_branch,
                    source_module,
                    stack,
                    used_ops,
                )?;
                self.imported_static_helper_expr_used_static_ops(
                    else_branch,
                    source_module,
                    stack,
                    used_ops,
                )
            }
            ExprKind::Case {
                scrutinee, arms, ..
            } => {
                self.imported_static_helper_expr_used_static_ops(
                    scrutinee,
                    source_module,
                    stack,
                    used_ops,
                )?;
                for arm in arms {
                    if let Some(guard) = &arm.node.guard {
                        self.imported_static_helper_expr_used_static_ops(
                            guard,
                            source_module,
                            stack,
                            used_ops,
                        )?;
                    }
                    self.imported_static_helper_expr_used_static_ops(
                        &arm.node.body,
                        source_module,
                        stack,
                        used_ops,
                    )?;
                }
                Some(())
            }
            ExprKind::Block { stmts, .. } => {
                for stmt in stmts {
                    match &stmt.node {
                        Stmt::Let { value, .. } => self
                            .imported_static_helper_expr_used_static_ops(
                                value,
                                source_module,
                                stack,
                                used_ops,
                            )?,
                        Stmt::Expr(expr) => self.imported_static_helper_expr_used_static_ops(
                            expr,
                            source_module,
                            stack,
                            used_ops,
                        )?,
                        Stmt::LetFun { .. } => {}
                    }
                }
                Some(())
            }
            ExprKind::StringInterp { parts, .. } => {
                for part in parts {
                    if let ast::StringPart::Expr(expr) = part {
                        self.imported_static_helper_expr_used_static_ops(
                            expr,
                            source_module,
                            stack,
                            used_ops,
                        )?;
                    }
                }
                Some(())
            }
            ExprKind::DictMethodAccess { dict, .. } | ExprKind::DictSuperAccess { dict, .. } => {
                self.imported_static_helper_expr_used_static_ops(
                    dict,
                    source_module,
                    stack,
                    used_ops,
                )
            }
            ExprKind::ForeignCall { args, .. } => {
                for arg in args {
                    self.imported_static_helper_expr_used_static_ops(
                        arg,
                        source_module,
                        stack,
                        used_ops,
                    )?;
                }
                Some(())
            }
            _ => Some(()),
        }
    }

    fn imported_static_helper_direct_effect_call_supported(
        &self,
        source_module: &str,
        head: &Expr,
        op_name: &str,
        _qualifier: Option<&str>,
        args: &[&Expr],
    ) -> bool {
        let Some(effect_name) = self.resolved_effect_call_name_for_module(source_module, head.id)
        else {
            return false;
        };
        let key = format!("{}.{}", effect_name, op_name);
        let has_key = self.static_tail_resume_ops.contains_key(&key);
        let args_ok = args.iter().all(|arg| {
            !self.branch_is_effectful(arg) && self.imported_static_helper_arg_supported(arg)
        });
        has_key && args_ok
    }

    fn imported_static_helper_arg_supported(&self, expr: &Expr) -> bool {
        Self::imported_static_helper_pure_expr_supported(expr)
    }

    fn imported_static_helper_pure_expr_supported(expr: &Expr) -> bool {
        if let Some((_ctor, args)) = collect_ctor_call(expr) {
            return args
                .into_iter()
                .all(Self::imported_static_helper_pure_expr_supported);
        }
        if collect_effect_call_expr(expr).is_some() {
            return false;
        }

        match &expr.kind {
            ExprKind::Lit { .. }
            | ExprKind::Var { .. }
            | ExprKind::Constructor { .. }
            | ExprKind::QualifiedName { .. }
            | ExprKind::DictRef { .. } => true,
            ExprKind::App { .. } => false,
            ExprKind::BinOp { left, right, .. } => {
                Self::imported_static_helper_pure_expr_supported(left)
                    && Self::imported_static_helper_pure_expr_supported(right)
            }
            ExprKind::UnaryMinus { expr } | ExprKind::FieldAccess { expr, .. } => {
                Self::imported_static_helper_pure_expr_supported(expr)
            }
            ExprKind::Tuple { elements } | ExprKind::ListLit { elements } => elements
                .iter()
                .all(Self::imported_static_helper_pure_expr_supported),
            ExprKind::RecordCreate { fields, .. } | ExprKind::AnonRecordCreate { fields } => fields
                .iter()
                .all(|(_, _, field)| Self::imported_static_helper_pure_expr_supported(field)),
            ExprKind::RecordUpdate { record, fields, .. } => {
                Self::imported_static_helper_pure_expr_supported(record)
                    && fields.iter().all(|(_, _, field)| {
                        Self::imported_static_helper_pure_expr_supported(field)
                    })
            }
            ExprKind::Ascription { expr, .. } => {
                Self::imported_static_helper_pure_expr_supported(expr)
            }
            ExprKind::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => {
                Self::imported_static_helper_pure_expr_supported(cond)
                    && Self::imported_static_helper_pure_expr_supported(then_branch)
                    && Self::imported_static_helper_pure_expr_supported(else_branch)
            }
            ExprKind::Case {
                scrutinee, arms, ..
            } => {
                Self::imported_static_helper_pure_expr_supported(scrutinee)
                    && arms.iter().all(|arm| {
                        arm.node.guard.as_ref().is_none_or(|guard| {
                            Self::imported_static_helper_pure_expr_supported(guard)
                        }) && Self::imported_static_helper_pure_expr_supported(&arm.node.body)
                    })
            }
            ExprKind::Block { stmts, .. } => stmts.iter().all(|stmt| match &stmt.node {
                Stmt::Let { value, .. } => Self::imported_static_helper_pure_expr_supported(value),
                Stmt::Expr(expr) => Self::imported_static_helper_pure_expr_supported(expr),
                Stmt::LetFun { .. } => false,
            }),
            ExprKind::StringInterp { parts, .. } => parts.iter().all(|part| match part {
                ast::StringPart::Lit(_) => true,
                ast::StringPart::Expr(expr) => {
                    Self::imported_static_helper_pure_expr_supported(expr)
                }
            }),
            ExprKind::DictMethodAccess { dict, .. } | ExprKind::DictSuperAccess { dict, .. } => {
                Self::imported_static_helper_pure_expr_supported(dict)
            }
            ExprKind::ForeignCall { args, .. } => args
                .iter()
                .all(Self::imported_static_helper_pure_expr_supported),
            _ => false,
        }
    }

    fn imported_static_helper_expr_supported(
        &self,
        expr: &Expr,
        source_module: &str,
        stack: &mut Vec<String>,
    ) -> bool {
        if let Some((head, op_name, qualifier, args)) = collect_effect_call_expr(expr) {
            return self.imported_static_helper_direct_effect_call_supported(
                source_module,
                head,
                op_name,
                qualifier,
                &args,
            );
        }
        if let Some((callee, _head, args)) = collect_fun_call(expr)
            && !args.is_empty()
        {
            let nested_key = format!("{}.{}", source_module, callee);
            return self.local_helper_defs.contains_key(&nested_key)
                && self.imported_static_helper_call_supported_inner(&nested_key, &args, stack);
        }
        if let Some((_ctor, args)) = collect_ctor_call(expr) {
            return args
                .into_iter()
                .all(|arg| self.imported_static_helper_expr_supported(arg, source_module, stack));
        }

        match &expr.kind {
            ExprKind::Lit { .. }
            | ExprKind::Var { .. }
            | ExprKind::Constructor { .. }
            | ExprKind::QualifiedName { .. }
            | ExprKind::DictRef { .. } => true,
            ExprKind::App { .. } => false,
            ExprKind::BinOp { left, right, .. } => {
                self.imported_static_helper_expr_supported(left, source_module, stack)
                    && self.imported_static_helper_expr_supported(right, source_module, stack)
            }
            ExprKind::UnaryMinus { expr } | ExprKind::FieldAccess { expr, .. } => {
                self.imported_static_helper_expr_supported(expr, source_module, stack)
            }
            ExprKind::Tuple { elements } | ExprKind::ListLit { elements } => {
                elements.iter().all(|element| {
                    self.imported_static_helper_expr_supported(element, source_module, stack)
                })
            }
            ExprKind::RecordCreate { fields, .. } | ExprKind::AnonRecordCreate { fields } => {
                fields.iter().all(|(_, _, field)| {
                    self.imported_static_helper_expr_supported(field, source_module, stack)
                })
            }
            ExprKind::RecordUpdate { record, fields, .. } => {
                self.imported_static_helper_expr_supported(record, source_module, stack)
                    && fields.iter().all(|(_, _, field)| {
                        self.imported_static_helper_expr_supported(field, source_module, stack)
                    })
            }
            ExprKind::Ascription { expr, .. } => {
                self.imported_static_helper_expr_supported(expr, source_module, stack)
            }
            ExprKind::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => {
                self.imported_static_helper_expr_supported(cond, source_module, stack)
                    && self.imported_static_helper_expr_supported(then_branch, source_module, stack)
                    && self.imported_static_helper_expr_supported(else_branch, source_module, stack)
            }
            ExprKind::Case {
                scrutinee, arms, ..
            } => {
                self.imported_static_helper_expr_supported(scrutinee, source_module, stack)
                    && arms.iter().all(|arm| {
                        arm.node.guard.as_ref().is_none_or(|guard| {
                            self.imported_static_helper_expr_supported(guard, source_module, stack)
                        }) && self.imported_static_helper_expr_supported(
                            &arm.node.body,
                            source_module,
                            stack,
                        )
                    })
            }
            ExprKind::Block { stmts, .. } => stmts.iter().all(|stmt| match &stmt.node {
                Stmt::Let { value, .. } => {
                    self.imported_static_helper_expr_supported(value, source_module, stack)
                }
                Stmt::Expr(expr) => {
                    self.imported_static_helper_expr_supported(expr, source_module, stack)
                }
                Stmt::LetFun { .. } => false,
            }),
            ExprKind::StringInterp { parts, .. } => parts.iter().all(|part| match part {
                ast::StringPart::Lit(_) => true,
                ast::StringPart::Expr(expr) => {
                    self.imported_static_helper_expr_supported(expr, source_module, stack)
                }
            }),
            ExprKind::DictMethodAccess { dict, .. } | ExprKind::DictSuperAccess { dict, .. } => {
                self.imported_static_helper_expr_supported(dict, source_module, stack)
            }
            ExprKind::ForeignCall { args, .. } => args
                .iter()
                .all(|arg| self.imported_static_helper_expr_supported(arg, source_module, stack)),
            _ => false,
        }
    }

    fn collect_simple_pat_bindings(
        pat: &Pat,
        bound: &mut std::collections::HashSet<String>,
    ) -> bool {
        match pat {
            Pat::Var { name, .. } => {
                bound.insert(name.clone());
                true
            }
            Pat::Wildcard { .. }
            | Pat::Lit {
                value: ast::Lit::Unit,
                ..
            } => true,
            _ => false,
        }
    }

    fn collect_static_tail_resume_plan_captures(
        plan: &StaticTailResumeOp,
        captures: &mut std::collections::BTreeMap<String, Expr>,
    ) -> Option<()> {
        let mut bound = std::collections::HashSet::new();
        for (name, value) in &plan.captures {
            captures
                .entry(name.clone())
                .or_insert_with(|| value.clone());
            bound.insert(name.clone());
        }
        for param in &plan.arm.params {
            if !Self::collect_simple_pat_bindings(param, &mut bound) {
                return None;
            }
        }
        Self::collect_static_tail_resume_body_captures(&plan.arm.body, &mut bound, captures)
    }

    fn collect_static_tail_resume_body_captures(
        expr: &Expr,
        bound: &mut std::collections::HashSet<String>,
        captures: &mut std::collections::BTreeMap<String, Expr>,
    ) -> Option<()> {
        match &expr.kind {
            ExprKind::Resume { value } => {
                Self::collect_static_tail_resume_value_captures(value, bound, captures)
            }
            ExprKind::Block { stmts, .. } => {
                let (last, prefix) = stmts.split_last()?;
                for stmt in prefix {
                    match &stmt.node {
                        Stmt::Let { pattern, value, .. } => {
                            Self::collect_static_tail_resume_value_captures(
                                value, bound, captures,
                            )?;
                            if !Self::collect_simple_pat_bindings(pattern, bound) {
                                return None;
                            }
                        }
                        Stmt::Expr(expr) => {
                            Self::collect_static_tail_resume_value_captures(expr, bound, captures)?;
                        }
                        Stmt::LetFun { .. } => return None,
                    }
                }
                match &last.node {
                    Stmt::Expr(expr) => {
                        Self::collect_static_tail_resume_body_captures(expr, bound, captures)
                    }
                    Stmt::Let { .. } | Stmt::LetFun { .. } => None,
                }
            }
            _ => None,
        }
    }

    fn collect_static_tail_resume_value_captures(
        expr: &Expr,
        bound: &std::collections::HashSet<String>,
        captures: &mut std::collections::BTreeMap<String, Expr>,
    ) -> Option<()> {
        if let Some((_ctor, args)) = collect_ctor_call(expr) {
            for arg in args {
                Self::collect_static_tail_resume_value_captures(arg, bound, captures)?;
            }
            return Some(());
        }
        if collect_effect_call_expr(expr).is_some() {
            return None;
        }
        match &expr.kind {
            ExprKind::Lit { .. } | ExprKind::Constructor { .. } | ExprKind::DictRef { .. } => {
                Some(())
            }
            ExprKind::Var { name } => {
                if !bound.contains(name) {
                    captures.entry(name.clone()).or_insert_with(|| expr.clone());
                }
                Some(())
            }
            ExprKind::QualifiedName { .. } => None,
            ExprKind::App { .. } => None,
            ExprKind::BinOp { left, right, .. } => {
                Self::collect_static_tail_resume_value_captures(left, bound, captures)?;
                Self::collect_static_tail_resume_value_captures(right, bound, captures)
            }
            ExprKind::UnaryMinus { expr } | ExprKind::FieldAccess { expr, .. } => {
                Self::collect_static_tail_resume_value_captures(expr, bound, captures)
            }
            ExprKind::Tuple { elements } | ExprKind::ListLit { elements } => {
                for element in elements {
                    Self::collect_static_tail_resume_value_captures(element, bound, captures)?;
                }
                Some(())
            }
            ExprKind::RecordCreate { fields, .. } | ExprKind::AnonRecordCreate { fields } => {
                for (_, _, field) in fields {
                    Self::collect_static_tail_resume_value_captures(field, bound, captures)?;
                }
                Some(())
            }
            ExprKind::RecordUpdate { record, fields, .. } => {
                Self::collect_static_tail_resume_value_captures(record, bound, captures)?;
                for (_, _, field) in fields {
                    Self::collect_static_tail_resume_value_captures(field, bound, captures)?;
                }
                Some(())
            }
            ExprKind::Ascription { expr, .. } => {
                Self::collect_static_tail_resume_value_captures(expr, bound, captures)
            }
            _ => None,
        }
    }
}
