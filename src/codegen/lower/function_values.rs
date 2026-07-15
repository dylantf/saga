use std::collections::HashMap;
use std::ops::{Deref, DerefMut};

use crate::ast::{self, Decl, Expr, ExprKind, Pat, Stmt};
use crate::codegen::cerl::{CArm, CExpr, CLit, CPat};
use crate::codegen::runtime_shape::{CallableAbi, EvidenceAbi};

use super::evidence;
use super::util::{self, collect_ctor_call_with_head, collect_effect_call_expr};
use super::{EvidenceFrame, Lowerer};

fn direct_lambda_arity(expr: &Expr) -> Option<usize> {
    let ExprKind::Lambda { params, body } = &expr.kind else {
        return None;
    };
    let mut arity = params.len();
    let mut current = body.as_ref();
    while let ExprKind::Lambda {
        params,
        body: nested_body,
    } = &current.kind
    {
        arity += params.len();
        current = nested_body.as_ref();
    }
    Some(arity)
}

/// Owns the contextual function-value planning pass. It borrows lowering's
/// semantic metadata, but all mutations performed by this type are ABI-plan
/// mutations; Core emission remains on `Lowerer` below.
struct EffectAbiPlanner<'lowerer, 'ctx> {
    lowerer: &'lowerer mut Lowerer<'ctx>,
}

impl<'lowerer, 'ctx> Deref for EffectAbiPlanner<'lowerer, 'ctx> {
    type Target = Lowerer<'ctx>;

    fn deref(&self) -> &Self::Target {
        self.lowerer
    }
}

impl DerefMut for EffectAbiPlanner<'_, '_> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.lowerer
    }
}

impl<'a> Lowerer<'a> {
    pub(super) fn plan_contextual_function_value_abis(&mut self, program: &[Decl]) {
        EffectAbiPlanner { lowerer: self }.plan_program(program);
    }
}

impl EffectAbiPlanner<'_, '_> {
    /// Complete the function-value portion of the effect ABI plan before Core
    /// lowering begins. The call classifier owns declaration and call ABIs;
    /// this second pass owns contextual value boundaries, whose expected type
    /// comes from the declaration that consumes the value rather than from the
    /// expression's already-instantiated occurrence type.
    fn plan_program(&mut self, program: &[Decl]) {
        for decl in program {
            self.plan_contextual_decl(decl);
        }
    }

    fn plan_contextual_decl(&mut self, decl: &Decl) {
        match decl {
            Decl::FunBinding {
                name, body, params, ..
            } => {
                let expected = self
                    .check_result
                    .env
                    .get(name)
                    .map(|scheme| self.check_result.sub.apply(&scheme.ty))
                    .and_then(|ty| Self::return_type_after_params(&ty, params.len()));
                self.plan_contextual_expr(body, expected.as_ref());
            }
            Decl::Let { value, .. } => self.plan_contextual_expr(value, None),
            Decl::ImplDef { methods, .. } => {
                for method in methods {
                    self.plan_contextual_expr(&method.node.body, None);
                }
            }
            Decl::HandlerDef { body, .. } => {
                for arm in &body.arms {
                    self.plan_contextual_expr(&arm.node.body, None);
                    if let Some(finally) = &arm.node.finally_block {
                        self.plan_contextual_expr(finally, None);
                    }
                }
                if let Some(return_clause) = &body.return_clause {
                    self.plan_contextual_expr(&return_clause.body, None);
                }
            }
            Decl::DictConstructor {
                super_dicts,
                methods,
                method_effects,
                method_open_rows,
                impl_effects,
                ..
            } => {
                for super_dict in super_dicts {
                    self.plan_contextual_expr(super_dict, None);
                }
                for (idx, method) in methods.iter().enumerate() {
                    let (is_cps, static_effects, is_open_row) = self.method_cps_shape(
                        method,
                        method_effects,
                        method_open_rows,
                        impl_effects,
                        idx,
                    );
                    if is_cps {
                        let user_arity = self
                            .semantic_type_at_node(method.id)
                            .filter(|ty| matches!(ty, crate::typechecker::Type::Fun(..)))
                            .map(|ty| util::arity_and_effects_from_type(ty).0)
                            .or_else(|| direct_lambda_arity(method))
                            .expect("dictionary method is missing its callable arity");
                        let abi = CallableAbi::cps(
                            user_arity,
                            EvidenceAbi::new(static_effects, is_open_row),
                        );
                        self.effect_abi_plan.record_function_value_boundary(
                            method.id,
                            abi.clone(),
                            abi,
                        );
                    }
                    self.plan_contextual_expr(method, None);
                }
            }
            _ => {}
        }
    }

    fn return_type_after_params(
        ty: &crate::typechecker::Type,
        param_count: usize,
    ) -> Option<crate::typechecker::Type> {
        let mut current = ty;
        for _ in 0..param_count {
            let crate::typechecker::Type::Fun(_, result, _) = current else {
                return None;
            };
            current = result;
        }
        Some(current.clone())
    }

    fn collect_contextual_app(expr: &Expr) -> (&Expr, Vec<&Expr>) {
        let mut args = Vec::new();
        let mut head = expr;
        while let ExprKind::App { func, arg } = &head.kind {
            args.push(arg.as_ref());
            head = func.as_ref();
        }
        args.reverse();
        (head, args)
    }

    fn expected_contextual_arg_types(
        &self,
        head: &Expr,
        arg_count: usize,
    ) -> Option<Vec<crate::typechecker::Type>> {
        if self.resolved.get(&head.id).is_some_and(|resolved| {
            matches!(
                resolved.kind,
                crate::codegen::resolve::ResolvedCodegenKind::Intrinsic { .. }
            )
        }) {
            // Intrinsics own their callback invocation convention. For
            // example `catch_panic` invokes its already-handled thunk as a
            // plain BEAM function even though its source declaration carries
            // an open row. Its specialized occurrence type, not the generic
            // declaration ABI, governs that compiler-native bridge.
            return None;
        }
        match &head.kind {
            ExprKind::Var { name } | ExprKind::QualifiedName { name, .. } => self
                .resolved_fun_info(head.id, name)
                .map(|info| info.expected_arg_types(arg_count)),
            ExprKind::DictMethodAccess {
                trait_name,
                method_index,
                ..
            } => self
                .trait_info(trait_name)
                .and_then(|info| info.methods.get(*method_index))
                .map(|method| method.param_types.iter().take(arg_count).cloned().collect()),
            _ => self.semantic_type_at_node(head.id).map(|ty| {
                util::param_types_from_type(ty)
                    .into_iter()
                    .take(arg_count)
                    .collect()
            }),
        }
    }

    fn plan_contextual_callable_boundary(
        &mut self,
        expr: &Expr,
        expected_ty: &crate::typechecker::Type,
    ) {
        if !matches!(expected_ty, crate::typechecker::Type::Fun(..)) {
            return;
        }
        let expected =
            CallableAbi::from_type(expected_ty, |effects| self.canonicalize_effects(effects));
        let inferred = self
            .planned_function_value(expr.id)
            .and_then(|value| value.inferred().cloned());
        let literal = matches!(expr.kind, ExprKind::Lambda { .. })
            || Lowerer::is_eta_reduced_effect_expr(expr);
        let implementation = if literal {
            let evidence = match (
                expected.evidence.as_ref(),
                inferred.as_ref().and_then(|abi| abi.evidence.as_ref()),
            ) {
                (None, None) => None,
                (Some(evidence), None) | (None, Some(evidence)) => Some(evidence.clone()),
                (Some(expected), Some(inferred)) => {
                    Some(EvidenceAbi::for_lambda_boundary(expected, inferred))
                }
            };
            CallableAbi::from_parts(expected.user_arity, evidence)
        } else {
            self.callable_abi_from_partial_app(expr)
                .or_else(|| self.callable_abi_from_named_function_value(expr))
                .or(inferred)
                .or_else(|| {
                    self.expr_cps_function_shape(expr)
                        .map(|evidence| CallableAbi::cps(expected.user_arity, evidence))
                })
                .or_else(|| self.callable_abi_from_dict_method_access(expr))
                .unwrap_or_else(|| CallableAbi::pure(expected.user_arity))
        };
        if implementation.evidence.is_some() || expected.evidence.is_some() {
            self.effect_abi_plan
                .record_function_value_boundary(expr.id, implementation, expected);
        }
    }

    fn plan_effect_callback_abis(
        &mut self,
        node_id: crate::ast::NodeId,
        op_name: &str,
        qualifier: Option<&str>,
        args: &[&Expr],
    ) {
        let Some(effect_name) = self.resolved_effect_call_name(node_id, op_name, qualifier) else {
            return;
        };
        let Some(op_info) = self
            .effect_defs
            .get(&effect_name)
            .and_then(|effect| effect.ops.get(op_name))
            .cloned()
        else {
            return;
        };
        for (source_idx, arg) in args.iter().enumerate() {
            let absorbed = op_info.param_absorbed_effects.get(&source_idx);
            let has_open_row = op_info.param_open_rows.contains(&source_idx);
            if absorbed.is_none() && !has_open_row {
                continue;
            }
            let actual_callback_effects = self
                .expr_cps_function_shape(arg)
                .map(|shape| shape.static_slots().to_vec())
                .unwrap_or_default();
            let mut static_effects = Vec::new();
            let mut uses_native_callback_context = false;
            for effect in absorbed.into_iter().flatten() {
                if self
                    .effect_handler_ops(std::slice::from_ref(effect))
                    .is_empty()
                {
                    continue;
                }
                if self.beam_native_handler_for_effect(effect).is_some() {
                    uses_native_callback_context = true;
                    continue;
                }
                let concrete = if actual_callback_effects.contains(effect) {
                    effect.clone()
                } else {
                    let family = crate::typechecker::applied_effect_family(effect);
                    let matches: Vec<&String> = actual_callback_effects
                        .iter()
                        .filter(|actual| {
                            crate::typechecker::applied_effect_family(actual) == family
                        })
                        .collect();
                    if matches.len() == 1 {
                        matches[0].clone()
                    } else {
                        effect.clone()
                    }
                };
                static_effects.push(concrete);
            }
            static_effects.sort();
            static_effects.dedup();
            let is_open = has_open_row && !uses_native_callback_context;
            if static_effects.is_empty() && !is_open {
                continue;
            }
            let user_arity = self
                .semantic_type_at_node(arg.id)
                .filter(|ty| matches!(ty, crate::typechecker::Type::Fun(..)))
                .map(|ty| util::arity_and_effects_from_type(ty).0)
                .or_else(|| direct_lambda_arity(arg))
                .expect("effect callback is missing its callable arity");
            let abi = CallableAbi::cps(user_arity, EvidenceAbi::new(static_effects, is_open));
            self.effect_abi_plan
                .record_function_value_boundary(arg.id, abi.clone(), abi);
        }
    }

    fn plan_contextual_stmt(
        &mut self,
        stmt: &Stmt,
        expected_result: Option<&crate::typechecker::Type>,
    ) {
        match stmt {
            Stmt::Let { pattern, value, .. } => {
                let expected = self
                    .let_pat_resolved_type(pattern)
                    .or_else(|| self.semantic_type_at_node(value.id).cloned());
                self.plan_contextual_expr(value, expected.as_ref());
            }
            Stmt::LetFun { body, guard, .. } => {
                if let Some(guard) = guard {
                    self.plan_contextual_expr(guard, None);
                }
                self.plan_contextual_expr(body, None);
            }
            Stmt::Expr(expr) => self.plan_contextual_expr(expr, expected_result),
        }
    }

    fn plan_contextual_expr(
        &mut self,
        expr: &Expr,
        expected_ty: Option<&crate::typechecker::Type>,
    ) {
        if let Some(expected_ty) = expected_ty {
            self.plan_contextual_callable_boundary(expr, expected_ty);
        }

        match &expr.kind {
            ExprKind::App { .. } => {
                if let Some((head, op_name, qualifier, args)) = collect_effect_call_expr(expr) {
                    self.plan_effect_callback_abis(head.id, op_name, qualifier, &args);
                    for arg in args {
                        self.plan_contextual_expr(arg, None);
                    }
                    return;
                }
                if let Some(expected_ty) = expected_ty
                    && let Some((head, ctor_name, args)) = collect_ctor_call_with_head(expr)
                {
                    let resolved = self.resolved_constructor_name_for(head.id, ctor_name);
                    if let Some(arg_types) =
                        self.constructor_arg_types_from_expected(&resolved, expected_ty)
                    {
                        for (arg, arg_ty) in args.iter().zip(arg_types.iter()) {
                            self.plan_contextual_expr(arg, Some(arg_ty));
                        }
                        return;
                    }
                }
                let (head, args) = Self::collect_contextual_app(expr);
                let expected_args = self.expected_contextual_arg_types(head, args.len());
                self.plan_contextual_expr(head, None);
                for (index, arg) in args.iter().enumerate() {
                    self.plan_contextual_expr(
                        arg,
                        expected_args.as_ref().and_then(|types| types.get(index)),
                    );
                }
            }
            ExprKind::Lambda { params, body } => {
                let callable_ty = expected_ty
                    .cloned()
                    .or_else(|| self.semantic_type_at_node(expr.id).cloned());
                let body_expected = callable_ty
                    .as_ref()
                    .and_then(|ty| Self::return_type_after_params(ty, params.len()));
                self.plan_contextual_expr(body, body_expected.as_ref());
            }
            ExprKind::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => {
                self.plan_contextual_expr(cond, None);
                self.plan_contextual_expr(then_branch, expected_ty);
                self.plan_contextual_expr(else_branch, expected_ty);
            }
            ExprKind::Case {
                scrutinee, arms, ..
            } => {
                self.plan_contextual_expr(scrutinee, None);
                for arm in arms {
                    if let Some(guard) = &arm.node.guard {
                        self.plan_contextual_expr(guard, None);
                    }
                    self.plan_contextual_expr(&arm.node.body, expected_ty);
                }
            }
            ExprKind::Block { stmts, .. } => {
                let last = stmts.len().saturating_sub(1);
                for (index, stmt) in stmts.iter().enumerate() {
                    self.plan_contextual_stmt(
                        &stmt.node,
                        (index == last).then_some(expected_ty).flatten(),
                    );
                }
            }
            ExprKind::Tuple { elements } => {
                let expected_elements = match expected_ty {
                    Some(crate::typechecker::Type::Con(name, args))
                        if crate::typechecker::bare_type_name(name) == "Tuple" =>
                    {
                        Some(args)
                    }
                    _ => None,
                };
                for (index, element) in elements.iter().enumerate() {
                    self.plan_contextual_expr(
                        element,
                        expected_elements.and_then(|types| types.get(index)),
                    );
                }
            }
            ExprKind::RecordCreate {
                name,
                fields,
                record_name,
            } => {
                let field_types = expected_ty
                    .and_then(|ty| self.record_field_types_from_expected(ty))
                    .or_else(|| self.record_field_types_by_name(record_name.as_deref(), name));
                for (field, _, value) in fields {
                    self.plan_contextual_expr(
                        value,
                        field_types.as_ref().and_then(|types| types.get(field)),
                    );
                }
            }
            ExprKind::AnonRecordCreate { fields } => {
                let field_types =
                    expected_ty.and_then(|ty| self.record_field_types_from_expected(ty));
                for (field, _, value) in fields {
                    self.plan_contextual_expr(
                        value,
                        field_types.as_ref().and_then(|types| types.get(field)),
                    );
                }
            }
            ExprKind::RecordBuild { fields, .. } => {
                for (_, _, value) in fields {
                    self.plan_contextual_expr(value, None);
                }
            }
            ExprKind::RecordUpdate { record, fields, .. } => {
                self.plan_contextual_expr(record, expected_ty);
                let field_types =
                    expected_ty.and_then(|ty| self.record_field_types_from_expected(ty));
                for (field, _, value) in fields {
                    self.plan_contextual_expr(
                        value,
                        field_types.as_ref().and_then(|types| types.get(field)),
                    );
                }
            }
            ExprKind::EffectCall {
                name,
                qualifier,
                args,
            } => {
                let args: Vec<&Expr> = args.iter().collect();
                self.plan_effect_callback_abis(expr.id, name, qualifier.as_deref(), &args);
                for arg in args {
                    self.plan_contextual_expr(arg, None);
                }
            }
            ExprKind::With {
                expr: handled,
                handler,
            } => {
                self.plan_contextual_expr(handled, expected_ty);
                if let ast::Handler::Inline { items, .. } = handler.as_ref() {
                    for item in items {
                        match &item.node {
                            ast::HandlerItem::Arm(arm) | ast::HandlerItem::Return(arm) => {
                                self.plan_contextual_expr(&arm.body, None);
                                if let Some(finally) = &arm.finally_block {
                                    self.plan_contextual_expr(finally, None);
                                }
                            }
                            ast::HandlerItem::Named(_) => {}
                        }
                    }
                }
            }
            ExprKind::Do {
                bindings,
                success,
                else_arms,
                ..
            } => {
                for (_, value) in bindings {
                    self.plan_contextual_expr(value, None);
                }
                self.plan_contextual_expr(success, expected_ty);
                for arm in else_arms {
                    if let Some(guard) = &arm.node.guard {
                        self.plan_contextual_expr(guard, None);
                    }
                    self.plan_contextual_expr(&arm.node.body, expected_ty);
                }
            }
            ExprKind::Receive {
                arms, after_clause, ..
            } => {
                for arm in arms {
                    if let Some(guard) = &arm.node.guard {
                        self.plan_contextual_expr(guard, None);
                    }
                    self.plan_contextual_expr(&arm.node.body, expected_ty);
                }
                if let Some((timeout, body)) = after_clause {
                    self.plan_contextual_expr(timeout, None);
                    self.plan_contextual_expr(body, expected_ty);
                }
            }
            ExprKind::Ascription { expr: inner, .. } => {
                let annotated = self.semantic_type_at_node(expr.id).cloned();
                self.plan_contextual_expr(inner, annotated.as_ref().or(expected_ty));
            }
            ExprKind::BinOp { left, right, .. } => {
                self.plan_contextual_expr(left, None);
                self.plan_contextual_expr(right, None);
            }
            ExprKind::UnaryMinus { expr: inner }
            | ExprKind::FieldAccess { expr: inner, .. }
            | ExprKind::Resume { value: inner } => self.plan_contextual_expr(inner, None),
            ExprKind::BitString { segments } => {
                for segment in segments {
                    self.plan_contextual_expr(&segment.value, None);
                    if let Some(size) = &segment.size {
                        self.plan_contextual_expr(size, None);
                    }
                }
            }
            ExprKind::HandlerExpr { body } => {
                for arm in &body.arms {
                    self.plan_contextual_expr(&arm.node.body, None);
                    if let Some(finally) = &arm.node.finally_block {
                        self.plan_contextual_expr(finally, None);
                    }
                }
                if let Some(return_clause) = &body.return_clause {
                    self.plan_contextual_expr(&return_clause.body, None);
                }
            }
            ExprKind::DictMethodAccess { dict, .. } | ExprKind::DictSuperAccess { dict, .. } => {
                self.plan_contextual_expr(dict, None)
            }
            ExprKind::ForeignCall { args, .. } => {
                for arg in args {
                    self.plan_contextual_expr(arg, None);
                }
            }
            ExprKind::Lit { .. }
            | ExprKind::Var { .. }
            | ExprKind::Constructor { .. }
            | ExprKind::QualifiedName { .. }
            | ExprKind::DictRef { .. } => {}
            ExprKind::Pipe { .. }
            | ExprKind::BinOpChain { .. }
            | ExprKind::PipeBack { .. }
            | ExprKind::ComposeForward { .. }
            | ExprKind::Cons { .. }
            | ExprKind::ListLit { .. }
            | ExprKind::StringInterp { .. }
            | ExprKind::ListComprehension { .. } => {
                unreachable!("surface expression reached contextual ABI planning")
            }
        }
    }
}

impl<'a> Lowerer<'a> {
    fn lower_curried_lambda_for_expected_arity(
        &mut self,
        expr: &Expr,
        expected_ty: &crate::typechecker::Type,
    ) -> Option<CExpr> {
        let (expected_arity, effects) = util::arity_and_effects_from_type(expected_ty);
        if expected_arity == 0 || !effects.is_empty() {
            return None;
        }
        let actual_arity = direct_lambda_arity(expr)?;
        if expected_arity >= actual_arity {
            return None;
        }

        let ExprKind::Lambda { params, body } = &expr.kind else {
            return None;
        };
        if params.len() != expected_arity
            || !params.iter().all(|p| {
                matches!(
                    p,
                    Pat::Var { .. }
                        | Pat::Wildcard { .. }
                        | Pat::Lit {
                            value: ast::Lit::Unit,
                            ..
                        }
                )
            })
        {
            return None;
        }

        let param_vars = super::pats::lower_params(params);
        Some(CExpr::Fun(
            param_vars,
            Box::new(self.lower_expr_value(body)),
        ))
    }

    fn lower_constructor_function_value(
        &mut self,
        name: &str,
        expected_ty: &crate::typechecker::Type,
    ) -> Option<CExpr> {
        let mut params = Vec::new();
        let mut current = expected_ty;
        while let crate::typechecker::Type::Fun(_, ret, _) = current {
            params.push(self.fresh());
            current = ret;
        }
        if params.is_empty() {
            return None;
        }

        let bare = name.rsplit('.').next().unwrap_or(name);
        let atom =
            util::mangle_ctor_atom(name, &self.constructor_atoms, self.handler_origin_module());
        let value = if bare == "Cons" && params.len() == 2 {
            CExpr::Cons(
                Box::new(CExpr::Var(params[0].clone())),
                Box::new(CExpr::Var(params[1].clone())),
            )
        } else {
            let mut elems = vec![CExpr::Lit(CLit::Atom(atom))];
            elems.extend(params.iter().map(|param| CExpr::Var(param.clone())));
            CExpr::Tuple(elems)
        };

        Some(
            params
                .into_iter()
                .rev()
                .fold(value, |body, param| CExpr::Fun(vec![param], Box::new(body))),
        )
    }

    pub(super) fn cps_function_shape_from_type(
        &self,
        ty: &crate::typechecker::Type,
    ) -> Option<EvidenceAbi> {
        CallableAbi::from_type(ty, |effects| self.canonicalize_effects(effects)).cps_evidence()
    }

    pub(super) fn expr_cps_function_shape(&self, expr: &Expr) -> Option<EvidenceAbi> {
        self.planned_function_value(expr.id)
            .and_then(|plan| plan.inferred())
            .and_then(|abi| abi.evidence.clone())
            .or_else(|| {
                self.check_result
                    .resolved_type_for_node(expr.id)
                    .and_then(|ty| self.cps_function_shape_from_type(&ty))
            })
    }

    /// If `expr` is a partial application of a CPS-shaped function (effects
    /// or open row), returns the resulting closure's runtime CPS shape.
    /// Used to bridge the gap between a value's static type — which may
    /// have been narrowed to pure via row-variable substitution at the
    /// application site — and its actual runtime convention, which is
    /// fixed by the head function's compiled signature.
    ///
    /// Example: `wrap : (Unit -> Unit needs {..e}) -> Unit -> Unit needs {..e}`.
    /// Applying `wrap pure_fn` resolves `..e` to closed empty so the result
    /// type is `Unit -> Unit` (pure), but at runtime the partial-app emits
    /// a closure with the CPS calling convention (`(user_args, _Evidence,
    /// _ReturnK)`) because `wrap` itself was compiled that way.
    ///
    /// Returns `None` for non-App expressions, saturated calls, calls
    /// whose head isn't a known CPS function, and calls whose head can't
    /// be resolved to a `FunInfo` entry.
    fn callable_abi_from_partial_app(&self, expr: &Expr) -> Option<CallableAbi> {
        fn collect_spine(e: &Expr) -> (&Expr, usize) {
            match &e.kind {
                ExprKind::App { func, .. } => {
                    let (head, n) = collect_spine(func);
                    (head, n + 1)
                }
                _ => (e, 0),
            }
        }
        let (head, supplied) = collect_spine(expr);
        if supplied == 0 {
            return None;
        }
        let info = match &head.kind {
            ExprKind::Var { name, .. } => self.resolved_fun_info(head.id, name)?,
            ExprKind::QualifiedName { module, name, .. } => {
                let qualified = format!("{}.{}", module, name);
                self.resolved_fun_info(head.id, &qualified)?
            }
            _ => return None,
        };
        let is_cps = info.abi.evidence.is_some();
        if !is_cps {
            return None;
        }
        // FunInfo.arity counts Evidence + ReturnK; user arity excludes them.
        let head_user_arity = info.abi.user_arity;
        if supplied >= head_user_arity {
            return None;
        }
        Some(CallableAbi::cps(
            head_user_arity - supplied,
            info.abi
                .evidence
                .clone()
                .expect("CPS FunInfo missing evidence"),
        ))
    }

    /// Return the declaration ABI for a named function used as a value.
    ///
    /// Its occurrence type may contain effects absorbed while unifying it
    /// with an open callback slot. Those effects describe the call-site
    /// boundary, not the function's compiled implementation layout.
    fn callable_abi_from_named_function_value(&self, expr: &Expr) -> Option<CallableAbi> {
        match &expr.kind {
            ExprKind::Var { name } => self
                .resolved_fun_info(expr.id, name)
                .map(|info| info.abi.clone()),
            ExprKind::QualifiedName { module, name, .. } => {
                let qualified = format!("{module}.{name}");
                self.resolved_fun_info(expr.id, &qualified)
                    .map(|info| info.abi.clone())
            }
            _ => None,
        }
    }

    /// If `expr` is a `DictMethodAccess` for a trait method that carries
    /// effects, return its runtime CPS shape. Synthesized `DictMethodAccess`
    /// nodes have fresh `NodeId`s with no recorded type, so the type-based
    /// shape lookup misses them. Source the effects from the trait method's
    /// effect signature directly. Without this, a trait method passed as a
    /// first-class value (e.g. `run decode n`) falls through to the pure
    /// adapter and the resulting wrapper drops `_Evidence`/`_ReturnK` when
    /// calling the underlying CPS-shaped method.
    fn callable_abi_from_dict_method_access(&self, expr: &Expr) -> Option<CallableAbi> {
        let ExprKind::DictMethodAccess {
            trait_name,
            method_index,
            ..
        } = &expr.kind
        else {
            return None;
        };
        let info = self.trait_info(trait_name)?;
        let method = info.methods.get(*method_index)?;
        let effects = self.canonicalize_effects(method.effect_sig.effects.clone());
        let is_open_row = method.effect_sig.is_open_row;
        if effects.is_empty() && !is_open_row {
            return None;
        }
        Some(CallableAbi::cps(
            method.param_types.len(),
            EvidenceAbi::new(effects, is_open_row),
        ))
    }

    fn wrap_pure_function_value_as_cps_adapter(
        &mut self,
        expr: &Expr,
        _expected_ty: &crate::typechecker::Type,
    ) -> CExpr {
        let user_arity = self
            .planned_function_value_boundary(expr.id)
            .map(|abi| abi.user_arity)
            .unwrap_or_else(|| {
                panic!(
                    "internal ABI planning error: missing pure-to-CPS adapter boundary for {:?}",
                    expr.id
                )
            });
        let fun_var = self.fresh();
        let result_var = self.fresh();
        let mut params = Vec::with_capacity(user_arity + 2);
        let mut apply_args = Vec::with_capacity(user_arity);
        for _ in 0..user_arity {
            let param = self.fresh();
            apply_args.push(CExpr::Var(param.clone()));
            params.push(param);
        }
        params.push("_Evidence".to_string());
        params.push("_ReturnK".to_string());

        let pure_fun = self.lower_expr_value(expr);
        let pure_call = CExpr::Apply(Box::new(CExpr::Var(fun_var.clone())), apply_args);
        let return_call = CExpr::Apply(
            Box::new(CExpr::Var("_ReturnK".to_string())),
            vec![CExpr::Var(result_var.clone())],
        );
        let adapter = CExpr::Fun(
            params,
            Box::new(CExpr::Let(
                result_var,
                Box::new(pure_call),
                Box::new(return_call),
            )),
        );
        CExpr::Let(fun_var, Box::new(pure_fun), Box::new(adapter))
    }

    /// Adapt a CPS-shaped runtime value to a pure-shape callable. The
    /// inverse of `wrap_pure_function_value_as_cps_adapter`: needed when
    /// the type system has narrowed a CPS function's row variable to
    /// closed-empty (e.g. via let annotation or by saturating a callback
    /// argument with a pure function), but the underlying value is the
    /// partial application of a row-polymorphic function compiled with
    /// the CPS calling convention.
    ///
    /// The adapter takes the pure shape's user args, invokes the CPS
    /// value with an empty evidence tuple and an identity `_ReturnK`,
    /// and returns the result. Empty evidence is safe because the static
    /// narrowing means no handler effects are actually used by this
    /// invocation; if the underlying function tries to look up evidence,
    /// the type system would have rejected the program upstream.
    fn wrap_cps_function_value_as_pure_adapter(
        &mut self,
        expr: &Expr,
        _expected_ty: &crate::typechecker::Type,
    ) -> CExpr {
        let user_arity = self
            .planned_function_value_boundary(expr.id)
            .map(|abi| abi.user_arity)
            .unwrap_or_else(|| {
                panic!(
                    "internal ABI planning error: missing CPS-to-pure adapter boundary for {:?}",
                    expr.id
                )
            });
        let fun_var = self.fresh();
        let identity_arg = self.fresh();
        let mut params = Vec::with_capacity(user_arity);
        let mut apply_args = Vec::with_capacity(user_arity + 2);
        for _ in 0..user_arity {
            let p = self.fresh();
            apply_args.push(CExpr::Var(p.clone()));
            params.push(p);
        }
        apply_args.push(CExpr::Tuple(vec![]));
        let identity_k = CExpr::Fun(
            vec![identity_arg.clone()],
            Box::new(CExpr::Var(identity_arg)),
        );
        apply_args.push(identity_k);

        let actual_fun = self.lower_expr_value(expr);
        let call = CExpr::Apply(Box::new(CExpr::Var(fun_var.clone())), apply_args);
        let adapter = CExpr::Fun(params, Box::new(call));
        CExpr::Let(fun_var, Box::new(actual_fun), Box::new(adapter))
    }

    fn adapt_cps_function_value_to_expected_shape(
        &mut self,
        expr: &Expr,
        _expected_ty: &crate::typechecker::Type,
        actual_shape: EvidenceAbi,
    ) -> CExpr {
        let boundary_abi = self
            .planned_function_value_boundary(expr.id)
            .cloned()
            .unwrap_or_else(|| {
                panic!(
                    "internal ABI planning error: missing CPS adapter boundary for {:?}",
                    expr.id
                )
            });
        let user_arity = boundary_abi.user_arity;
        let fun_var = self.fresh();
        let ev_var = self.fresh();
        let mut params = Vec::with_capacity(user_arity + 2);
        let mut apply_args = Vec::with_capacity(user_arity + 2);
        for _ in 0..user_arity {
            let param = self.fresh();
            apply_args.push(CExpr::Var(param.clone()));
            params.push(param);
        }
        params.push("_Evidence".to_string());
        params.push("_ReturnK".to_string());

        let expected_abi = boundary_abi
            .evidence
            .expect("CPS adapter boundary missing evidence ABI");
        let reframe_plan = crate::codegen::runtime_shape::EvidenceReframePlan::between(
            &expected_abi,
            &actual_shape,
        );
        apply_args.push(CExpr::Var(ev_var.clone()));
        apply_args.push(CExpr::Var("_ReturnK".to_string()));

        let actual_fun = self.lower_expr_value(expr);
        // Reframe from the callback slot's ABI into the implementation ABI.
        // This is required for open implementations too: two open rows may
        // have different static prefixes, and forwarding the boundary frame
        // unchanged would make the implementation read the wrong slot.
        let narrowed_evidence =
            evidence::apply_reframe(CExpr::Var("_Evidence".to_string()), &reframe_plan);
        let call = CExpr::Apply(Box::new(CExpr::Var(fun_var.clone())), apply_args);
        let adapter = CExpr::Fun(
            params,
            Box::new(CExpr::Let(
                ev_var,
                Box::new(narrowed_evidence),
                Box::new(call),
            )),
        );
        CExpr::Let(fun_var, Box::new(actual_fun), Box::new(adapter))
    }

    fn lower_cps_function_value_with_expected_shape(
        &mut self,
        expr: &Expr,
        expected_ty: &crate::typechecker::Type,
        expected_shape: EvidenceAbi,
    ) -> CExpr {
        if matches!(expr.kind, ExprKind::Lambda { .. }) || Self::is_eta_reduced_effect_expr(expr) {
            let implementation = self
                .planned_function_value_implementation(expr.id)
                .unwrap_or_else(|| {
                    panic!(
                        "internal ABI planning error: missing contextual callable ABI for {:?}",
                        expr.id
                    )
                });
            assert_eq!(
                implementation.user_arity,
                CallableAbi::from_type(expected_ty, |effects| self.canonicalize_effects(effects))
                    .user_arity,
                "internal ABI planning error: contextual callable arity disagrees with its boundary"
            );
            assert!(
                implementation.evidence.is_some(),
                "internal ABI planning error: CPS callback has a pure implementation ABI"
            );
            assert_eq!(
                self.planned_function_value_boundary(expr.id)
                    .and_then(|abi| abi.evidence.as_ref()),
                Some(&expected_shape),
                "internal ABI planning error: CPS callback boundary disagrees with lowering"
            );
            let ce = self
                .lower_eta_reduced_effect_expr(expr)
                .unwrap_or_else(|| self.lower_expr_value(expr));
            return ce;
        }

        // Determine the actual runtime shape. Partial applications must use
        // the compiled head's ABI even when their resolved occurrence type has
        // narrowed or closed its row; other values use the resolved type, with
        // a trait-dictionary fallback for synthesized method-access nodes.
        let expected_abi =
            CallableAbi::from_type(expected_ty, |effects| self.canonicalize_effects(effects));
        let computed_actual_abi = self
            // A partial application's runtime ABI is fixed by the compiled
            // head function, not by the occurrence type after its row has
            // been instantiated. In particular, partially applying
            // `route : ... needs {Skip, ..e}` must leave a closure whose
            // static prefix is `Skip` plus an open tail; the resolved result
            // type may misleadingly look like a closed union of every effect
            // supplied at this call site.
            .callable_abi_from_partial_app(expr)
            .or_else(|| self.callable_abi_from_named_function_value(expr))
            .or_else(|| {
                self.planned_function_value(expr.id)
                    .and_then(|plan| plan.inferred().cloned())
            })
            .or_else(|| {
                self.expr_cps_function_shape(expr)
                    .map(|evidence| CallableAbi::cps(expected_abi.user_arity, evidence))
            })
            .or_else(|| self.callable_abi_from_dict_method_access(expr))
            .unwrap_or_else(|| CallableAbi::pure(expected_abi.user_arity));
        let planned = self.planned_function_value(expr.id).unwrap_or_else(|| {
            panic!(
                "internal ABI planning error: missing function-value boundary for {:?}",
                expr.id
            )
        });
        let contextual = planned
            .contextual()
            .expect("contextual function-value plan is missing its boundary pair");
        let actual_abi = contextual.implementation().clone();
        let boundary_abi = contextual.boundary();
        assert_eq!(
            &expected_abi, boundary_abi,
            "internal ABI planning error: lowering expected ABI disagrees with planned boundary"
        );
        assert_eq!(
            computed_actual_abi, actual_abi,
            "internal ABI planning error: lowering implementation ABI disagrees with the plan"
        );

        if let Some(actual_shape) = actual_abi.evidence {
            self.adapt_cps_function_value_to_expected_shape(expr, expected_ty, actual_shape)
        } else {
            self.wrap_pure_function_value_as_cps_adapter(expr, expected_ty)
        }
    }

    pub(super) fn lower_expr_value_with_expected_type(
        &mut self,
        expr: &Expr,
        expected_ty: Option<&crate::typechecker::Type>,
    ) -> CExpr {
        if let Some(expected_ty) = expected_ty {
            if let ExprKind::Constructor { name, .. } = &expr.kind
                && matches!(expected_ty, crate::typechecker::Type::Fun(_, _, _))
                && let Some(ctor_fun) = {
                    let ctor_name = self.resolved_constructor_name_for(expr.id, name);
                    self.lower_constructor_function_value(&ctor_name, expected_ty)
                }
            {
                return ctor_fun;
            }

            if let Some(curried_lambda) =
                self.lower_curried_lambda_for_expected_arity(expr, expected_ty)
            {
                return curried_lambda;
            }

            if let Some((head, ctor_name, args)) = collect_ctor_call_with_head(expr) {
                let resolved_ctor = self.resolved_constructor_name_for(head.id, ctor_name);
                let bare = crate::typechecker::bare_type_name(match expected_ty {
                    crate::typechecker::Type::Con(name, _) => name,
                    _ => "",
                });
                if bare == "List"
                    && let crate::typechecker::Type::Con(_, type_args) = expected_ty
                    && let Some(elem_ty) = type_args.first()
                {
                    match (
                        resolved_ctor.rsplit('.').next().unwrap_or(&resolved_ctor),
                        args.as_slice(),
                    ) {
                        ("Nil", []) => return CExpr::Nil,
                        ("Cons", [head, tail]) => {
                            let head_var = self.fresh();
                            let tail_var = self.fresh();
                            let head_ce =
                                self.lower_expr_value_with_expected_type(head, Some(elem_ty));
                            let tail_ce =
                                self.lower_expr_value_with_expected_type(tail, Some(expected_ty));
                            return CExpr::Let(
                                head_var.clone(),
                                Box::new(head_ce),
                                Box::new(CExpr::Let(
                                    tail_var.clone(),
                                    Box::new(tail_ce),
                                    Box::new(CExpr::Cons(
                                        Box::new(CExpr::Var(head_var)),
                                        Box::new(CExpr::Var(tail_var)),
                                    )),
                                )),
                            );
                        }
                        _ => {}
                    }
                }

                if bare != "List"
                    && let Some(arg_tys) =
                        self.constructor_arg_types_from_expected(&resolved_ctor, expected_ty)
                {
                    let mut vars = Vec::new();
                    let mut bindings = Vec::new();
                    for (idx, arg) in args.iter().enumerate() {
                        let var = self.fresh();
                        let child_expected = arg_tys.get(idx);
                        let val = self.lower_expr_value_with_expected_type(arg, child_expected);
                        vars.push(var.clone());
                        bindings.push((var, val));
                    }
                    let atom = util::mangle_ctor_atom(
                        &resolved_ctor,
                        &self.constructor_atoms,
                        self.handler_origin_module(),
                    );
                    let mut elems = vec![CExpr::Lit(CLit::Atom(atom))];
                    elems.extend(vars.iter().map(|v| CExpr::Var(v.clone())));
                    let tuple = CExpr::Tuple(elems);
                    return self.wrap_let_bindings(bindings, tuple);
                }
            }

            if let ExprKind::Tuple { elements, .. } = &expr.kind
                && let crate::typechecker::Type::Con(name, elem_tys) = expected_ty
                && crate::typechecker::bare_type_name(name) == "Tuple"
                && elem_tys.len() == elements.len()
            {
                let mut vars = Vec::new();
                let mut bindings = Vec::new();
                for (elem, elem_ty) in elements.iter().zip(elem_tys.iter()) {
                    let var = self.fresh();
                    let val = self.lower_expr_value_with_expected_type(elem, Some(elem_ty));
                    vars.push(var.clone());
                    bindings.push((var, val));
                }
                let tuple = CExpr::Tuple(vars.iter().map(|v| CExpr::Var(v.clone())).collect());
                return self.wrap_let_bindings(bindings, tuple);
            }

            if let ExprKind::If {
                cond,
                then_branch,
                else_branch,
                ..
            } = &expr.kind
            {
                let cond_var = self.fresh();
                let cond_ce = self.lower_expr_value(cond);
                let then_ce =
                    self.lower_expr_value_with_expected_type(then_branch, Some(expected_ty));
                let else_ce =
                    self.lower_expr_value_with_expected_type(else_branch, Some(expected_ty));
                return CExpr::Let(
                    cond_var.clone(),
                    Box::new(cond_ce),
                    Box::new(CExpr::Case(
                        Box::new(CExpr::Var(cond_var)),
                        vec![
                            CArm {
                                pat: CPat::Lit(CLit::Atom("true".to_string())),
                                guard: None,
                                body: then_ce,
                            },
                            CArm {
                                pat: CPat::Lit(CLit::Atom("false".to_string())),
                                guard: None,
                                body: else_ce,
                            },
                        ],
                    )),
                );
            }

            if let Some(shape) = self.cps_function_shape_from_type(expected_ty) {
                return self.lower_cps_function_value_with_expected_shape(expr, expected_ty, shape);
            }

            // Expected is a pure function type, but the actual expression
            // is a partial application of a CPS-shaped function. The
            // static narrowing (row variable resolved to closed empty)
            // doesn't change the runtime BEAM arity of the partial-app
            // closure — `wrap pure_fn` is still a 3-arg closure even
            // though its inferred type is `Unit -> Unit`. Wrap it so the
            // call site sees the expected pure shape.
            if matches!(expected_ty, crate::typechecker::Type::Fun(_, _, _))
                && let Some(actual_abi) = self.callable_abi_from_partial_app(expr)
            {
                let boundary = CallableAbi::from_type(expected_ty, |effects| {
                    self.canonicalize_effects(effects)
                });
                let planned = self.planned_function_value(expr.id).unwrap_or_else(|| {
                    panic!(
                        "internal ABI planning error: missing pure-boundary adapter ABI for {:?}",
                        expr.id
                    )
                });
                let contextual = planned.contextual().expect("contextual adapter ABI");
                assert_eq!(contextual.implementation(), &actual_abi);
                assert_eq!(contextual.boundary(), &boundary);
                return self.wrap_cps_function_value_as_pure_adapter(expr, expected_ty);
            }

            match &expr.kind {
                ExprKind::RecordCreate {
                    name,
                    fields,
                    record_name,
                } => {
                    let Some(field_tys) = self.record_field_types_from_expected(expected_ty) else {
                        return self.lower_expr_value(expr);
                    };
                    let order = self
                        .record_create_field_order(record_name.as_deref(), expr.id, name)
                        .cloned()
                        .unwrap_or_else(|| {
                            panic!(
                                "codegen: cannot resolve field layout for record `{name}` \
                                 (node {:?}, module `{}`). The record's type could not be \
                                 determined here, so its tuple layout is unknown.",
                                expr.id,
                                self.current_semantic_module_name(),
                            )
                        });
                    let field_map: HashMap<&str, &Expr> =
                        fields.iter().map(|(n, _, e)| (n.as_str(), e)).collect();
                    let mut vars = Vec::new();
                    let mut bindings = Vec::new();
                    for field_name in &order {
                        let var = self.fresh();
                        let field_expr = field_map
                            .get(field_name.as_str())
                            .expect("field missing in RecordCreate");
                        let child_expected = field_tys.get(field_name.as_str());
                        let val =
                            self.lower_expr_value_with_expected_type(field_expr, child_expected);
                        vars.push(var.clone());
                        bindings.push((var, val));
                    }
                    let ctor_name = self
                        .current_record_type_name(expr.id)
                        .and_then(|name| self.canonical_constructor_key_for(name))
                        .unwrap_or_else(|| self.resolved_constructor_name_for(expr.id, name));
                    let atom = util::mangle_ctor_atom(
                        &ctor_name,
                        &self.constructor_atoms,
                        self.handler_origin_module(),
                    );
                    let mut elems = vec![CExpr::Lit(CLit::Atom(atom))];
                    elems.extend(vars.iter().map(|v| CExpr::Var(v.clone())));
                    return self.wrap_let_bindings(bindings, CExpr::Tuple(elems));
                }
                ExprKind::AnonRecordCreate { fields, .. } => {
                    let Some(field_tys) = self.record_field_types_from_expected(expected_ty) else {
                        return self.lower_expr_value(expr);
                    };
                    let names: Vec<&str> = fields.iter().map(|(n, _, _)| n.as_str()).collect();
                    let tag = crate::ast::anon_record_tag(&names);
                    let mut sorted_names: Vec<String> =
                        names.iter().map(|n| n.to_string()).collect();
                    sorted_names.sort();
                    let field_map: HashMap<&str, &Expr> =
                        fields.iter().map(|(n, _, e)| (n.as_str(), e)).collect();
                    let mut vars = Vec::new();
                    let mut bindings = Vec::new();
                    for field_name in &sorted_names {
                        let var = self.fresh();
                        let field_expr = field_map
                            .get(field_name.as_str())
                            .expect("field missing in AnonRecordCreate");
                        let child_expected = field_tys.get(field_name.as_str());
                        let val =
                            self.lower_expr_value_with_expected_type(field_expr, child_expected);
                        vars.push(var.clone());
                        bindings.push((var, val));
                    }
                    let mut elems = vec![CExpr::Lit(CLit::Atom(tag))];
                    elems.extend(vars.iter().map(|v| CExpr::Var(v.clone())));
                    return self.wrap_let_bindings(bindings, CExpr::Tuple(elems));
                }
                _ => {}
            }
        }

        self.lower_expr_value(expr)
    }

    pub(super) fn lower_call_args_with_expected_types(
        &mut self,
        args: &[&Expr],
        param_types: Option<&[crate::typechecker::Type]>,
    ) -> (Vec<String>, Vec<(String, CExpr)>) {
        let mut arg_vars: Vec<String> = Vec::new();
        let mut bindings: Vec<(String, CExpr)> = Vec::new();
        for (i, arg) in args.iter().enumerate() {
            let v = self.fresh();
            let ce = self
                .lower_expr_value_with_expected_type(arg, param_types.and_then(|tys| tys.get(i)));
            arg_vars.push(v.clone());
            bindings.push((v, ce));
        }
        (arg_vars, bindings)
    }

    pub(super) fn lower_call_args(
        &mut self,
        args: &[&Expr],
    ) -> (Vec<String>, Vec<(String, CExpr)>) {
        let mut arg_vars: Vec<String> = Vec::new();
        let mut bindings: Vec<(String, CExpr)> = Vec::new();
        for arg in args {
            let v = self.fresh();
            let ce = self
                .lower_eta_reduced_effect_expr(arg)
                .unwrap_or_else(|| self.lower_expr_value(arg));
            arg_vars.push(v.clone());
            bindings.push((v, ce));
        }
        (arg_vars, bindings)
    }
    pub(super) fn lower_eta_reduced_effect_op_ref(
        &mut self,
        node_id: crate::ast::NodeId,
        op_name: &str,
        qualifier: Option<&str>,
    ) -> Option<CExpr> {
        let effect_name = self.resolved_effect_call_name(node_id, op_name, qualifier)?;
        let _ = self.effect_defs.get(&effect_name)?.ops.get(op_name)?;
        let applied_effect = self
            .check_result
            .effect_at_node
            .get(&node_id)
            .map(crate::typechecker::applied_effect_key)
            .unwrap_or_else(|| effect_name.clone());
        let applied_effect = self.canonicalize_effect(&applied_effect);
        let op_info = self
            .effect_defs
            .get(&effect_name)?
            .ops
            .get(op_name)?
            .clone();

        // A nullary effect op (`fun now : Int`) can't be an eta-reduced *reference*
        // that still awaits arguments -- `now!` is always a saturated perform.
        // Without this, the zero-param loop below would emit `fun () -> perform`,
        // thunking the perform instead of running it. Fall through to
        // `lower_effect_call`, which performs immediately.
        if op_info.source_param_count == 0 {
            return None;
        }

        let mut params = Vec::new();
        let mut runtime_args = Vec::new();
        for idx in 0..op_info.source_param_count {
            let param = self.fresh();
            if op_info.runtime_param_positions.contains(&idx) {
                runtime_args.push(CExpr::Var(param.clone()));
            }
            params.push(param);
        }

        if let Some(shape) = self.planned_function_value_evidence(node_id) {
            // Raw CPS shape: the resulting closure is passed to a slot that
            // expects an effectful function value, so it takes `_Evidence`
            // and `_ReturnK` and reads the per-op handler out of the
            // evidence vector at call time.
            let evidence = "_Evidence".to_string();
            let return_k = "_ReturnK".to_string();
            runtime_args.push(CExpr::Var(return_k.clone()));
            params.push(evidence.clone());
            params.push(return_k);
            // Build the op lookup against the lambda's evidence parameter.
            let saved_evidence = self.current_evidence.clone();
            self.current_evidence = Some(EvidenceFrame::new(evidence, shape));
            let handler_expr = self.evidence_op_lookup(&applied_effect, op_name);
            self.current_evidence = saved_evidence;
            Some(CExpr::Fun(
                params,
                Box::new(CExpr::Apply(Box::new(handler_expr), runtime_args)),
            ))
        } else {
            // Value-closure shape: the resulting lambda is bound locally or
            // passed to a pure-shaped callback slot. Capture the in-scope
            // op closure (read out of current evidence) and provide an
            // identity return continuation.
            let handler_expr = self.evidence_op_lookup(&applied_effect, op_name);
            let return_value = self.fresh();
            runtime_args.push(CExpr::Fun(
                vec![return_value.clone()],
                Box::new(CExpr::Var(return_value)),
            ));
            Some(CExpr::Fun(
                params,
                Box::new(CExpr::Apply(Box::new(handler_expr), runtime_args)),
            ))
        }
    }

    pub(super) fn lower_eta_reduced_effect_expr(&mut self, expr: &Expr) -> Option<CExpr> {
        let mut args = Vec::new();
        let mut current = expr;
        let (effect_call_id, op_name, qualifier) = loop {
            match &current.kind {
                ExprKind::App { func, arg, .. } => {
                    args.push(arg.as_ref());
                    current = func.as_ref();
                }
                ExprKind::EffectCall {
                    name, qualifier, ..
                } => {
                    args.reverse();
                    break (current.id, name.as_str(), qualifier.as_deref());
                }
                _ => return None,
            }
        };

        if !args.is_empty() {
            return None;
        }
        self.lower_eta_reduced_effect_op_ref(effect_call_id, op_name, qualifier)
    }

    fn is_eta_reduced_effect_expr(expr: &Expr) -> bool {
        let mut args = Vec::new();
        let mut current = expr;
        loop {
            match &current.kind {
                ExprKind::App { func, arg, .. } => {
                    args.push(arg.as_ref());
                    current = func.as_ref();
                }
                ExprKind::EffectCall { .. } => return args.is_empty(),
                _ => return false,
            }
        }
    }
}
