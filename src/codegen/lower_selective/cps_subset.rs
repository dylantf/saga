use super::*;

impl<'a, 'info> DirectLowerer<'a, 'info> {
    pub(super) fn expr_is_cps_island_subset(&mut self, expr: &MExpr) -> bool {
        match expr {
            MExpr::Yield { op, args, .. } => self.yield_args_are_cps_island_subset(op, args),
            MExpr::Let { var, value, body }
            | MExpr::Bind {
                var, value, body, ..
            } => {
                let value_supported = self.expr_is_direct_subset(value)
                    || self.expr_is_cps_island_subset(value)
                    || self.cps_bind_value_expr_is_supported(value);
                if !value_supported {
                    return false;
                }

                let local_shape = self
                    .cps_bind_shape_for_expr(value)
                    .or_else(|| self.direct_local_shape_for_expr(value))
                    .or_else(|| self.direct_call_shape_for_local_use_in_expr(&var.name, body));
                let known_dict = self.known_dict_value_for_expr(value);
                let known_cps_lambda = self.known_cps_lambda_for_expr(value);
                let known_direct_lambda = self.known_direct_lambda_for_expr(value);
                let known_atom = self.known_direct_atom_for_expr(value);
                self.push_scope();
                self.current_scope_mut().insert(var.name.clone());
                if let Some(shape) = local_shape {
                    self.current_shape_scope_mut()
                        .insert(var.name.clone(), shape);
                }
                if let Some(dict) = known_dict {
                    self.bind_known_dict_value(var.name.clone(), dict);
                }
                if let Some(lambda) = known_cps_lambda {
                    self.bind_known_cps_lambda(var.name.clone(), lambda);
                }
                if let Some(lambda) = known_direct_lambda {
                    self.bind_known_direct_lambda(var.name.clone(), lambda);
                }
                if let Some(atom) = known_atom {
                    self.bind_known_direct_atom(var.name.clone(), atom);
                }
                let supported =
                    self.expr_is_cps_island_subset(body) || self.expr_is_direct_subset(body);
                self.pop_scope();
                supported
            }
            MExpr::App { head, args, .. } => {
                if self.expr_is_direct_subset(expr) {
                    return true;
                }

                if let Some((source_arity, adapter_arity, _effects)) =
                    self.cps_lambda_arity_for_atom(head)
                    && self.lambda_is_cps_subset(head)
                {
                    return source_arity == args.len()
                        && adapter_arity == args.len() + 2
                        && args.iter().all(|arg| self.atom_is_cps_value_subset(arg));
                }

                let call_supported = match self.call_shape(head) {
                    Some(CallShape::Cps {
                        source_arity,
                        adapter_arity,
                        ..
                    })
                    | Some(CallShape::LocalCpsCallable {
                        source_arity,
                        adapter_arity,
                        ..
                    }) => source_arity == args.len() && adapter_arity == args.len() + 2,
                    _ => false,
                };
                if !call_supported {
                    return false;
                }
                self.cps_call_args_are_supported(head, args)
            }
            MExpr::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => {
                self.atom_is_direct_subset(cond)
                    && self.expr_is_cps_island_subset(then_branch)
                    && self.expr_is_cps_island_subset(else_branch)
            }
            MExpr::Case {
                scrutinee, arms, ..
            } => {
                if !self.atom_is_direct_subset(scrutinee) {
                    return false;
                }
                arms.iter().all(|arm| {
                    if !direct_pat_supported(&arm.pattern) {
                        return false;
                    }
                    self.push_scope();
                    self.bind_pat_locals(&arm.pattern);
                    let supported = arm
                        .guard
                        .as_ref()
                        .is_none_or(|guard| self.expr_is_direct_subset(guard))
                        && self.expr_is_cps_island_subset(&arm.body);
                    self.pop_scope();
                    supported
                })
            }
            MExpr::Receive { arms, after, .. } => {
                arms.iter().all(|arm| {
                    if !direct_pat_supported(&arm.pattern) {
                        return false;
                    }
                    self.push_scope();
                    self.bind_pat_locals(&arm.pattern);
                    let supported = arm
                        .guard
                        .as_ref()
                        .is_none_or(|guard| self.expr_is_direct_subset(guard))
                        && self.expr_is_cps_island_subset(&arm.body);
                    self.pop_scope();
                    supported
                }) && after.as_ref().is_none_or(|(timeout, body)| {
                    self.atom_is_direct_subset(timeout) && self.expr_is_cps_island_subset(body)
                })
            }
            MExpr::With { handler, body, .. } => {
                self.handler_is_cps_island_subset(handler) && self.expr_is_cps_island_subset(body)
            }
            MExpr::BitString { segments, .. } => segments.iter().all(|segment| {
                self.atom_is_direct_subset(&segment.value)
                    && segment
                        .size
                        .as_ref()
                        .is_none_or(|size| self.atom_is_direct_subset(size))
            }),
            MExpr::HandlerValue {
                arms,
                return_clause,
                ..
            } => self.handler_value_is_cps_island_subset(arms, return_clause.as_deref()),
            _ => self.expr_is_direct_subset(expr),
        }
    }

    pub(super) fn yield_args_are_cps_island_subset(
        &mut self,
        _op: &EffectOpRef,
        args: &[Atom],
    ) -> bool {
        args.iter()
            .all(|arg| self.effect_protocol_arg_atom_is_cps_island_subset(arg))
    }

    pub(super) fn effect_protocol_arg_atom_is_cps_island_subset(&mut self, arg: &Atom) -> bool {
        self.atom_is_direct_subset(arg) || self.atom_is_cps_value_subset(arg)
    }

    pub(super) fn handler_is_cps_island_subset(&mut self, handler: &MHandler) -> bool {
        let (arms, return_clause) = match handler {
            MHandler::Static {
                arms,
                return_clause,
                ..
            } => (arms, return_clause.as_ref()),
            MHandler::Dynamic {
                op_tuple,
                return_lambda,
                ..
            } => {
                return self.atom_is_direct_subset(op_tuple)
                    && return_lambda
                        .as_ref()
                        .is_none_or(|lambda| self.atom_is_cps_value_subset(lambda));
            }
            MHandler::Native { .. } => return self.direct_handler_kind(handler).is_some(),
            _ => return false,
        };
        if !return_clause.is_none_or(|arm| self.return_clause_is_cps_island_subset(arm)) {
            return false;
        }
        arms.iter()
            .all(|arm| self.handler_arm_is_cps_island_subset(arm))
    }

    pub(super) fn return_clause_is_cps_island_subset(&mut self, arm: &MHandlerArm) -> bool {
        if arm.finally_block.is_some()
            || arm.params.len() > 1
            || arm.params.iter().any(|p| !direct_param_supported(p))
        {
            return false;
        }
        self.push_scope();
        for pat in &arm.params {
            self.bind_pat_locals(pat);
        }
        let supported =
            self.expr_is_direct_subset(&arm.body) || self.expr_is_cps_island_subset(&arm.body);
        self.pop_scope();
        supported
    }

    pub(super) fn handler_arm_is_cps_island_subset(&mut self, arm: &MHandlerArm) -> bool {
        if arm.params.iter().any(|p| !direct_param_supported(p)) {
            return false;
        }
        if arm.finally_block.is_some() && Self::handler_arm_expr_contains_yield(&arm.body) {
            return false;
        }
        self.push_scope();
        self.bind_cps_handler_arm_param_locals(arm);
        let supported = match arm.finally_block.as_ref() {
            Some(finally_block) => {
                self.handler_arm_expr_is_cps_island_subset_with_finally(&arm.body, finally_block)
            }
            None => self.handler_arm_expr_is_cps_island_subset(&arm.body),
        };
        self.pop_scope();
        supported
    }

    pub(super) fn handler_arm_expr_is_cps_island_subset_with_finally(
        &mut self,
        expr: &MExpr,
        finally_block: &MExpr,
    ) -> bool {
        match expr {
            MExpr::Pure(atom) => {
                self.handler_arm_atom_is_cps_island_subset(atom)
                    && self.handler_finally_expr_is_supported(finally_block)
            }
            MExpr::Resume { value, .. } => {
                self.atom_is_direct_subset(value)
                    && self.handler_finally_expr_is_supported(finally_block)
            }
            MExpr::Bind {
                var, value, body, ..
            }
            | MExpr::Let { var, value, body } => {
                let value_supported = if let MExpr::Resume {
                    value: resume_value,
                    ..
                } = &**value
                {
                    self.atom_is_direct_subset(resume_value)
                        && self.handler_finally_expr_is_supported(finally_block)
                } else {
                    self.handler_arm_expr_is_cps_island_subset(value)
                        || self.handler_arm_expr_is_cps_callback_call_subset(value)
                };
                if !value_supported {
                    return false;
                }
                let local_shape = self.direct_local_shape_for_expr(value).or_else(|| {
                    matches!(&**value, MExpr::Resume { .. })
                        .then(|| self.direct_call_shape_for_local_use_in_expr(&var.name, body))
                        .flatten()
                });
                self.push_scope();
                self.current_scope_mut().insert(var.name.clone());
                if let Some(shape) = local_shape {
                    self.current_shape_scope_mut()
                        .insert(var.name.clone(), shape);
                }
                let supported =
                    self.handler_arm_expr_is_cps_island_subset_with_finally(body, finally_block);
                self.pop_scope();
                supported
            }
            MExpr::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => {
                self.atom_is_direct_subset(cond)
                    && self.handler_arm_expr_is_cps_island_subset_with_finally(
                        then_branch,
                        finally_block,
                    )
                    && self.handler_arm_expr_is_cps_island_subset_with_finally(
                        else_branch,
                        finally_block,
                    )
            }
            MExpr::Case {
                scrutinee, arms, ..
            } => {
                if !self.atom_is_direct_subset(scrutinee) {
                    return false;
                }
                arms.iter().all(|arm| {
                    if !direct_pat_supported(&arm.pattern) {
                        return false;
                    }
                    self.push_scope();
                    self.bind_pat_locals(&arm.pattern);
                    let supported = arm
                        .guard
                        .as_ref()
                        .is_none_or(|guard| self.expr_is_direct_subset(guard))
                        && self.handler_arm_expr_is_cps_island_subset_with_finally(
                            &arm.body,
                            finally_block,
                        );
                    self.pop_scope();
                    supported
                })
            }
            MExpr::BitString { segments, .. } => {
                segments.iter().all(|segment| {
                    self.handler_arm_atom_is_cps_island_subset(&segment.value)
                        && segment
                            .size
                            .as_ref()
                            .is_none_or(|size| self.handler_arm_atom_is_cps_island_subset(size))
                }) && self.handler_finally_expr_is_supported(finally_block)
            }
            MExpr::Yield { .. } => false,
            MExpr::App { head, args, .. } if self.is_flat_map_identity_resume_app(head, args) => {
                self.handler_finally_expr_is_supported(finally_block)
            }
            _ => {
                (self.expr_is_direct_subset(expr)
                    || self.handler_arm_expr_is_cps_island_subset(expr))
                    && self.handler_finally_expr_is_supported(finally_block)
            }
        }
    }

    pub(super) fn handler_finally_expr_is_supported(&mut self, expr: &MExpr) -> bool {
        self.expr_is_direct_subset(expr) || self.handler_arm_expr_is_cps_callback_call_subset(expr)
    }

    pub(super) fn handler_arm_expr_is_cps_callback_call_subset(&mut self, expr: &MExpr) -> bool {
        let MExpr::App { head, args, .. } = expr else {
            return false;
        };
        matches!(
            self.call_shape(head),
            Some(CallShape::Cps { .. } | CallShape::LocalCpsCallable { .. })
        ) && args
            .iter()
            .all(|arg| self.atom_is_direct_subset(arg) || self.atom_is_cps_value_subset(arg))
    }

    pub(super) fn handler_arm_expr_is_cps_island_subset(&mut self, expr: &MExpr) -> bool {
        if let MExpr::Pure(atom) = expr {
            return self.handler_arm_atom_is_cps_island_subset(atom);
        }
        if self.expr_is_direct_subset(expr) {
            return true;
        }
        match expr {
            MExpr::Yield { op, args, .. } => self.yield_args_are_cps_island_subset(op, args),
            MExpr::Resume { value, .. } => self.atom_is_direct_subset(value),
            MExpr::App { head, args, .. } => {
                self.handler_arm_expr_is_cps_callback_call_subset(expr)
                    || self.is_flat_map_identity_resume_app(head, args)
            }
            MExpr::Bind {
                var, value, body, ..
            }
            | MExpr::Let { var, value, body } => {
                let value_supported = self.handler_arm_expr_is_cps_island_subset(value)
                    || matches!(&**value, MExpr::Resume { value, .. } if self.atom_is_direct_subset(value));
                if !value_supported {
                    return false;
                }
                let local_shape = self.direct_local_shape_for_expr(value).or_else(|| {
                    matches!(&**value, MExpr::Resume { .. })
                        .then(|| self.direct_call_shape_for_local_use_in_expr(&var.name, body))
                        .flatten()
                });
                self.push_scope();
                self.current_scope_mut().insert(var.name.clone());
                if let Some(shape) = local_shape {
                    self.current_shape_scope_mut()
                        .insert(var.name.clone(), shape);
                }
                let supported = self.handler_arm_expr_is_cps_island_subset(body);
                self.pop_scope();
                supported
            }
            MExpr::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => {
                self.atom_is_direct_subset(cond)
                    && self.handler_arm_expr_is_cps_island_subset(then_branch)
                    && self.handler_arm_expr_is_cps_island_subset(else_branch)
            }
            MExpr::Case {
                scrutinee, arms, ..
            } => {
                if !self.atom_is_direct_subset(scrutinee) {
                    return false;
                }
                arms.iter().all(|arm| {
                    if !direct_pat_supported(&arm.pattern) {
                        return false;
                    }
                    self.push_scope();
                    self.bind_pat_locals(&arm.pattern);
                    let supported = arm
                        .guard
                        .as_ref()
                        .is_none_or(|guard| self.expr_is_direct_subset(guard))
                        && self.handler_arm_expr_is_cps_island_subset(&arm.body);
                    self.pop_scope();
                    supported
                })
            }
            MExpr::BitString { segments, .. } => segments.iter().all(|segment| {
                self.handler_arm_atom_is_cps_island_subset(&segment.value)
                    && segment
                        .size
                        .as_ref()
                        .is_none_or(|size| self.handler_arm_atom_is_cps_island_subset(size))
            }),
            _ => false,
        }
    }

    pub(super) fn handler_arm_expr_contains_yield(expr: &MExpr) -> bool {
        match expr {
            MExpr::Yield { .. } => true,
            MExpr::Let { value, body, .. } | MExpr::Bind { value, body, .. } => {
                Self::handler_arm_expr_contains_yield(value)
                    || Self::handler_arm_expr_contains_yield(body)
            }
            MExpr::If {
                then_branch,
                else_branch,
                ..
            } => {
                Self::handler_arm_expr_contains_yield(then_branch)
                    || Self::handler_arm_expr_contains_yield(else_branch)
            }
            MExpr::Case { arms, .. } => arms
                .iter()
                .any(|arm| Self::handler_arm_expr_contains_yield(&arm.body)),
            _ => false,
        }
    }

    pub(super) fn handler_arm_atom_is_cps_island_subset(&mut self, atom: &Atom) -> bool {
        match atom {
            Atom::Lambda { params, body, .. } => {
                self.handler_arm_lambda_is_cps_island_subset(params, body)
            }
            Atom::Ctor { args, .. } => args
                .iter()
                .all(|arg| self.handler_arm_atom_is_cps_island_subset(arg)),
            Atom::Tuple { elements, .. } => elements
                .iter()
                .all(|arg| self.handler_arm_atom_is_cps_island_subset(arg)),
            Atom::AnonRecord { fields, .. } | Atom::Record { fields, .. } => fields
                .iter()
                .all(|(_, arg)| self.handler_arm_atom_is_cps_island_subset(arg)),
            Atom::BackendSpawnThunk { callback, .. } => {
                self.handler_arm_atom_is_cps_island_subset(callback)
            }
            Atom::Var { .. }
            | Atom::Lit { .. }
            | Atom::Symbol { .. }
            | Atom::QualifiedRef { .. }
            | Atom::DictRef { .. } => self.atom_is_direct_subset(atom),
            Atom::BackendAtom { .. } => true,
        }
    }

    pub(super) fn handler_arm_lambda_is_cps_island_subset(
        &mut self,
        params: &[Pat],
        body: &MExpr,
    ) -> bool {
        if params.iter().any(|p| !direct_param_supported(p)) {
            return false;
        }
        self.push_scope();
        for pat in params {
            self.bind_pat_locals(pat);
        }
        let supported = self.handler_arm_expr_is_cps_island_subset(body);
        self.pop_scope();
        supported
    }

    pub(super) fn is_flat_map_identity_resume_app(&mut self, head: &Atom, args: &[Atom]) -> bool {
        if args.len() != 2 {
            return false;
        }
        let Some(CallShape::Direct(callable)) = self.call_shape(head) else {
            return false;
        };
        if callable.arity != 2 || callable.name != "flat_map" {
            return false;
        }
        if !self.atom_is_direct_subset(&args[1]) {
            return false;
        }
        let Atom::Lambda { params, body, .. } = &args[0] else {
            return false;
        };
        self.lambda_is_identity_resume(params, body)
    }

    pub(super) fn lambda_is_identity_resume(&self, params: &[Pat], body: &MExpr) -> bool {
        let [Pat::Var { name, .. }] = params else {
            return false;
        };
        matches!(
            body,
            MExpr::Resume {
                value: Atom::Var { name: var, .. },
                ..
            } if var.name == *name
        )
    }

    pub(super) fn direct_intrinsic_args_are_supported(
        &mut self,
        intrinsic: IntrinsicId,
        args: &[Atom],
    ) -> bool {
        match intrinsic {
            IntrinsicId::CatchPanic => {
                matches!(
                    args,
                    [Atom::Lambda { params, body, .. }]
                        if self.lambda_is_direct_subset(params, body)
                            || self.lambda_is_pure_direct_cps_island_subset(&args[0], params, body)
                ) || args.iter().all(|arg| self.atom_is_direct_subset(arg))
            }
            IntrinsicId::PrintStdout | IntrinsicId::PrintStderr | IntrinsicId::Dbg => {
                args.iter().all(|arg| self.atom_is_direct_subset(arg))
            }
        }
    }

    pub(super) fn fresh_cps_temp(&mut self, prefix: &str) -> String {
        let id = self.cps_temp_counter;
        self.cps_temp_counter += 1;
        format!("{prefix}{id}")
    }

    pub(super) fn fresh_abort_marker(&mut self) -> String {
        let id = self.cps_temp_counter;
        self.cps_temp_counter += 1;
        format!("__saga_abort_{}_{}", self.current_module, id)
    }

    pub(super) fn handler_arm_semantically_aborts(&self, arm: &MHandlerArm) -> bool {
        !self.expr_contains_resume(&arm.body)
            && self.handler_info.resumption.get(&arm.id) != Some(&ResumptionKind::TailResumptive)
    }

    pub(super) fn handler_arm_is_optimized_tail_resume(&self, arm: &MHandlerArm) -> bool {
        !self.expr_contains_resume(&arm.body)
            && self.handler_info.resumption.get(&arm.id) == Some(&ResumptionKind::TailResumptive)
    }

    pub(super) fn atom_is_direct_subset(&mut self, atom: &Atom) -> bool {
        match atom {
            Atom::Var { name, .. } => {
                let cps_callable_local = matches!(
                    self.local_shape(&name.name),
                    Some(
                        LocalValueShape::CpsCallable { .. }
                            | LocalValueShape::RuntimeCpsCallable { .. }
                    )
                );
                (self.is_local(&name.name) && !cps_callable_local)
                    || self.direct_values.contains(&name.name)
                    || self.supported_direct_call(atom).is_some()
                    || self.direct_function_value_ref(atom).is_some()
            }
            Atom::Lit { .. } | Atom::Symbol { .. } => true,
            Atom::Ctor { args, .. } => args.iter().all(|arg| self.atom_is_direct_subset(arg)),
            Atom::Tuple { elements, .. } => {
                elements.iter().all(|arg| self.atom_is_direct_subset(arg))
            }
            Atom::AnonRecord { fields, .. } | Atom::Record { fields, .. } => fields
                .iter()
                .all(|(_, arg)| self.atom_is_direct_subset(arg)),
            Atom::Lambda { params, body, .. } => {
                self.lambda_is_direct_subset(params, body)
                    || self.lambda_is_pure_direct_cps_island_subset(atom, params, body)
            }
            Atom::QualifiedRef { .. } => self.direct_function_value_ref(atom).is_some(),
            Atom::BackendAtom { .. } => true,
            Atom::BackendSpawnThunk { callback, .. } => {
                self.effect_protocol_arg_atom_is_cps_island_subset(callback)
            }
            Atom::DictRef { .. } => self.direct_dict_constructor(atom).is_some(),
        }
    }

    pub(super) fn atom_is_cps_value_subset(&mut self, atom: &Atom) -> bool {
        if matches!(atom, Atom::Lambda { .. }) {
            return self.lambda_is_cps_subset(atom) || self.atom_is_direct_subset(atom);
        }
        self.cps_value_atom_shape(atom).is_some() || self.atom_is_direct_subset(atom)
    }

    pub(super) fn cps_call_args_are_supported(&mut self, head: &Atom, args: &[Atom]) -> bool {
        let expected_arg_shapes = self.cps_callback_param_shapes(head);
        let expected_arg_types = self.direct_call_param_types(head);
        args.iter().enumerate().all(|(index, arg)| {
            match expected_arg_shapes.get(index).copied().flatten() {
                Some((_source_arity, _adapter_arity)) => self.cps_callback_arg_is_supported(arg),
                None => {
                    expected_arg_types
                        .get(index)
                        .and_then(Option::as_ref)
                        .cloned()
                        .is_some_and(|ty| self.atom_is_supported_for_expected_type(arg, &ty))
                        || self.atom_is_cps_value_subset(arg)
                }
            }
        })
    }

    pub(super) fn cps_callback_arg_is_supported(&mut self, atom: &Atom) -> bool {
        if let Atom::Lambda { params, body, .. } = atom {
            self.lambda_is_cps_subset(atom) || self.lambda_is_direct_subset(params, body)
        } else {
            self.cps_value_atom_shape(atom).is_some()
                || self.pure_value_atom_shape(atom).is_some()
                || self.atom_is_direct_subset(atom)
        }
    }

    pub(super) fn direct_call_args_are_supported(&mut self, head: &Atom, args: &[Atom]) -> bool {
        let expected_arg_shapes = self.direct_call_effectful_callback_param_shapes(head);
        let expected_arg_types = self.direct_call_param_types(head);
        args.iter().enumerate().all(|(index, arg)| {
            match expected_arg_shapes.get(index).copied().flatten() {
                Some((_source_arity, _adapter_arity)) => self.cps_callback_arg_is_supported(arg),
                None => {
                    expected_arg_types
                        .get(index)
                        .and_then(Option::as_ref)
                        .cloned()
                        .is_some_and(|ty| self.atom_is_supported_for_expected_type(arg, &ty))
                        || self.atom_is_direct_subset(arg)
                }
            }
        })
    }

    pub(super) fn direct_call_param_types(&self, head: &Atom) -> Vec<Option<Type>> {
        let source = match head {
            Atom::Var { source, .. }
            | Atom::QualifiedRef { source, .. }
            | Atom::Lambda { source, .. } => *source,
            _ => return Vec::new(),
        };
        let Some(mut current) = self.effect_info.type_at_node.get(&source) else {
            return Vec::new();
        };
        let mut params = Vec::new();
        while let Type::Fun(param, ret, _) = current {
            params.push(Some((**param).clone()));
            current = ret;
        }
        params
    }

    pub(super) fn atom_is_supported_for_expected_type(
        &mut self,
        atom: &Atom,
        expected: &Type,
    ) -> bool {
        if self.atom_is_direct_subset(atom) {
            return true;
        }

        if self.cps_function_arity_from_type(expected).is_some() {
            return self.cps_callback_arg_is_supported(atom);
        }

        match (atom, expected) {
            (Atom::Ctor { name, args, .. }, Type::Con(type_name, type_args))
                if type_name == crate::typechecker::canonicalize_type_name("List")
                    && type_args.len() == 1 =>
            {
                match (name.as_str(), args.as_slice()) {
                    ("Nil", []) => true,
                    ("Cons", [head, tail]) => {
                        self.atom_is_supported_for_expected_type(head, &type_args[0])
                            && self.atom_is_supported_for_expected_type(tail, expected)
                    }
                    _ => false,
                }
            }
            (Atom::Tuple { elements, .. }, Type::Con(type_name, type_args))
                if type_name == crate::typechecker::canonicalize_type_name("Tuple")
                    && elements.len() == type_args.len() =>
            {
                elements.iter().zip(type_args).all(|(element, expected)| {
                    self.atom_is_supported_for_expected_type(element, expected)
                })
            }
            _ => false,
        }
    }

    pub(super) fn direct_call_effectful_callback_param_shapes(
        &self,
        head: &Atom,
    ) -> Vec<Option<(usize, usize)>> {
        let source = match head {
            Atom::Var { source, .. }
            | Atom::QualifiedRef { source, .. }
            | Atom::Lambda { source, .. } => *source,
            _ => return Vec::new(),
        };
        let mut shapes = Vec::new();
        if let Some(mut current) = self.effect_info.type_at_node.get(&source) {
            while let Type::Fun(param, ret, _) = current {
                shapes.push(self.cps_callback_shape_from_type(param));
                current = ret;
            }
        }
        if shapes.iter().any(Option::is_some) {
            return shapes;
        }
        self.resolved_callback_param_shapes(head)
    }

    pub(super) fn cps_callback_shape_from_type(&self, ty: &Type) -> Option<(usize, usize)> {
        self.cps_function_arity_from_type(ty)
            .map(|(source_arity, adapter_arity, _effects)| (source_arity, adapter_arity))
    }

    fn resolved_callback_param_shapes(&self, head: &Atom) -> Vec<Option<(usize, usize)>> {
        let source = match head {
            Atom::Var { source, .. } | Atom::QualifiedRef { source, .. } => *source,
            _ => return Vec::new(),
        };
        let Some(resolved) = self.resolution.get(&source) else {
            return Vec::new();
        };
        let ResolvedCodegenKind::BeamFunction {
            erlang_mod, name, ..
        } = &resolved.kind
        else {
            return Vec::new();
        };
        let arities = self
            .resolved_erlang_module_for_symbol(resolved, erlang_mod)
            .and_then(|module| {
                self.imported_callback_param_arities
                    .get(&(module, name.clone()))
            })
            .or_else(|| self.callable_callback_param_arities.get(name));

        arities
            .map(|arities| {
                arities
                    .iter()
                    .map(|arity| arity.map(|source_arity| (source_arity, source_arity + 2)))
                    .collect()
            })
            .unwrap_or_default()
    }

    pub(super) fn lambda_is_direct_subset(&mut self, params: &[Pat], body: &MExpr) -> bool {
        if params.iter().any(|p| !direct_param_supported(p)) {
            return false;
        }
        self.push_scope();
        for pat in params {
            self.bind_pat_locals(pat);
        }
        let supported = self.expr_is_direct_subset(body);
        self.pop_scope();
        supported
    }

    pub(super) fn lambda_is_direct_cps_island_subset(
        &mut self,
        params: &[Pat],
        body: &MExpr,
    ) -> bool {
        if params.iter().any(|p| !direct_param_supported(p)) {
            return false;
        }
        self.push_scope();
        for pat in params {
            self.bind_pat_locals(pat);
        }
        let supported = self.expr_is_cps_island_subset(body);
        self.pop_scope();
        supported
    }

    pub(super) fn lambda_is_pure_direct_cps_island_subset(
        &mut self,
        atom: &Atom,
        params: &[Pat],
        body: &MExpr,
    ) -> bool {
        self.pure_callback_arity_for_atom(atom) == Some(params.len())
            && self.lambda_is_direct_cps_island_subset(params, body)
    }

    pub(super) fn lambda_is_cps_subset(&mut self, atom: &Atom) -> bool {
        let Atom::Lambda { params, body, .. } = atom else {
            return false;
        };
        if self.cps_lambda_arity_for_atom(atom).is_none()
            || params.iter().any(|p| !direct_param_supported(p))
        {
            return false;
        }
        self.push_scope();
        for pat in params {
            self.bind_pat_locals(pat);
        }
        let direct = self.expr_is_direct_subset(body);
        let supported = !direct && self.expr_is_cps_island_subset(body);
        self.pop_scope();
        supported
    }
}
