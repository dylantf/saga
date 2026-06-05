use super::*;

impl<'a, 'info> DirectLowerer<'a, 'info> {
    pub(super) fn expr_is_direct_subset(&mut self, expr: &MExpr) -> bool {
        match expr {
            MExpr::Pure(atom) => self.atom_is_direct_subset(atom),
            MExpr::Yield { op, args, .. } => self.native_direct_yield_is_direct_subset(op, args),
            MExpr::Let { var, value, body }
            | MExpr::Bind {
                var, value, body, ..
            } => {
                let local_shape = self.direct_local_shape_for_expr(value).or_else(|| {
                    if matches!(&**value, MExpr::Resume { .. }) {
                        self.direct_call_shape_for_local_use_in_expr(&var.name, body)
                            .or(Some(LocalValueShape::PureCallableFromUseType))
                    } else {
                        None
                    }
                });
                let known_direct_lambda = self.known_direct_lambda_for_expr(value);
                let known_direct_value = self.known_direct_value_for_expr(value);
                if !self.expr_is_direct_subset(value) {
                    return false;
                }
                self.push_scope();
                self.current_scope_mut().insert(var.name.clone());
                if let Some(shape) = local_shape {
                    self.current_shape_scope_mut()
                        .insert(var.name.clone(), shape);
                }
                if let Some(lambda) = known_direct_lambda {
                    self.bind_known_direct_lambda(var.name.clone(), lambda);
                }
                if let Some(value) = known_direct_value {
                    self.bind_known_direct_value(var.name.clone(), value);
                }
                let supported = self.expr_is_direct_subset(body);
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
                    && self.expr_is_direct_subset(then_branch)
                    && self.expr_is_direct_subset(else_branch)
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
                        && self.expr_is_direct_subset(&arm.body);
                    self.pop_scope();
                    supported
                })
            }
            MExpr::App { head, args, .. } => {
                if self.is_panic_or_todo_call(head, args) {
                    return self.atom_is_direct_subset(&args[0]);
                }
                if self
                    .partial_known_direct_lambda_result_shape(head, args)
                    .is_some()
                {
                    return args.iter().all(|arg| self.atom_is_direct_subset(arg));
                }
                if let Atom::Lambda { params, body, .. } = head
                    && params.len() == args.len()
                    && args.iter().all(|arg| self.atom_is_direct_subset(arg))
                {
                    return self.lambda_is_direct_subset(params, body);
                }
                match self.call_shape(head) {
                    Some(CallShape::Intrinsic(intrinsic)) => {
                        direct_intrinsic_arity(intrinsic).is_some_and(|arity| arity == args.len())
                            && self.direct_intrinsic_args_are_supported(intrinsic, args)
                    }
                    Some(CallShape::Direct(callable)) => {
                        args.len() <= callable.arity
                            && self.direct_call_args_are_supported(head, args)
                    }
                    Some(CallShape::LocalCallable { arity, .. }) => {
                        args.len() <= arity && self.direct_call_args_are_supported(head, args)
                    }
                    Some(CallShape::Cps {
                        source_arity,
                        adapter_arity,
                        effects,
                        ..
                    }) => {
                        effects.is_empty()
                            && source_arity == args.len()
                            && adapter_arity == args.len() + 2
                            && self.direct_cps_call_args_are_supported(head, args)
                    }
                    Some(CallShape::LocalCpsCallable { .. }) | None => false,
                }
            }
            MExpr::BinOp { left, right, .. } => {
                self.atom_is_direct_subset(left) && self.atom_is_direct_subset(right)
            }
            MExpr::UnaryMinus { value, .. } => self.atom_is_direct_subset(value),
            MExpr::FieldAccess { record, .. } => self.atom_is_direct_subset(record),
            MExpr::RecordUpdate { record, fields, .. } => {
                self.atom_is_direct_subset(record)
                    && fields
                        .iter()
                        .all(|(_, atom)| self.atom_is_direct_subset(atom))
            }
            MExpr::ForeignCall { args, .. } => {
                args.iter().all(|arg| self.atom_is_direct_subset(arg))
            }
            MExpr::Receive { arms, after, .. } => {
                let arms_supported = arms.iter().all(|arm| {
                    if !direct_pat_supported(&arm.pattern) {
                        return false;
                    }
                    self.push_scope();
                    self.bind_pat_locals(&arm.pattern);
                    let supported = arm
                        .guard
                        .as_ref()
                        .is_none_or(|guard| self.expr_is_direct_subset(guard))
                        && self.expr_is_direct_subset(&arm.body);
                    self.pop_scope();
                    supported
                });
                arms_supported
                    && after.as_ref().is_none_or(|(timeout, body)| {
                        self.atom_is_direct_subset(timeout) && self.expr_is_direct_subset(body)
                    })
            }
            MExpr::With { handler, body, .. } => {
                (self.static_handler_is_direct_return_only(handler)
                    || self.direct_handler_kind(handler).is_some())
                    && self.expr_is_direct_subset(body)
            }
            MExpr::BitString { .. }
            | MExpr::Resume { .. }
            | MExpr::Ensure { .. }
            | MExpr::LetFun { .. }
            | MExpr::HandlerValue { .. } => false,
            MExpr::DictMethodAccess { dict, .. } => self.atom_is_direct_subset(dict),
        }
    }

    pub(super) fn static_handler_is_direct_return_only(&mut self, handler: &MHandler) -> bool {
        let MHandler::Static {
            effects,
            arms,
            return_clause,
            ..
        } = handler
        else {
            return false;
        };
        if !effects.is_empty() || !arms.is_empty() {
            return false;
        }
        let Some(arm) = return_clause else {
            return true;
        };
        if arm.finally_block.is_some()
            || arm.params.len() > 1
            || arm
                .params
                .iter()
                .any(|param| !direct_param_supported(param))
        {
            return false;
        }
        self.push_scope();
        for param in &arm.params {
            self.bind_pat_locals(param);
        }
        let supported = self.expr_is_direct_subset(&arm.body);
        self.pop_scope();
        supported
    }

    pub(super) fn direct_handler_kind(&self, handler: &MHandler) -> Option<DirectHandlerKind> {
        let MHandler::Native { handler, .. } = handler else {
            return None;
        };
        DirectHandlerKind::from_handler_name(handler)
    }

    pub(super) fn push_native_variant_frame_for_name(&mut self, name: &str) -> bool {
        let Some(frame) = Self::native_variant_frame_for_name(name) else {
            return false;
        };
        self.direct_handler_stack.push(frame);
        true
    }

    pub(super) fn push_native_variant_frame(
        &mut self,
        output_name: &str,
        native_frame: Option<DirectHandlerFrame>,
    ) -> bool {
        if let Some(frame) = native_frame {
            self.direct_handler_stack.push(frame);
            return true;
        }
        self.push_native_variant_frame_for_name(output_name)
    }

    pub(super) fn native_variant_frame_for_name(name: &str) -> Option<DirectHandlerFrame> {
        let (_, suffix) = name.split_once("__native__")?;
        let (handler, effects) = suffix.split_once("__")?;
        let kind = DirectHandlerKind::from_handler_name(handler)?;
        let effects = effects
            .split("__")
            .filter(|effect| !effect.is_empty())
            .map(|effect| effect.replace('_', "."))
            .collect::<Vec<_>>();
        if effects.is_empty() {
            return None;
        }
        Some(DirectHandlerFrame::Native { effects, kind })
    }

    pub(super) fn native_variant_frames_in_program(
        &self,
        program: &MProgram,
    ) -> Vec<DirectHandlerFrame> {
        let mut frames = Vec::new();
        let mut seen = HashSet::new();
        for decl in program {
            match decl {
                MDecl::FunBinding(fb) => {
                    self.collect_native_variant_frames_in_expr(&fb.body, &mut frames, &mut seen);
                }
                MDecl::Val(val) => {
                    self.collect_native_variant_frames_in_expr(&val.value, &mut frames, &mut seen);
                }
                MDecl::DictConstructor(dc) => {
                    for method in &dc.methods {
                        self.collect_native_variant_frames_in_expr(method, &mut frames, &mut seen);
                    }
                }
                MDecl::Passthrough(_) => {}
            }
        }
        frames
    }

    pub(super) fn collect_native_variant_frames_in_expr(
        &self,
        expr: &MExpr,
        frames: &mut Vec<DirectHandlerFrame>,
        seen: &mut HashSet<String>,
    ) {
        match expr {
            MExpr::With { handler, body, .. } => {
                self.collect_native_variant_frames_in_handler(handler, frames, seen);
                self.collect_native_variant_frames_in_expr(body, frames, seen);
            }
            MExpr::Bind { value, body, .. } | MExpr::Let { value, body, .. } => {
                self.collect_native_variant_frames_in_expr(value, frames, seen);
                self.collect_native_variant_frames_in_expr(body, frames, seen);
            }
            MExpr::Ensure { body, cleanup } => {
                self.collect_native_variant_frames_in_expr(body, frames, seen);
                self.collect_native_variant_frames_in_expr(cleanup, frames, seen);
            }
            MExpr::Case { arms, .. } | MExpr::Receive { arms, .. } => {
                if let MExpr::Case { scrutinee, .. } = expr {
                    self.collect_native_variant_frames_in_atom(scrutinee, frames, seen);
                }
                for arm in arms {
                    if let Some(guard) = &arm.guard {
                        self.collect_native_variant_frames_in_expr(guard, frames, seen);
                    }
                    self.collect_native_variant_frames_in_expr(&arm.body, frames, seen);
                }
                if let MExpr::Receive {
                    after: Some((_, body)),
                    ..
                } = expr
                {
                    if let MExpr::Receive {
                        after: Some((timeout, _)),
                        ..
                    } = expr
                    {
                        self.collect_native_variant_frames_in_atom(timeout, frames, seen);
                    }
                    self.collect_native_variant_frames_in_expr(body, frames, seen);
                }
            }
            MExpr::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => {
                self.collect_native_variant_frames_in_atom(cond, frames, seen);
                self.collect_native_variant_frames_in_expr(then_branch, frames, seen);
                self.collect_native_variant_frames_in_expr(else_branch, frames, seen);
            }
            MExpr::LetFun { body, rest, .. } => {
                self.collect_native_variant_frames_in_expr(body, frames, seen);
                self.collect_native_variant_frames_in_expr(rest, frames, seen);
            }
            MExpr::HandlerValue {
                arms,
                return_clause,
                ..
            } => {
                for arm in arms {
                    self.collect_native_variant_frames_in_handler_arm(arm, frames, seen);
                }
                if let Some(arm) = return_clause {
                    self.collect_native_variant_frames_in_handler_arm(arm, frames, seen);
                }
            }
            MExpr::Pure(atom) | MExpr::Resume { value: atom, .. } => {
                self.collect_native_variant_frames_in_atom(atom, frames, seen);
            }
            MExpr::Yield { args, .. } | MExpr::ForeignCall { args, .. } => {
                for arg in args {
                    self.collect_native_variant_frames_in_atom(arg, frames, seen);
                }
            }
            MExpr::App { head, args, .. } => {
                self.collect_native_variant_frames_in_atom(head, frames, seen);
                for arg in args {
                    self.collect_native_variant_frames_in_atom(arg, frames, seen);
                }
            }
            MExpr::FieldAccess { record, .. } | MExpr::DictMethodAccess { dict: record, .. } => {
                self.collect_native_variant_frames_in_atom(record, frames, seen);
            }
            MExpr::RecordUpdate { record, fields, .. } => {
                self.collect_native_variant_frames_in_atom(record, frames, seen);
                for (_, atom) in fields {
                    self.collect_native_variant_frames_in_atom(atom, frames, seen);
                }
            }
            MExpr::BinOp { left, right, .. } => {
                self.collect_native_variant_frames_in_atom(left, frames, seen);
                self.collect_native_variant_frames_in_atom(right, frames, seen);
            }
            MExpr::UnaryMinus { value, .. } => {
                self.collect_native_variant_frames_in_atom(value, frames, seen);
            }
            MExpr::BitString { segments, .. } => {
                for segment in segments {
                    self.collect_native_variant_frames_in_atom(&segment.value, frames, seen);
                    if let Some(size) = &segment.size {
                        self.collect_native_variant_frames_in_atom(size, frames, seen);
                    }
                }
            }
        }
    }

    pub(super) fn collect_native_variant_frames_in_atom(
        &self,
        atom: &Atom,
        frames: &mut Vec<DirectHandlerFrame>,
        seen: &mut HashSet<String>,
    ) {
        match atom {
            Atom::Ctor { args, .. } | Atom::Tuple { elements: args, .. } => {
                for arg in args {
                    self.collect_native_variant_frames_in_atom(arg, frames, seen);
                }
            }
            Atom::AnonRecord { fields, .. } | Atom::Record { fields, .. } => {
                for (_, value) in fields {
                    self.collect_native_variant_frames_in_atom(value, frames, seen);
                }
            }
            Atom::Lambda { body, .. } => {
                self.collect_native_variant_frames_in_expr(body, frames, seen);
            }
            Atom::BackendSpawnThunk { callback, .. } => {
                self.collect_native_variant_frames_in_atom(callback, frames, seen);
            }
            Atom::Var { .. }
            | Atom::Lit { .. }
            | Atom::DictRef { .. }
            | Atom::QualifiedRef { .. }
            | Atom::Symbol { .. }
            | Atom::BackendAtom { .. } => {}
        }
    }

    pub(super) fn collect_native_variant_frames_in_handler(
        &self,
        handler: &MHandler,
        frames: &mut Vec<DirectHandlerFrame>,
        seen: &mut HashSet<String>,
    ) {
        match handler {
            MHandler::Native {
                effects, handler, ..
            } => {
                let Some(kind) = DirectHandlerKind::from_handler_name(handler) else {
                    return;
                };
                let frame = DirectHandlerFrame::Native {
                    effects: effects.clone(),
                    kind,
                };
                let key = Self::native_variant_frame_key(&frame);
                if seen.insert(key) {
                    frames.push(frame);
                }
            }
            MHandler::Static {
                arms,
                return_clause,
                ..
            } => {
                for arm in arms {
                    self.collect_native_variant_frames_in_handler_arm(arm, frames, seen);
                }
                if let Some(arm) = return_clause {
                    self.collect_native_variant_frames_in_handler_arm(arm, frames, seen);
                }
            }
            MHandler::Composite { handlers, .. } => {
                for handler in handlers {
                    self.collect_native_variant_frames_in_handler(handler, frames, seen);
                }
            }
            MHandler::Dynamic {
                return_lambda: Some(Atom::Lambda { body, .. }),
                ..
            } => {
                self.collect_native_variant_frames_in_expr(body, frames, seen);
            }
            MHandler::Dynamic { .. } => {}
        }
    }

    pub(super) fn collect_native_variant_frames_in_handler_arm(
        &self,
        arm: &MHandlerArm,
        frames: &mut Vec<DirectHandlerFrame>,
        seen: &mut HashSet<String>,
    ) {
        self.collect_native_variant_frames_in_expr(&arm.body, frames, seen);
        if let Some(finally_block) = &arm.finally_block {
            self.collect_native_variant_frames_in_expr(finally_block, frames, seen);
        }
    }

    pub(super) fn native_variant_name_for_function(
        &self,
        name: &str,
        frame: &DirectHandlerFrame,
    ) -> Option<String> {
        if !self.native_variant_frame_handles_function(name, frame) {
            return None;
        }
        Some(format!(
            "__saga_native_variant__{}__{}",
            Self::sanitize_native_variant_part(name),
            Self::native_variant_frame_key(frame)
        ))
    }

    pub(super) fn native_variant_name_for_current_frame(&self, name: &str) -> Option<String> {
        self.direct_handler_stack
            .iter()
            .rev()
            .find_map(|frame| self.native_variant_name_for_function(name, frame))
    }

    pub(super) fn native_variant_frame_handles_function(
        &self,
        name: &str,
        frame: &DirectHandlerFrame,
    ) -> bool {
        let DirectHandlerFrame::Native { .. } = frame else {
            return false;
        };
        self.function_plans
            .get(name)
            .copied()
            .is_some_and(FunctionLoweringPlan::has_cps_body)
    }

    pub(super) fn native_variant_frame_key(frame: &DirectHandlerFrame) -> String {
        let DirectHandlerFrame::Native { effects, kind } = frame else {
            return "native__unknown".to_string();
        };
        let handler = match kind {
            DirectHandlerKind::BeamActor => "beam_actor",
            DirectHandlerKind::BeamRef => "beam_ref",
            DirectHandlerKind::EtsRef => "ets_ref",
            DirectHandlerKind::BeamVec => "beam_vec",
            DirectHandlerKind::BeamSignal => "beam_signal",
        };
        let mut parts = vec!["native".to_string(), handler.to_string()];
        parts.extend(effects.iter().map(|effect| {
            effect
                .split('.')
                .map(Self::sanitize_native_variant_part)
                .collect::<Vec<_>>()
                .join("_")
        }));
        parts.join("__")
    }

    pub(super) fn sanitize_native_variant_part(part: &str) -> String {
        part.chars()
            .map(|ch| {
                if ch.is_ascii_alphanumeric() || ch == '_' {
                    ch
                } else {
                    '_'
                }
            })
            .collect()
    }

    pub(super) fn native_direct_yield_is_direct_subset(
        &mut self,
        op: &EffectOpRef,
        args: &[Atom],
    ) -> bool {
        let Some(kind) = self.native_direct_handler_kind_for_yield(op) else {
            return false;
        };
        match kind {
            DirectHandlerKind::BeamActor | DirectHandlerKind::BeamSignal => {
                let Some(spec) = native_op(&op.effect, &op.op) else {
                    return false;
                };
                !spec.erl_module.is_empty()
                    && args.len() == spec.param_count
                    && args.iter().all(|arg| self.atom_is_direct_subset(arg))
            }
            DirectHandlerKind::BeamRef | DirectHandlerKind::EtsRef => {
                op.effect == "Std.Ref.Ref"
                    && match op.op.as_str() {
                        "get" => args.len() == 1 && self.atom_is_direct_subset(&args[0]),
                        "set" => {
                            args.len() == 2
                                && self.atom_is_direct_subset(&args[0])
                                && self.atom_is_direct_subset(&args[1])
                        }
                        "new" => args.len() == 1 && self.atom_is_direct_subset(&args[0]),
                        "modify" => {
                            args.len() == 2
                                && self.atom_is_direct_subset(&args[0])
                                && self.effect_protocol_arg_atom_is_cps_island_subset(&args[1])
                        }
                        _ => false,
                    }
            }
            DirectHandlerKind::BeamVec => false,
        }
    }

    pub(super) fn direct_cps_call_args_are_supported(
        &mut self,
        head: &Atom,
        args: &[Atom],
    ) -> bool {
        let expected_arg_shapes = self.direct_call_effectful_callback_param_shapes(head);
        if !expected_arg_shapes.iter().any(Option::is_some) {
            return false;
        }
        args.iter().enumerate().all(|(index, arg)| {
            match expected_arg_shapes.get(index).copied().flatten() {
                Some((source_arity, _adapter_arity)) => {
                    self.cps_runtime_arg_atom_is_supported(arg, source_arity)
                }
                None => self.atom_is_direct_subset(arg),
            }
        })
    }

    pub(super) fn cps_runtime_arg_atom_is_supported(
        &mut self,
        atom: &Atom,
        source_arity: usize,
    ) -> bool {
        match atom {
            Atom::Lambda { params, body, .. } => {
                params.len() == source_arity
                    && (self.lambda_is_direct_subset(params, body)
                        || self.lambda_is_cps_subset(atom)
                        || self.lambda_is_direct_cps_island_subset(params, body))
            }
            _ => {
                self.atom_is_direct_subset(atom)
                    || self
                        .cps_value_atom_shape(atom)
                        .is_some_and(|shape| match shape {
                            LocalValueShape::RuntimeCpsCallable {
                                source_arity: actual,
                                ..
                            }
                            | LocalValueShape::CpsCallable {
                                source_arity: actual,
                                ..
                            }
                            | LocalValueShape::PureCallable { arity: actual } => {
                                actual == source_arity
                            }
                            LocalValueShape::PureCallableFromUseType => true,
                        })
            }
        }
    }
}
