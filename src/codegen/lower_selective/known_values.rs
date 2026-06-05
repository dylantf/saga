use super::*;

impl<'a, 'info> DirectLowerer<'a, 'info> {
    pub(super) fn direct_local_shape_for_expr(&mut self, expr: &MExpr) -> Option<LocalValueShape> {
        match expr {
            MExpr::Pure(Atom::Lambda { params, body, .. })
                if self.lambda_is_direct_subset(params, body) =>
            {
                Some(LocalValueShape::PureCallable {
                    arity: params.len(),
                })
            }
            MExpr::DictMethodAccess {
                source,
                trait_name,
                method_index,
                ..
            } => self
                .pure_function_arity_at(*source)
                .or_else(|| self.pure_trait_method_arity(trait_name, *method_index))
                .map(|arity| LocalValueShape::PureCallable { arity }),
            MExpr::App { head, args, source } => self
                .partial_known_direct_lambda_result_shape(head, args)
                .or_else(|| self.local_shape_for_expr_result_type(*source)),
            MExpr::Resume { source, .. } | MExpr::With { source, .. } => {
                self.local_shape_for_expr_result_type(*source)
            }
            _ => None,
        }
    }

    pub(super) fn local_shape_for_expr_result_type(
        &self,
        source: NodeId,
    ) -> Option<LocalValueShape> {
        let ty = self.effect_info.type_at_node.get(&source)?;
        self.local_shape_for_param_type(ty)
    }

    pub(super) fn partial_known_direct_lambda_result_shape(
        &self,
        head: &Atom,
        args: &[Atom],
    ) -> Option<LocalValueShape> {
        let lambda = self.known_direct_lambda_for_atom(head)?;
        (args.len() < lambda.params.len()).then_some(LocalValueShape::PureCallable {
            arity: lambda.params.len() - args.len(),
        })
    }

    pub(super) fn direct_call_shape_for_local_use_in_expr(
        &self,
        local: &str,
        expr: &MExpr,
    ) -> Option<LocalValueShape> {
        let mut arity = None;
        Self::collect_direct_call_arity_for_local_in_expr(local, expr, &mut arity);
        arity.map(|arity| LocalValueShape::PureCallable { arity })
    }

    pub(super) fn collect_direct_call_arity_for_local_in_expr(
        local: &str,
        expr: &MExpr,
        arity: &mut Option<usize>,
    ) -> bool {
        match expr {
            MExpr::Pure(atom) => {
                Self::collect_direct_call_arity_for_local_in_atom(local, atom, arity)
            }
            MExpr::Yield { args, .. } | MExpr::ForeignCall { args, .. } => args
                .iter()
                .all(|arg| Self::collect_direct_call_arity_for_local_in_atom(local, arg, arity)),
            MExpr::Bind {
                var, value, body, ..
            }
            | MExpr::Let { var, value, body } => {
                Self::collect_direct_call_arity_for_local_in_expr(local, value, arity)
                    && (var.name == local
                        || Self::collect_direct_call_arity_for_local_in_expr(local, body, arity))
            }
            MExpr::Ensure { body, cleanup } => {
                Self::collect_direct_call_arity_for_local_in_expr(local, body, arity)
                    && Self::collect_direct_call_arity_for_local_in_expr(local, cleanup, arity)
            }
            MExpr::Case {
                scrutinee, arms, ..
            } => {
                Self::collect_direct_call_arity_for_local_in_atom(local, scrutinee, arity)
                    && arms.iter().all(|arm| {
                        arm.guard.as_ref().is_none_or(|guard| {
                            Self::collect_direct_call_arity_for_local_in_expr(local, guard, arity)
                        }) && (pat_binds_name(&arm.pattern, local)
                            || Self::collect_direct_call_arity_for_local_in_expr(
                                local, &arm.body, arity,
                            ))
                    })
            }
            MExpr::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => {
                Self::collect_direct_call_arity_for_local_in_atom(local, cond, arity)
                    && Self::collect_direct_call_arity_for_local_in_expr(local, then_branch, arity)
                    && Self::collect_direct_call_arity_for_local_in_expr(local, else_branch, arity)
            }
            MExpr::App { head, args, .. } => {
                if let Atom::Var { name, .. } = head
                    && name.name == local
                    && !Self::record_local_call_arity(arity, args.len())
                {
                    return false;
                }
                Self::collect_direct_call_arity_for_local_in_atom(local, head, arity)
                    && args.iter().all(|arg| {
                        Self::collect_direct_call_arity_for_local_in_atom(local, arg, arity)
                    })
            }
            MExpr::With { handler, body, .. } => {
                Self::collect_direct_call_arity_for_local_in_handler(local, handler, arity)
                    && Self::collect_direct_call_arity_for_local_in_expr(local, body, arity)
            }
            MExpr::Resume { value, .. }
            | MExpr::FieldAccess { record: value, .. }
            | MExpr::UnaryMinus { value, .. } => {
                Self::collect_direct_call_arity_for_local_in_atom(local, value, arity)
            }
            MExpr::RecordUpdate { record, fields, .. } => {
                Self::collect_direct_call_arity_for_local_in_atom(local, record, arity)
                    && fields.iter().all(|(_, atom)| {
                        Self::collect_direct_call_arity_for_local_in_atom(local, atom, arity)
                    })
            }
            MExpr::DictMethodAccess { dict, .. } => {
                Self::collect_direct_call_arity_for_local_in_atom(local, dict, arity)
            }
            MExpr::BinOp { left, right, .. } => {
                Self::collect_direct_call_arity_for_local_in_atom(local, left, arity)
                    && Self::collect_direct_call_arity_for_local_in_atom(local, right, arity)
            }
            MExpr::BitString { segments, .. } => segments.iter().all(|segment| {
                Self::collect_direct_call_arity_for_local_in_atom(local, &segment.value, arity)
            }),
            MExpr::Receive { arms, after, .. } => {
                arms.iter().all(|arm| {
                    arm.guard.as_ref().is_none_or(|guard| {
                        Self::collect_direct_call_arity_for_local_in_expr(local, guard, arity)
                    }) && (pat_binds_name(&arm.pattern, local)
                        || Self::collect_direct_call_arity_for_local_in_expr(
                            local, &arm.body, arity,
                        ))
                }) && after.as_ref().is_none_or(|(timeout, body)| {
                    Self::collect_direct_call_arity_for_local_in_atom(local, timeout, arity)
                        && Self::collect_direct_call_arity_for_local_in_expr(local, body, arity)
                })
            }
            MExpr::LetFun {
                name, body, rest, ..
            } => {
                let body_ok = name == local
                    || Self::collect_direct_call_arity_for_local_in_expr(local, body, arity);
                body_ok && Self::collect_direct_call_arity_for_local_in_expr(local, rest, arity)
            }
            MExpr::HandlerValue {
                arms,
                return_clause,
                ..
            } => {
                arms.iter().all(|arm| {
                    Self::collect_direct_call_arity_for_local_in_handler_arm(local, arm, arity)
                }) && return_clause.as_ref().is_none_or(|arm| {
                    Self::collect_direct_call_arity_for_local_in_handler_arm(local, arm, arity)
                })
            }
        }
    }

    pub(super) fn collect_direct_call_arity_for_local_in_atom(
        local: &str,
        atom: &Atom,
        arity: &mut Option<usize>,
    ) -> bool {
        match atom {
            Atom::Var { .. }
            | Atom::Lit { .. }
            | Atom::DictRef { .. }
            | Atom::QualifiedRef { .. }
            | Atom::Symbol { .. }
            | Atom::BackendAtom { .. } => true,
            Atom::Ctor { args, .. } => args
                .iter()
                .all(|arg| Self::collect_direct_call_arity_for_local_in_atom(local, arg, arity)),
            Atom::Tuple { elements, .. } => elements
                .iter()
                .all(|arg| Self::collect_direct_call_arity_for_local_in_atom(local, arg, arity)),
            Atom::AnonRecord { fields, .. } | Atom::Record { fields, .. } => {
                fields.iter().all(|(_, atom)| {
                    Self::collect_direct_call_arity_for_local_in_atom(local, atom, arity)
                })
            }
            Atom::Lambda { params, body, .. } => {
                params.iter().any(|param| pat_binds_name(param, local))
                    || Self::collect_direct_call_arity_for_local_in_expr(local, body, arity)
            }
            Atom::BackendSpawnThunk { callback, .. } => {
                Self::collect_direct_call_arity_for_local_in_atom(local, callback, arity)
            }
        }
    }

    pub(super) fn collect_direct_call_arity_for_local_in_handler(
        local: &str,
        handler: &MHandler,
        arity: &mut Option<usize>,
    ) -> bool {
        match handler {
            MHandler::Static {
                arms,
                return_clause,
                ..
            } => {
                arms.iter().all(|arm| {
                    Self::collect_direct_call_arity_for_local_in_handler_arm(local, arm, arity)
                }) && return_clause.as_ref().is_none_or(|arm| {
                    Self::collect_direct_call_arity_for_local_in_handler_arm(local, arm, arity)
                })
            }
            MHandler::Composite { handlers, .. } => handlers.iter().all(|handler| {
                Self::collect_direct_call_arity_for_local_in_handler(local, handler, arity)
            }),
            MHandler::Dynamic {
                op_tuple,
                return_lambda,
                ..
            } => {
                Self::collect_direct_call_arity_for_local_in_atom(local, op_tuple, arity)
                    && return_lambda.as_ref().is_none_or(|return_lambda| {
                        Self::collect_direct_call_arity_for_local_in_atom(
                            local,
                            return_lambda,
                            arity,
                        )
                    })
            }
            MHandler::Native { .. } => true,
        }
    }

    pub(super) fn collect_direct_call_arity_for_local_in_handler_arm(
        local: &str,
        arm: &MHandlerArm,
        arity: &mut Option<usize>,
    ) -> bool {
        arm.params.iter().any(|param| pat_binds_name(param, local))
            || (Self::collect_direct_call_arity_for_local_in_expr(local, &arm.body, arity)
                && arm.finally_block.as_ref().is_none_or(|finally_block| {
                    Self::collect_direct_call_arity_for_local_in_expr(local, finally_block, arity)
                }))
    }

    pub(super) fn record_local_call_arity(arity: &mut Option<usize>, next: usize) -> bool {
        match *arity {
            Some(existing) => existing == next,
            None => {
                *arity = Some(next);
                true
            }
        }
    }

    pub(super) fn cps_dict_method_shape_for_expr(&self, expr: &MExpr) -> Option<LocalValueShape> {
        let MExpr::DictMethodAccess {
            source,
            trait_name,
            method_index,
            ..
        } = expr
        else {
            return None;
        };
        let (source_arity, adapter_arity, effects) = self
            .cps_function_arity_at(*source)
            .or_else(|| self.cps_trait_method_arity(trait_name, *method_index))?;
        Some(LocalValueShape::RuntimeCpsCallable {
            source_arity,
            adapter_arity,
            effects,
        })
    }

    pub(super) fn cps_local_shape_for_expr(&self, expr: &MExpr) -> Option<LocalValueShape> {
        let MExpr::Pure(atom) = expr else {
            return None;
        };
        match self.cps_function_shape(atom)? {
            CallShape::Cps {
                module,
                name,
                source_arity,
                adapter_arity,
                effects,
            } => Some(LocalValueShape::CpsCallable {
                module,
                name,
                source_arity,
                adapter_arity,
                effects,
                hof_direct_specialization: self
                    .hof_direct_specialization_for_head(atom)
                    .map(|(_, specialization)| specialization),
            }),
            _ => None,
        }
    }

    pub(super) fn cps_bind_shape_for_expr(&self, expr: &MExpr) -> Option<LocalValueShape> {
        match expr {
            MExpr::Pure(atom) => {
                if self.lambda_is_cps_atom(atom) {
                    let (source_arity, adapter_arity, effects) =
                        self.cps_lambda_arity_for_atom(atom)?;
                    return Some(LocalValueShape::RuntimeCpsCallable {
                        source_arity,
                        adapter_arity,
                        effects,
                    });
                }
                if let Atom::Var { name, source } = atom {
                    match self.local_shape(&name.name) {
                        Some(
                            shape @ (LocalValueShape::CpsCallable { .. }
                            | LocalValueShape::RuntimeCpsCallable { .. }),
                        ) => return Some(shape),
                        Some(LocalValueShape::PureCallableFromUseType) => {
                            let (source_arity, adapter_arity, effects) =
                                self.cps_function_arity_at(*source)?;
                            return Some(LocalValueShape::RuntimeCpsCallable {
                                source_arity,
                                adapter_arity,
                                effects,
                            });
                        }
                        _ => {}
                    }
                }
                self.cps_local_shape_for_expr(expr)
                    .or_else(|| self.pure_value_atom_shape(atom))
            }
            MExpr::DictMethodAccess { .. } => self.cps_dict_method_shape_for_expr(expr),
            MExpr::If {
                then_branch,
                else_branch,
                ..
            } => {
                let then_shape = self.cps_bind_shape_for_expr(then_branch)?;
                let else_shape = self.cps_bind_shape_for_expr(else_branch)?;
                self.compatible_runtime_cps_shape(&then_shape, &else_shape)
            }
            MExpr::Case { arms, .. } => self.compatible_case_runtime_cps_shape(arms),
            _ => None,
        }
    }

    pub(super) fn known_dict_value_for_expr(&mut self, expr: &MExpr) -> Option<KnownDictValue> {
        match expr {
            MExpr::App { head, args, .. } => {
                let Atom::DictRef { name, .. } = head else {
                    return None;
                };
                let (constructor, methods_inlineable) =
                    if let Some(constructor) = self.local_dict_constructors.get(name) {
                        (constructor.clone(), true)
                    } else {
                        (self.imported_dict_constructors.get(name)?.clone(), false)
                    };
                if constructor.dict_params.len() != args.len()
                    || args.iter().any(|arg| !self.atom_is_direct_subset(arg))
                {
                    return None;
                }

                let mut methods = Vec::with_capacity(constructor.methods.len());
                for method in &constructor.methods {
                    let MExpr::Pure(atom @ Atom::Lambda { .. }) = method else {
                        return None;
                    };
                    methods.push(atom.clone());
                }
                Some(KnownDictValue {
                    constructor_name: name.clone(),
                    methods_inlineable,
                    dict_params: constructor.dict_params.clone(),
                    dict_args: args.to_vec(),
                    methods,
                })
            }
            MExpr::If {
                then_branch,
                else_branch,
                ..
            } => {
                let then_dict = self.known_dict_value_for_expr(then_branch)?;
                let else_dict = self.known_dict_value_for_expr(else_branch)?;
                (then_dict == else_dict).then_some(then_dict)
            }
            _ => None,
        }
    }

    pub(super) fn known_cps_lambda_for_expr(&mut self, expr: &MExpr) -> Option<KnownCpsLambda> {
        let MExpr::DictMethodAccess {
            dict, method_index, ..
        } = expr
        else {
            return None;
        };
        let Atom::Var { name, .. } = dict else {
            return None;
        };
        let known_dict = self.known_dict_value(&name.name)?;
        if !known_dict.methods_inlineable {
            return None;
        }
        if self.known_dict_method_is_active(&known_dict, *method_index) {
            return None;
        }
        if known_dict
            .dict_params
            .iter()
            .any(|param| self.is_local(param))
        {
            return None;
        }
        let method = known_dict.methods.get(*method_index)?.clone();
        if !self.lambda_is_cps_subset(&method) {
            return None;
        }
        let Atom::Lambda { params, body, .. } = method else {
            return None;
        };
        if params.iter().any(|param| !direct_param_supported(param)) {
            return None;
        }
        let dict_bindings = known_dict
            .dict_params
            .into_iter()
            .zip(known_dict.dict_args)
            .collect();
        Some(KnownCpsLambda {
            dict_bindings,
            params,
            body,
        })
    }

    pub(super) fn known_direct_lambda_for_expr(&self, expr: &MExpr) -> Option<KnownDirectLambda> {
        if let MExpr::Pure(atom) = expr
            && let Some(lambda) = self.known_direct_lambda_for_atom(atom)
        {
            return Some(lambda);
        }

        let MExpr::DictMethodAccess {
            dict, method_index, ..
        } = expr
        else {
            return None;
        };
        let Atom::Var { name, .. } = dict else {
            return None;
        };
        let known_dict = self.known_dict_value(&name.name)?;
        if !known_dict.methods_inlineable {
            return None;
        }
        if self.known_dict_method_is_active(&known_dict, *method_index) {
            return None;
        }
        if known_dict
            .dict_params
            .iter()
            .any(|param| self.is_local(param))
        {
            return None;
        }
        let method = known_dict.methods.get(*method_index)?.clone();
        let Atom::Lambda { params, body, .. } = method else {
            return None;
        };
        if params.iter().any(|param| !direct_param_supported(param)) {
            return None;
        }
        let dict_bindings = known_dict
            .dict_params
            .into_iter()
            .zip(known_dict.dict_args)
            .collect();
        Some(KnownDirectLambda {
            dict_bindings,
            params,
            body,
        })
    }

    pub(super) fn known_direct_lambda_for_atom(&self, atom: &Atom) -> Option<KnownDirectLambda> {
        match atom {
            Atom::Var { name, .. } => self.known_direct_lambda(&name.name),
            Atom::Lambda { params, body, .. } => {
                if params.iter().any(|param| !direct_param_supported(param)) {
                    return None;
                }
                Some(KnownDirectLambda {
                    dict_bindings: Vec::new(),
                    params: params.clone(),
                    body: body.clone(),
                })
            }
            _ => None,
        }
    }
}
