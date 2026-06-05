use super::direct_core_refs::core_expr_mentions_var;
use super::*;

impl<'a, 'info> DirectLowerer<'a, 'info> {
    pub(super) fn lower_expr(&mut self, expr: &MExpr) -> CExpr {
        match expr {
            MExpr::Pure(atom) => self.lower_atom(atom),
            MExpr::Yield { op, args, .. } => self
                .lower_native_direct_call_yield_result(op, args, CExpr::Tuple(vec![]))
                .unwrap_or_else(|| self.unsupported_expr(expr)),
            MExpr::Let { var, value, body }
            | MExpr::Bind {
                var, value, body, ..
            } => {
                if let Some(lowered) =
                    self.try_lower_known_dict_immediate_method_sequence(var, value, body)
                {
                    return lowered;
                }
                if let Some(lowered) =
                    self.try_lower_immediate_known_dict_method_bind(var, value, body)
                {
                    return lowered;
                }
                let known_direct_lambda = self.known_direct_lambda_for_expr(value);
                if let Some(lambda) = known_direct_lambda
                    && occurs::local_is_only_called_in_expr(&var.name, body)
                    && lambda.params.iter().all(direct_param_supported)
                    && self.lambda_is_direct_subset_with_dict_bindings(
                        &lambda.dict_bindings,
                        &lambda.params,
                        &lambda.body,
                    )
                {
                    self.push_scope();
                    self.current_scope_mut().insert(var.name.clone());
                    self.current_shape_scope_mut().insert(
                        var.name.clone(),
                        LocalValueShape::PureCallable {
                            arity: lambda.params.len(),
                        },
                    );
                    self.bind_known_direct_lambda(var.name.clone(), lambda);
                    let body = self.lower_expr(body);
                    self.pop_scope();
                    return body;
                }
                let known_direct_lambda = self.known_direct_lambda_for_expr(value);
                if let Some(lambda) = known_direct_lambda
                    && lambda.params.iter().all(direct_param_supported)
                    && self.lambda_is_direct_subset_with_dict_bindings(
                        &lambda.dict_bindings,
                        &lambda.params,
                        &lambda.body,
                    )
                {
                    let lowered_value = self.lower_known_direct_lambda_value(&lambda);
                    self.push_scope();
                    self.current_scope_mut().insert(var.name.clone());
                    self.current_shape_scope_mut().insert(
                        var.name.clone(),
                        LocalValueShape::PureCallable {
                            arity: lambda.params.len(),
                        },
                    );
                    self.bind_known_direct_lambda(var.name.clone(), lambda);
                    let body = self.lower_expr(body);
                    self.pop_scope();
                    return CExpr::Let(
                        core_var(&var.name),
                        Box::new(lowered_value),
                        Box::new(body),
                    );
                }
                let local_shape = self.direct_local_shape_for_expr(value);
                let known_dict = self.known_dict_value_for_expr(value);
                let known_atom = self.known_direct_atom_for_expr(value);
                let known_value = self.known_direct_value_for_expr(value);
                self.push_scope();
                self.current_scope_mut().insert(var.name.clone());
                if let Some(shape) = local_shape {
                    self.current_shape_scope_mut()
                        .insert(var.name.clone(), shape);
                }
                if let Some(dict) = known_dict.as_ref() {
                    self.bind_known_dict_value(var.name.clone(), dict.clone());
                }
                if let Some(atom) = known_atom.as_ref() {
                    self.bind_known_direct_atom(var.name.clone(), atom.clone());
                }
                if let Some(value) = known_value.as_ref() {
                    self.bind_known_direct_value(var.name.clone(), value.clone());
                }
                let body = self.lower_expr(body);
                self.pop_scope();
                if known_dict.is_some() && !core_expr_mentions_var(&var.name, &body) {
                    return body;
                }
                if known_atom.is_some() && !core_expr_mentions_var(&var.name, &body) {
                    return body;
                }
                if known_value.is_some() && !core_expr_mentions_var(&var.name, &body) {
                    return body;
                }
                let value = self.lower_expr(value);
                CExpr::Let(core_var(&var.name), Box::new(value), Box::new(body))
            }
            MExpr::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => {
                if let Some(value) = self.known_direct_bool_for_atom(cond) {
                    return self.lower_expr(if value { then_branch } else { else_branch });
                }
                CExpr::Case(
                    Box::new(self.lower_atom(cond)),
                    vec![
                        CArm {
                            pat: CPat::Lit(CLit::Atom("true".to_string())),
                            guard: None,
                            body: self.lower_expr(then_branch),
                        },
                        CArm {
                            pat: CPat::Lit(CLit::Atom("false".to_string())),
                            guard: None,
                            body: self.lower_expr(else_branch),
                        },
                    ],
                )
            }
            MExpr::Case {
                scrutinee, arms, ..
            } => self.lower_case_chain(scrutinee, arms),
            MExpr::App { head, args, .. } => self.lower_app(head, args),
            MExpr::BinOp {
                op, left, right, ..
            } => binop_atoms(op, self.lower_atom(left), self.lower_atom(right)),
            MExpr::UnaryMinus { value, .. } => CExpr::Call(
                "erlang".to_string(),
                "-".to_string(),
                vec![CExpr::Lit(CLit::Int(0)), self.lower_atom(value)],
            ),
            MExpr::FieldAccess {
                record,
                field,
                record_name,
                anon_fields,
                ..
            } => self.lower_field_access(record, field, record_name.as_deref(), anon_fields),
            MExpr::RecordUpdate {
                record,
                fields,
                record_name,
                anon_fields,
                ..
            } => self.lower_record_update(record, fields, record_name.as_deref(), anon_fields),
            MExpr::ForeignCall {
                module, func, args, ..
            } => self.lower_foreign_call(module, func, args),
            MExpr::With { handler, body, .. } => self.lower_direct_with(handler, body),
            MExpr::Receive { arms, after, .. } => self.lower_direct_receive(arms, after.as_ref()),
            MExpr::BitString { .. } => self.unsupported_expr(expr),
            MExpr::DictMethodAccess {
                dict, method_index, ..
            } => {
                let dict = self.lower_atom(dict);
                CExpr::Call(
                    "erlang".to_string(),
                    "element".to_string(),
                    vec![CExpr::Lit(CLit::Int(*method_index as i64 + 1)), dict],
                )
            }
            MExpr::Resume { .. }
            | MExpr::Ensure { .. }
            | MExpr::LetFun { .. }
            | MExpr::HandlerValue { .. } => self.unsupported_expr(expr),
        }
    }
}
