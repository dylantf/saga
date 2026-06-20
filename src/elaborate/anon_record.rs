use super::*;

impl Elaborator {
    pub(crate) fn build_anon_record_generic_dict(&self, fields: &[(String, Type)], span: Span) -> Expr {
        Expr::synth(
            span,
            ExprKind::Tuple {
                elements: vec![
                    self.build_anon_record_generic_to(fields, span),
                    self.build_anon_record_generic_from(fields, span),
                ],
            },
        )
    }


    pub(crate) fn build_anon_record_generic_to(&self, fields: &[(String, Type)], span: Span) -> Expr {
        let record_var_name = "__anon_rec".to_string();
        let record_var = Expr::synth(
            span,
            ExprKind::Var {
                name: record_var_name.clone(),
            },
        );
        let names: Vec<&str> = fields.iter().map(|(name, _)| name.as_str()).collect();
        let tag = crate::ast::anon_record_tag(&names);
        let inner = self.build_anon_record_rep_to_inner(fields, &record_var, &tag, span);
        let body = self.apply2(
            &generic_ctor("Record"),
            self.string_lit(&tag, span),
            inner,
            span,
        );
        Expr::synth(
            span,
            ExprKind::Lambda {
                params: vec![Pat::Var {
                    id: NodeId::fresh(),
                    name: record_var_name,
                    span,
                }],
                body: Box::new(body),
            },
        )
    }


    pub(crate) fn build_anon_record_generic_from(&self, fields: &[(String, Type)], span: Span) -> Expr {
        let field_var_names: Vec<String> = (0..fields.len()).map(|i| format!("__f{i}")).collect();
        let inner_pat = self.build_anon_record_rep_from_inner(&field_var_names, span);
        let record_pat = Pat::Constructor {
            id: NodeId::fresh(),
            name: generic_ctor("Record"),
            args: vec![
                Pat::Wildcard {
                    id: NodeId::fresh(),
                    span,
                },
                inner_pat,
            ],
            span,
        };
        let record_fields: Vec<(String, Span, Expr)> = fields
            .iter()
            .zip(field_var_names.iter())
            .map(|((field_name, _), var_name)| {
                (
                    field_name.clone(),
                    span,
                    Expr::synth(
                        span,
                        ExprKind::Var {
                            name: var_name.clone(),
                        },
                    ),
                )
            })
            .collect();
        Expr::synth(
            span,
            ExprKind::Lambda {
                params: vec![record_pat],
                body: Box::new(Expr::synth(
                    span,
                    ExprKind::AnonRecordCreate {
                        fields: record_fields,
                    },
                )),
            },
        )
    }


    pub(crate) fn build_anon_record_rep_to_inner(
        &self,
        fields: &[(String, Type)],
        record_var: &Expr,
        record_tag: &str,
        span: Span,
    ) -> Expr {
        if fields.is_empty() {
            return Expr::synth(
                span,
                ExprKind::Constructor {
                    name: generic_ctor("U1"),
                },
            );
        }
        let mut iter = fields.iter().rev();
        let (last_name, _) = iter.next().expect("non-empty fields");
        let mut acc = self.build_anon_record_field_to(last_name, record_var, record_tag, span);
        for (field_name, _) in iter {
            acc = self.apply2(
                &generic_ctor("And"),
                self.build_anon_record_field_to(field_name, record_var, record_tag, span),
                acc,
                span,
            );
        }
        acc
    }


    pub(crate) fn build_anon_record_field_to(
        &self,
        field_name: &str,
        record_var: &Expr,
        record_tag: &str,
        span: Span,
    ) -> Expr {
        let access = Expr::synth(
            span,
            ExprKind::FieldAccess {
                expr: Box::new(record_var.clone()),
                field: field_name.to_string(),
                record_name: Some(record_tag.to_string()),
            },
        );
        self.apply1(
            &generic_ctor("Labeled"),
            self.apply1(&generic_ctor("Leaf"), access, span),
            span,
        )
    }


    pub(crate) fn build_anon_record_rep_from_inner(&self, field_vars: &[String], span: Span) -> Pat {
        if field_vars.is_empty() {
            return Pat::Constructor {
                id: NodeId::fresh(),
                name: generic_ctor("U1"),
                args: vec![],
                span,
            };
        }
        let mut iter = field_vars.iter().rev();
        let last = iter.next().expect("non-empty field vars");
        let mut acc = self.build_anon_record_field_from(last, span);
        for var_name in iter {
            acc = Pat::Constructor {
                id: NodeId::fresh(),
                name: generic_ctor("And"),
                args: vec![self.build_anon_record_field_from(var_name, span), acc],
                span,
            };
        }
        acc
    }


    pub(crate) fn build_anon_record_field_from(&self, var_name: &str, span: Span) -> Pat {
        Pat::Constructor {
            id: NodeId::fresh(),
            name: generic_ctor("Labeled"),
            args: vec![Pat::Constructor {
                id: NodeId::fresh(),
                name: generic_ctor("Leaf"),
                args: vec![Pat::Var {
                    id: NodeId::fresh(),
                    name: var_name.to_string(),
                    span,
                }],
                span,
            }],
            span,
        }
    }


    pub(crate) fn apply1(&self, func: &str, arg: Expr, span: Span) -> Expr {
        Expr::synth(
            span,
            ExprKind::App {
                func: Box::new(Expr::synth(
                    span,
                    ExprKind::Constructor { name: func.into() },
                )),
                arg: Box::new(arg),
            },
        )
    }


    pub(crate) fn apply2(&self, func: &str, a: Expr, b: Expr, span: Span) -> Expr {
        Expr::synth(
            span,
            ExprKind::App {
                func: Box::new(self.apply1(func, a, span)),
                arg: Box::new(b),
            },
        )
    }


    pub(crate) fn string_lit(&self, value: &str, span: Span) -> Expr {
        Expr::synth(
            span,
            ExprKind::Lit {
                value: Lit::String(value.into(), StringKind::Normal),
            },
        )
    }


    /// Check if the evidence at a node indicates Show for a Tuple type.
    /// If so, build an inline show expression for the tuple rather than
    /// using dictionary dispatch (since tuples are variable-arity).
    ///
    /// Returns a lambda: fun t -> "(" ++ show_T1(element(1,t)) ++ ", " ++ ... ++ ")"
    pub(crate) fn try_inline_tuple_show(
        &self,
        trait_name: &str,
        node_id: crate::ast::NodeId,
        span: Span,
    ) -> Option<Expr> {
        if trait_name != SHOW && trait_name != DEBUG {
            return None;
        }
        let evidence_list = self.evidence_by_node.get(&node_id)?;
        let tuple_ev = evidence_list.iter().find(|ev| {
            ev.trait_name == trait_name
                && ev.resolved_type.as_ref().is_some_and(|(name, _)| {
                    name == crate::typechecker::canonicalize_type_name("Tuple")
                })
        })?;
        let (_type_name, type_args) = tuple_ev.resolved_type.as_ref()?;
        self.build_tuple_show_lambda(trait_name, type_args, span)
    }


    /// Build a show/debug lambda for a tuple with the given element types.
    pub(crate) fn build_tuple_show_lambda(
        &self,
        trait_name: &str,
        type_args: &[Type],
        span: Span,
    ) -> Option<Expr> {
        let s = span;
        let t_var = Expr::synth(
            s,
            ExprKind::Var {
                name: "__tup".into(),
            },
        );

        // Build: "(" ++ show_T1(element(1, t)) ++ ", " ++ show_T2(element(2, t)) ++ ... ++ ")"
        let arity = type_args.len();
        if arity == 0 {
            // Empty tuple = unit, but this shouldn't happen (Unit is separate)
            return Some(Expr::synth(
                s,
                ExprKind::Lambda {
                    params: vec![Pat::Var {
                        id: NodeId::fresh(),
                        name: "__tup".into(),
                        span: s,
                    }],
                    body: Box::new(Expr::synth(
                        s,
                        ExprKind::Lit {
                            value: Lit::String("()".into(), StringKind::Normal),
                        },
                    )),
                },
            ));
        }

        // Build the shown elements and join with ", "
        let mut parts: Vec<Expr> = Vec::new();
        for (i, elem_ty) in type_args.iter().enumerate() {
            let show_fn = self.show_fn_for_type(trait_name, elem_ty, s)?;
            let elem = Expr::synth(
                s,
                ExprKind::ForeignCall {
                    module: "erlang".into(),
                    func: "element".into(),
                    args: vec![
                        Expr::synth(
                            s,
                            ExprKind::Lit {
                                value: Lit::Int(((i + 1) as i64).to_string(), (i + 1) as i64),
                            },
                        ),
                        t_var.clone(),
                    ],
                },
            );
            parts.push(Expr::synth(
                s,
                ExprKind::App {
                    func: Box::new(show_fn),
                    arg: Box::new(elem),
                },
            ));
        }

        // Join parts with ", " separators: "(" ++ p1 ++ ", " ++ p2 ++ ... ++ ")"
        let mut result = Expr::synth(
            s,
            ExprKind::Lit {
                value: Lit::String("(".into(), StringKind::Normal),
            },
        );
        for (i, part) in parts.into_iter().enumerate() {
            if i > 0 {
                result = Expr::synth(
                    s,
                    ExprKind::BinOp {
                        op: BinOp::Concat,
                        left: Box::new(result),
                        right: Box::new(Expr::synth(
                            s,
                            ExprKind::Lit {
                                value: Lit::String(", ".into(), StringKind::Normal),
                            },
                        )),
                    },
                );
            }
            result = Expr::synth(
                s,
                ExprKind::BinOp {
                    op: BinOp::Concat,
                    left: Box::new(result),
                    right: Box::new(part),
                },
            );
        }
        result = Expr::synth(
            s,
            ExprKind::BinOp {
                op: BinOp::Concat,
                left: Box::new(result),
                right: Box::new(Expr::synth(
                    s,
                    ExprKind::Lit {
                        value: Lit::String(")".into(), StringKind::Normal),
                    },
                )),
            },
        );

        Some(Expr::synth(
            s,
            ExprKind::Lambda {
                params: vec![Pat::Var {
                    id: NodeId::fresh(),
                    name: "__tup".into(),
                    span: s,
                }],
                body: Box::new(result),
            },
        ))
    }
}
