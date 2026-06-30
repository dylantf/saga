use super::*;

impl Elaborator {
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
