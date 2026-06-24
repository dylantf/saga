use super::*;

impl Elaborator {
    pub(crate) fn elaborate_expr(&mut self, expr: &Expr) -> Expr {
        let span = expr.span;
        let node_id = expr.id;
        match &expr.kind {
            // Trait method reference: look up evidence to determine dispatch
            ExprKind::Var { name } => {
                // Evidence-first: only treat as a trait method if the typechecker
                // recorded evidence at this node. This correctly handles shadowing
                // (a user function named `compare` won't be mistaken for Ord.compare).

                if let Some((trait_name, method_index)) = self.resolve_trait_method(name, node_id) {
                    if is_known_symbol_trait(&trait_name)
                        && let Some(symbol_lambda) = self.try_symbol_intrinsic_lambda(node_id, span)
                    {
                        return symbol_lambda;
                    }
                    if let Some(dict_expr) = self.resolve_dict(&trait_name, node_id, span) {
                        return Expr::synth(
                            span,
                            ExprKind::DictMethodAccess {
                                dict: Box::new(dict_expr),
                                trait_name: trait_name.clone(),
                                method_index,
                            },
                        );
                    }
                    // Tuple Show: inline expansion (no dict constructor for tuples)
                    if let Some(show_lambda) =
                        self.try_inline_tuple_show(&trait_name, node_id, span)
                    {
                        return show_lambda;
                    }
                }

                // Dict-parameterized function used as a bare value (not directly applied).
                // Partially apply the dict args so it can be passed as a first-class function.
                // e.g. `let p = print` becomes `let p = print __dict_Show_String`
                if let Some(dict_param_info) = self.fun_dict_params_for_callee(name, node_id) {
                    let mut result: Expr = expr.clone();
                    let mut trait_occurrences: HashMap<&str, usize> = HashMap::new();
                    for (trait_name, _type_var) in &dict_param_info {
                        let occ = trait_occurrences.entry(trait_name).or_insert(0);
                        if let Some(dict_expr) =
                            self.resolve_dict_nth(trait_name, node_id, span, *occ)
                        {
                            result = Expr::synth(
                                span,
                                ExprKind::App {
                                    func: Box::new(result),
                                    arg: Box::new(dict_expr),
                                },
                            );
                        }
                        *occ += 1;
                    }
                    // A dict-parameterized *local* let-binding is eta-expanded to a
                    // closure taking leading dict params plus its user args
                    // (`fun (dict, arg) -> ...`). Applying only the dicts here leaves
                    // an under-saturated closure, and Core Erlang's `apply` cannot
                    // partially apply a local closure — the runtime aborts with
                    // "called with 1 argument(s), but expects 2". Eta-abstract the
                    // remaining user args so the inner application is saturated:
                    //   g  -->  fun (__p0, ..) -> g(dict.., __p0, ..)
                    // Top-level functions don't need this: their under-saturated
                    // call sites are turned into partial-application closures during
                    // lowering (`lower_resolved_fun_call`).
                    if matches!(
                        self.resolution.value(node_id),
                        Some(ResolvedValue::Local { .. })
                    ) && let Some(&value_arity) = self.let_binding_arities.get(name)
                        && value_arity > 0
                    {
                        let eta_params: Vec<Pat> = (0..value_arity)
                            .map(|i| Pat::Var {
                                id: NodeId::fresh(),
                                name: format!("__partial_arg{}", i),
                                span,
                            })
                            .collect();
                        for p in &eta_params {
                            if let Pat::Var { name: pname, .. } = p {
                                result = Expr::synth(
                                    span,
                                    ExprKind::App {
                                        func: Box::new(result),
                                        arg: Box::new(Expr::synth(
                                            span,
                                            ExprKind::Var {
                                                name: pname.clone(),
                                            },
                                        )),
                                    },
                                );
                            }
                        }
                        return Expr::synth(
                            span,
                            ExprKind::Lambda {
                                params: eta_params,
                                body: Box::new(result),
                            },
                        );
                    }
                    return result;
                }

                expr.clone()
            }

            // Function application: check if we need to insert dict args
            ExprKind::App { func, arg } => {
                // An `op!` call is represented as an App spine over an EffectCall
                // head. If the operation has its own `where` constraints, append a
                // dictionary argument (resolved from the call-site evidence) for
                // each, as the outermost applications so they arrive *after* the
                // user args — matching the handler arm closure's trailing dict
                // params. Handle the whole spine here so dicts are appended once.
                if let Some(elaborated) = self.elaborate_effect_call_spine(expr) {
                    return elaborated;
                }

                // Check if this is a direct call to a function with where clauses
                if let ExprKind::Var { name, .. } = &func.kind {
                    // Evidence-first: check if the typechecker identified this as
                    // a trait method call before attempting dict dispatch.
                    if let Some((trait_name, method_index)) =
                        self.resolve_trait_method(name, func.id)
                    {
                        if is_known_symbol_trait(&trait_name)
                            && let Some(symbol_lambda) =
                                self.try_symbol_intrinsic_lambda(func.id, func.span)
                        {
                            let elab_arg = self.elaborate_expr(arg);
                            return Expr::synth(
                                span,
                                ExprKind::App {
                                    func: Box::new(symbol_lambda),
                                    arg: Box::new(elab_arg),
                                },
                            );
                        }
                        if let Some(dict_expr) = self
                            .resolve_call_dict_nth(&trait_name, func.id, node_id, func.span, 0)
                            .or_else(|| {
                                self.resolve_dict_from_arg_type(&trait_name, arg, func.span)
                            })
                        {
                            let elab_arg = self.elaborate_expr(arg);
                            let method = Expr::synth(
                                func.span,
                                ExprKind::DictMethodAccess {
                                    dict: Box::new(dict_expr),
                                    trait_name: trait_name.clone(),
                                    method_index,
                                },
                            );
                            return Expr::synth(
                                span,
                                ExprKind::App {
                                    func: Box::new(method),
                                    arg: Box::new(elab_arg),
                                },
                            );
                        }
                        // Tuple Show: inline expansion directly applied to the arg
                        if let Some(show_lambda) =
                            self.try_inline_tuple_show(&trait_name, func.id, func.span)
                        {
                            let elab_arg = self.elaborate_expr(arg);
                            return Expr::synth(
                                span,
                                ExprKind::App {
                                    func: Box::new(show_lambda),
                                    arg: Box::new(elab_arg),
                                },
                            );
                        }
                    }

                    // If calling a function that has dict params, insert them
                    if let Some(dict_param_info) = self.fun_dict_params_for_callee(name, func.id) {
                        let elab_arg = self.elaborate_expr(arg);
                        // Build the call with dict args prepended
                        let mut result: Expr =
                            Expr::rebuild_like(func, ExprKind::Var { name: name.clone() });
                        let mut trait_occurrences: HashMap<&str, usize> = HashMap::new();
                        for (trait_name, _type_var) in &dict_param_info {
                            let occ = trait_occurrences.entry(trait_name).or_insert(0);
                            if let Some(dict_expr) = self
                                .resolve_call_dict_nth(
                                    trait_name, func.id, node_id, func.span, *occ,
                                )
                                .or_else(|| {
                                    (*occ == 0)
                                        .then(|| {
                                            self.resolve_dict_from_arg_type(
                                                trait_name, arg, func.span,
                                            )
                                        })
                                        .flatten()
                                })
                            {
                                result = Expr::synth(
                                    span,
                                    ExprKind::App {
                                        func: Box::new(result),
                                        arg: Box::new(dict_expr),
                                    },
                                );
                            }
                            *occ += 1;
                        }
                        return Expr::rebuild_like(
                            expr,
                            ExprKind::App {
                                func: Box::new(result),
                                arg: Box::new(elab_arg),
                            },
                        );
                    }
                }

                // Same logic for qualified module calls: Result.unwrap, etc.
                if let ExprKind::QualifiedName { module, name, .. } = &func.kind {
                    let qualified = format!("{}.{}", module, name);

                    // Evidence-first: trait method via qualified name
                    if let Some((trait_name, method_index)) =
                        self.resolve_trait_method(&qualified, func.id)
                        && let Some(dict_expr) = self
                            .resolve_call_dict_nth(&trait_name, func.id, node_id, func.span, 0)
                            .or_else(|| {
                                self.resolve_dict_from_arg_type(&trait_name, arg, func.span)
                            })
                    {
                        let elab_arg = self.elaborate_expr(arg);
                        let method = Expr::synth(
                            func.span,
                            ExprKind::DictMethodAccess {
                                dict: Box::new(dict_expr),
                                trait_name: trait_name.clone(),
                                method_index,
                            },
                        );
                        return Expr::synth(
                            span,
                            ExprKind::App {
                                func: Box::new(method),
                                arg: Box::new(elab_arg),
                            },
                        );
                    }

                    // Dict-parameterized function via qualified name
                    if let Some(dict_param_info) =
                        self.fun_dict_params_for_callee(&qualified, func.id)
                    {
                        let elab_arg = self.elaborate_expr(arg);
                        let mut result: Expr = func.as_ref().clone();
                        let mut trait_occurrences: HashMap<&str, usize> = HashMap::new();
                        for (trait_name, _type_var) in &dict_param_info {
                            let occ = trait_occurrences.entry(trait_name).or_insert(0);
                            if let Some(dict_expr) = self
                                .resolve_call_dict_nth(
                                    trait_name, func.id, node_id, func.span, *occ,
                                )
                                .or_else(|| {
                                    (*occ == 0)
                                        .then(|| {
                                            self.resolve_dict_from_arg_type(
                                                trait_name, arg, func.span,
                                            )
                                        })
                                        .flatten()
                                })
                            {
                                result = Expr::synth(
                                    span,
                                    ExprKind::App {
                                        func: Box::new(result),
                                        arg: Box::new(dict_expr),
                                    },
                                );
                            }
                            *occ += 1;
                        }
                        return Expr::rebuild_like(
                            expr,
                            ExprKind::App {
                                func: Box::new(result),
                                arg: Box::new(elab_arg),
                            },
                        );
                    }
                }

                // Also handle nested App chains (multi-arg calls)
                // For App(App(Var(f), arg1), arg2) where f has dict params,
                // we need to insert dicts before the first user arg.
                // The single-arg case above handles most uses; multi-arg
                // is handled by the lowerer's collect_fun_call.

                Expr::rebuild_like(
                    expr,
                    ExprKind::App {
                        func: Box::new(self.elaborate_expr(func)),
                        arg: Box::new(self.elaborate_expr(arg)),
                    },
                )
            }

            // Recurse into all other expression forms
            ExprKind::Lit { .. } | ExprKind::Constructor { .. } => expr.clone(),

            ExprKind::BinOp { op, left, right } => {
                if matches!(op, BinOp::Concat)
                    && let Some(combine_expr) =
                        self.desugar_semigroup_concat(left, right, node_id, span)
                {
                    return combine_expr;
                }

                // Rewrite comparison operators to `compare` calls for non-primitive types.
                // Primitives (Int, Float, String) keep using BEAM BIFs directly.
                if matches!(op, BinOp::Lt | BinOp::Gt | BinOp::LtEq | BinOp::GtEq) {
                    let is_primitive = self
                        .evidence_by_node
                        .get(&node_id)
                        .and_then(|evs| evs.iter().find(|ev| ev.trait_name == ORD))
                        .and_then(|ev| ev.resolved_type.as_ref())
                        .is_some_and(|(name, _)| {
                            [
                                crate::typechecker::canonicalize_type_name("Int"),
                                crate::typechecker::canonicalize_type_name("Float"),
                                crate::typechecker::canonicalize_type_name("String"),
                            ]
                            .contains(&name.as_str())
                        });

                    if !is_primitive
                        && let Some(compare_expr) =
                            self.desugar_comparison(op, left, right, node_id, span)
                    {
                        return compare_expr;
                    }
                }

                // Rewrite Div to IntDiv when the Num constraint resolved to Int,
                // and Mod to FloatMod when resolved to Float.
                let elaborated_op = if *op == BinOp::FloatDiv {
                    let is_int = self
                        .evidence_by_node
                        .get(&node_id)
                        .and_then(|evs| evs.iter().find(|ev| ev.trait_name == "Num"))
                        .and_then(|ev| ev.resolved_type.as_ref())
                        .is_some_and(|(name, _)| {
                            name == crate::typechecker::canonicalize_type_name("Int")
                        });
                    if is_int {
                        BinOp::IntDiv
                    } else {
                        BinOp::FloatDiv
                    }
                } else if *op == BinOp::Mod {
                    let is_float = self
                        .evidence_by_node
                        .get(&node_id)
                        .and_then(|evs| evs.iter().find(|ev| ev.trait_name == "Num"))
                        .and_then(|ev| ev.resolved_type.as_ref())
                        .is_some_and(|(name, _)| {
                            name == crate::typechecker::canonicalize_type_name("Float")
                        });
                    if is_float {
                        BinOp::FloatMod
                    } else {
                        BinOp::Mod
                    }
                } else {
                    op.clone()
                };
                Expr::rebuild_like(
                    expr,
                    ExprKind::BinOp {
                        op: elaborated_op,
                        left: Box::new(self.elaborate_expr(left)),
                        right: Box::new(self.elaborate_expr(right)),
                    },
                )
            }

            ExprKind::UnaryMinus { expr: e } => Expr::rebuild_like(
                expr,
                ExprKind::UnaryMinus {
                    expr: Box::new(self.elaborate_expr(e)),
                },
            ),

            ExprKind::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => Expr::rebuild_like(
                expr,
                ExprKind::If {
                    cond: Box::new(self.elaborate_expr(cond)),
                    then_branch: Box::new(self.elaborate_expr(then_branch)),
                    else_branch: Box::new(self.elaborate_expr(else_branch)),
                    multiline: false,
                },
            ),

            ExprKind::Case {
                scrutinee, arms, ..
            } => Expr::rebuild_like(
                expr,
                ExprKind::Case {
                    dangling_trivia: vec![],
                    scrutinee: Box::new(self.elaborate_expr(scrutinee)),
                    arms: arms
                        .iter()
                        .map(|ann| {
                            let arm = &ann.node;
                            Annotated::bare(CaseArm {
                                pattern: arm.pattern.clone(),
                                guard: arm.guard.as_ref().map(|g| self.elaborate_expr(g)),
                                body: self.elaborate_expr(&arm.body),
                                span: arm.span,
                            })
                        })
                        .collect(),
                },
            ),

            ExprKind::Block { stmts, .. } => Expr::rebuild_like(
                expr,
                ExprKind::Block {
                    dangling_trivia: vec![],
                    stmts: stmts
                        .iter()
                        .map(|ann| {
                            let s = &ann.node;
                            Annotated::bare(match s {
                                Stmt::Let {
                                    pattern,
                                    annotation,
                                    value,
                                    assert,
                                    span,
                                } => {
                                    // Check if this specific let binding has trait constraints.
                                    // Use pat_id to distinguish same-named bindings in
                                    // different scopes (e.g. `result` in multiple test bodies).
                                    let dict_info = if let Pat::Var { name, id, .. } = pattern {
                                        let is_this_binding = self
                                            .let_dict_pat_ids
                                            .get(name.as_str())
                                            .is_some_and(|ids| ids.contains(id));
                                        if is_this_binding {
                                            self.fun_dict_params_for_callee(name, *id)
                                        } else {
                                            None
                                        }
                                    } else {
                                        None
                                    };

                                    if let Some(dict_param_info) = dict_info {
                                        // Set up dict params for elaborating the value.
                                        // Keep enclosing dicts visible: a constrained local
                                        // binding may call helpers that also need the outer
                                        // function's where-clause evidence.
                                        // Eta-expand: `let f = value` becomes
                                        // `let f = fun (dict, __arg) -> (elaborated_val)(__arg)`
                                        // so the lowerer sees a single function of arity N+1.
                                        let saved = (
                                            self.current_dict_params.clone(),
                                            self.current_dict_params_by_var.clone(),
                                        );
                                        let mut lambda_params = Vec::new();

                                        for (trait_name, type_var) in &dict_param_info {
                                            let bare =
                                                trait_name.rsplit('.').next().unwrap_or(trait_name);
                                            let param_name =
                                                format!("__dict_{}_{}", bare, type_var);
                                            self.current_dict_params
                                                .insert(trait_name.clone(), param_name.clone());
                                            self.current_dict_params_by_var.insert(
                                                (trait_name.clone(), type_var.clone()),
                                                param_name.clone(),
                                            );
                                            lambda_params.push(Pat::Var {
                                                id: NodeId::fresh(),
                                                name: param_name,
                                                span: *span,
                                            });
                                        }

                                        let elab_value = self.elaborate_expr(value);

                                        self.restore_dict_params(saved);

                                        // Eta-expand with the correct arity
                                        let let_name = if let Pat::Var { name: n, .. } = pattern {
                                            n
                                        } else {
                                            ""
                                        };
                                        let arity = self
                                            .let_binding_arities
                                            .get(let_name)
                                            .copied()
                                            .unwrap_or(1);
                                        let eta_params: Vec<String> =
                                            (0..arity).map(|i| format!("__let_arg{}", i)).collect();
                                        for p in &eta_params {
                                            lambda_params.push(Pat::Var {
                                                id: NodeId::fresh(),
                                                name: p.clone(),
                                                span: *span,
                                            });
                                        }
                                        // Apply the elaborated value to each eta param
                                        let mut body = elab_value;
                                        for p in &eta_params {
                                            body = Expr::synth(
                                                *span,
                                                ExprKind::App {
                                                    func: Box::new(body),
                                                    arg: Box::new(Expr::synth(
                                                        *span,
                                                        ExprKind::Var { name: p.clone() },
                                                    )),
                                                },
                                            );
                                        }
                                        let wrapped = Expr::synth(
                                            *span,
                                            ExprKind::Lambda {
                                                params: lambda_params,
                                                body: Box::new(body),
                                            },
                                        );

                                        Stmt::Let {
                                            pattern: pattern.clone(),
                                            annotation: annotation.clone(),
                                            value: wrapped,
                                            assert: *assert,
                                            span: *span,
                                        }
                                    } else {
                                        Stmt::Let {
                                            pattern: pattern.clone(),
                                            annotation: annotation.clone(),
                                            value: self.elaborate_expr(value),
                                            assert: *assert,
                                            span: *span,
                                        }
                                    }
                                }
                                Stmt::LetFun {
                                    id,
                                    name,
                                    name_span,
                                    params,
                                    guard,
                                    body,
                                    span,
                                } => Stmt::LetFun {
                                    id: *id,
                                    name: name.clone(),
                                    name_span: *name_span,
                                    params: params.clone(),
                                    guard: guard.as_ref().map(|g| Box::new(self.elaborate_expr(g))),
                                    body: self.elaborate_expr(body),
                                    span: *span,
                                },

                                Stmt::Expr(e) => Stmt::Expr(self.elaborate_expr(e)),
                            })
                        })
                        .collect(),
                },
            ),

            ExprKind::Lambda { params, body } => Expr::rebuild_like(
                expr,
                ExprKind::Lambda {
                    params: params.clone(),
                    body: Box::new(self.elaborate_expr(body)),
                },
            ),

            ExprKind::FieldAccess { expr: e, field, .. } => {
                let record_name = self.resolve_record_name(e.id);
                Expr::rebuild_like(
                    expr,
                    ExprKind::FieldAccess {
                        expr: Box::new(self.elaborate_expr(e)),
                        field: field.clone(),
                        record_name,
                    },
                )
            }

            ExprKind::RecordCreate { name, fields, .. } => {
                // Pin the constructed record's canonical type name on the node, from
                // the name-resolver's per-node record-type map (the same source the
                // codegen NodeId path reads). Carrying it on the node makes the tuple
                // field order survive NodeId freshening during cross-module inlining
                // — the fragile path that dropped insert_all's fields.
                let record_name = self.resolution.record_type(expr.id).map(str::to_string);
                Expr::rebuild_like(
                    expr,
                    ExprKind::RecordCreate {
                        name: name.clone(),
                        fields: fields
                            .iter()
                            .map(|(n, s, e)| (n.clone(), *s, self.elaborate_expr(e)))
                            .collect(),
                        record_name,
                    },
                )
            }

            ExprKind::AnonRecordCreate { fields } => Expr::rebuild_like(
                expr,
                ExprKind::AnonRecordCreate {
                    fields: fields
                        .iter()
                        .map(|(n, s, e)| (n.clone(), *s, self.elaborate_expr(e)))
                        .collect(),
                },
            ),

            ExprKind::RecordUpdate { record, fields, .. } => {
                let record_name = self.resolve_record_name(record.id);
                Expr::rebuild_like(
                    expr,
                    ExprKind::RecordUpdate {
                        record: Box::new(self.elaborate_expr(record)),
                        fields: fields
                            .iter()
                            .map(|(n, s, e)| (n.clone(), *s, self.elaborate_expr(e)))
                            .collect(),
                        record_name,
                    },
                )
            }

            ExprKind::Tuple { elements } => Expr::rebuild_like(
                expr,
                ExprKind::Tuple {
                    elements: elements.iter().map(|e| self.elaborate_expr(e)).collect(),
                },
            ),

            ExprKind::Do {
                bindings,
                success,
                else_arms,
                ..
            } => Expr::rebuild_like(
                expr,
                ExprKind::Do {
                    dangling_trivia: vec![],
                    bindings: bindings
                        .iter()
                        .map(|(p, e)| (p.clone(), self.elaborate_expr(e)))
                        .collect(),
                    success: Box::new(self.elaborate_expr(success)),
                    else_arms: else_arms
                        .iter()
                        .map(|ann| {
                            let arm = &ann.node;
                            Annotated::bare(CaseArm {
                                pattern: arm.pattern.clone(),
                                guard: arm.guard.as_ref().map(|g| self.elaborate_expr(g)),
                                body: self.elaborate_expr(&arm.body),
                                span: arm.span,
                            })
                        })
                        .collect(),
                },
            ),

            ExprKind::QualifiedName { module, name, .. } => {
                let qualified = format!("{}.{}", module, name);
                // Dict-parameterized function used as a bare value (not directly applied).
                if let Some(dict_param_info) = self.fun_dict_params_for_callee(&qualified, node_id)
                {
                    let mut result: Expr = expr.clone();
                    let mut trait_occurrences: HashMap<&str, usize> = HashMap::new();
                    for (trait_name, _type_var) in &dict_param_info {
                        let occ = trait_occurrences.entry(trait_name).or_insert(0);
                        if let Some(dict_expr) =
                            self.resolve_dict_nth(trait_name, node_id, span, *occ)
                        {
                            result = Expr::synth(
                                span,
                                ExprKind::App {
                                    func: Box::new(result),
                                    arg: Box::new(dict_expr),
                                },
                            );
                        }
                        *occ += 1;
                    }
                    return result;
                }
                expr.clone()
            }

            ExprKind::EffectCall {
                name,
                qualifier,
                args,
            } => Expr::rebuild_like(
                expr,
                ExprKind::EffectCall {
                    name: name.clone(),
                    qualifier: qualifier.clone(),
                    args: args.iter().map(|a| self.elaborate_expr(a)).collect(),
                },
            ),

            ExprKind::With { expr: e, handler } => {
                let with_expr = Expr::rebuild_like(
                    expr,
                    ExprKind::With {
                        expr: Box::new(self.elaborate_expr(e)),
                        handler: Box::new(self.elaborate_handler(handler)),
                    },
                );

                // For named handlers with where clauses, bind the dict variables
                // so handler arm bodies (which reference e.g. `__dict_Show_a`) can
                // capture them from the enclosing scope.
                if let Handler::Named(named) = handler.as_ref() {
                    if let Some(dict_param_info) =
                        self.handler_dict_params.get(&named.name).cloned()
                    {
                        let mut stmts: Vec<Annotated<Stmt>> = Vec::new();
                        let mut trait_occurrences: HashMap<&str, usize> = HashMap::new();
                        for (trait_name, type_var) in &dict_param_info {
                            let occ = trait_occurrences.entry(trait_name).or_insert(0);
                            let bare = trait_name.rsplit('.').next().unwrap_or(trait_name);
                            let dict_var = format!("__dict_{}_{}", bare, type_var);
                            if let Some(dict_expr) =
                                self.resolve_dict_nth(trait_name, node_id, span, *occ)
                            {
                                stmts.push(Annotated::bare(Stmt::Let {
                                    pattern: Pat::Var {
                                        id: NodeId::fresh(),
                                        name: dict_var,
                                        span,
                                    },
                                    annotation: None,
                                    value: dict_expr,
                                    assert: false,
                                    span,
                                }));
                            }
                            *occ += 1;
                        }
                        if stmts.is_empty() {
                            with_expr
                        } else {
                            stmts.push(Annotated::bare(Stmt::Expr(with_expr)));
                            Expr::synth(
                                span,
                                ExprKind::Block {
                                    stmts,
                                    dangling_trivia: vec![],
                                },
                            )
                        }
                    } else {
                        with_expr
                    }
                } else {
                    with_expr
                }
            }

            ExprKind::HandlerExpr { body } => Expr::rebuild_like(
                expr,
                ExprKind::HandlerExpr {
                    body: HandlerBody {
                        effects: body.effects.clone(),
                        needs: body.needs.clone(),
                        where_clause: body.where_clause.clone(),
                        arms: {
                            let handler_pairs = self.dict_params_from_where(&body.where_clause);
                            body.arms
                                .iter()
                                .map(|ann| {
                                    let arm = &ann.node;
                                    let mut arm_pairs = handler_pairs.clone();
                                    arm_pairs.extend(self.op_dict_params_for_arm(arm));
                                    let saved = self.push_dict_params_from_pairs(&arm_pairs);
                                    let elab = Annotated::bare(HandlerArm {
                                        id: arm.id,
                                        op_name: arm.op_name.clone(),
                                        qualifier: arm.qualifier.clone(),
                                        params: arm.params.clone(),
                                        body: Box::new(self.elaborate_expr(&arm.body)),
                                        finally_block: arm
                                            .finally_block
                                            .as_ref()
                                            .map(|fb| Box::new(self.elaborate_expr(fb))),
                                        span: arm.span,
                                    });
                                    self.restore_dict_params(saved);
                                    elab
                                })
                                .collect()
                        },
                        return_clause: body.return_clause.as_ref().map(|rc| {
                            Box::new(HandlerArm {
                                id: rc.id,
                                op_name: rc.op_name.clone(),
                                qualifier: rc.qualifier.clone(),
                                params: rc.params.clone(),
                                body: Box::new(self.elaborate_expr(&rc.body)),
                                finally_block: None,
                                span: rc.span,
                            })
                        }),
                    },
                },
            ),

            ExprKind::Resume { value } => Expr::rebuild_like(
                expr,
                ExprKind::Resume {
                    value: Box::new(self.elaborate_expr(value)),
                },
            ),

            ExprKind::ForeignCall { module, func, args } => Expr::rebuild_like(
                expr,
                ExprKind::ForeignCall {
                    module: module.clone(),
                    func: func.clone(),
                    args: args.iter().map(|a| self.elaborate_expr(a)).collect(),
                },
            ),

            ExprKind::Receive {
                arms, after_clause, ..
            } => Expr::rebuild_like(
                expr,
                ExprKind::Receive {
                    dangling_trivia: vec![],
                    arms: arms
                        .iter()
                        .map(|ann| {
                            let arm = &ann.node;
                            Annotated::bare(CaseArm {
                                pattern: arm.pattern.clone(),
                                guard: arm.guard.as_ref().map(|g| self.elaborate_expr(g)),
                                body: self.elaborate_expr(&arm.body),
                                span: arm.span,
                            })
                        })
                        .collect(),
                    after_clause: after_clause.as_ref().map(|(timeout, body)| {
                        (
                            Box::new(self.elaborate_expr(timeout)),
                            Box::new(self.elaborate_expr(body)),
                        )
                    }),
                },
            ),

            ExprKind::Ascription { expr, .. } => self.elaborate_expr(expr),

            ExprKind::BitString { segments } => Expr::rebuild_like(
                expr,
                ExprKind::BitString {
                    segments: segments
                        .iter()
                        .map(|seg| BitSegment {
                            value: self.elaborate_expr(&seg.value),
                            size: seg.size.as_ref().map(|s| Box::new(self.elaborate_expr(s))),
                            specs: seg.specs.clone(),
                            span: seg.span,
                        })
                        .collect(),
                },
            ),

            // Elaboration-only variants (shouldn't appear in input)
            ExprKind::DictMethodAccess { .. }
            | ExprKind::DictSuperAccess { .. }
            | ExprKind::DictRef { .. }
            | ExprKind::SymbolIntrinsic { .. } => expr.clone(),

            ExprKind::Pipe { .. }
            | ExprKind::BinOpChain { .. }
            | ExprKind::PipeBack { .. }
            | ExprKind::ComposeForward { .. }
            | ExprKind::Cons { .. }
            | ExprKind::ListLit { .. }
            | ExprKind::StringInterp { .. }
            | ExprKind::ListComprehension { .. } => {
                unreachable!("surface syntax should be desugared before elaboration")
            }
        }
    }

    pub(crate) fn elaborate_handler(&mut self, handler: &Handler) -> Handler {
        match handler {
            Handler::Named(_) => handler.clone(),
            Handler::Inline { items, .. } => Handler::Inline {
                dangling_trivia: vec![],
                items: items
                    .iter()
                    .map(|ann| {
                        let mut elaborate_arm = |arm: &HandlerArm| {
                            // Bring the op's own `where`-constraint dicts into
                            // scope so trait calls in the arm body resolve to the
                            // per-call dict threaded as a trailing op arg.
                            let arm_pairs = self.op_dict_params_for_arm(arm);
                            let saved = self.push_dict_params_from_pairs(&arm_pairs);
                            let elab = HandlerArm {
                                id: arm.id,
                                op_name: arm.op_name.clone(),
                                qualifier: arm.qualifier.clone(),
                                params: arm.params.clone(),
                                body: Box::new(self.elaborate_expr(&arm.body)),
                                finally_block: arm
                                    .finally_block
                                    .as_ref()
                                    .map(|fb| Box::new(self.elaborate_expr(fb))),
                                span: arm.span,
                            };
                            self.restore_dict_params(saved);
                            elab
                        };
                        match &ann.node {
                            HandlerItem::Named(_) => ann.clone(),
                            HandlerItem::Arm(arm) => {
                                Annotated::bare(HandlerItem::Arm(elaborate_arm(arm)))
                            }
                            HandlerItem::Return(arm) => {
                                Annotated::bare(HandlerItem::Return(elaborate_arm(arm)))
                            }
                        }
                    })
                    .collect(),
            },
        }
    }

    /// Check if a node has trait evidence that matches a known trait method name.
    /// Returns (trait_name, method_index) if this is a trait method call.
    ///
    /// Prefers the resolver's `ResolvedTraitMethod` when present (recorded
    /// per use-site NodeId). The resolver's `trait_name` is authoritative —
    /// look the method index up *inside that specific trait*, not in the
    /// flat name-keyed `self.trait_methods` table. The flat table contains
    /// every imported trait's methods regardless of exposing, so a
    /// method-name lookup can return the wrong trait when the same bare
    /// name appears in multiple imported traits.
    ///
    pub(crate) fn resolve_trait_method(
        &self,
        _name: &str,
        node_id: crate::ast::NodeId,
    ) -> Option<(String, usize)> {
        if let Some(resolved) = self.resolution.trait_method(node_id)
            && let Some(info) = self.traits.get(&resolved.trait_name)
            && let Some(idx) = info.methods.iter().position(|m| m.name == resolved.method)
        {
            return Some((resolved.trait_name.clone(), idx));
        }
        if let Some(canonical) = self.resolved_global_value_name(node_id)
            && let Some((trait_name, method)) = canonical.rsplit_once('.')
            && let Some(info) = self.traits.get(trait_name)
            && let Some(idx) = info.methods.iter().position(|m| m.name == method)
        {
            return Some((trait_name.to_string(), idx));
        }
        None
    }

    /// Rewrite `a < b` (etc.) into `compare a b == Lt` (etc.) using the Ord dict.
    ///
    /// Mapping: `<` -> `== Lt`, `>` -> `== Gt`, `<=` -> `!= Gt`, `>=` -> `!= Lt`
    pub(crate) fn desugar_comparison(
        &mut self,
        op: &BinOp,
        left: &Expr,
        right: &Expr,
        node_id: crate::ast::NodeId,
        span: Span,
    ) -> Option<Expr> {
        let dict_expr = self.resolve_dict(ORD, node_id, span)?;

        // Build: (DictMethodAccess(dict, 0)) left right
        // compare is method index 0 in Ord
        let compare_fn = Expr::synth(
            span,
            ExprKind::DictMethodAccess {
                dict: Box::new(dict_expr),
                trait_name: ORD.to_string(),
                method_index: 0,
            },
        );
        let elab_left = self.elaborate_expr(left);
        let elab_right = self.elaborate_expr(right);
        let compare_call = Expr::synth(
            span,
            ExprKind::App {
                func: Box::new(Expr::synth(
                    span,
                    ExprKind::App {
                        func: Box::new(compare_fn),
                        arg: Box::new(elab_left),
                    },
                )),
                arg: Box::new(elab_right),
            },
        );

        // Map operator to: (compare_result == Ctor) or (compare_result != Ctor)
        let (eq_op, ctor_name) = match op {
            BinOp::Lt => (BinOp::Eq, "Lt"),
            BinOp::Gt => (BinOp::Eq, "Gt"),
            BinOp::LtEq => (BinOp::NotEq, "Gt"),
            BinOp::GtEq => (BinOp::NotEq, "Lt"),
            _ => unreachable!(),
        };

        Some(Expr::synth(
            span,
            ExprKind::BinOp {
                op: eq_op,
                left: Box::new(compare_call),
                right: Box::new(Expr::synth(
                    span,
                    ExprKind::Constructor {
                        name: ctor_name.into(),
                    },
                )),
            },
        ))
    }

    /// Rewrite `a <> b` into `combine a b` using the Semigroup dict.
    pub(crate) fn desugar_semigroup_concat(
        &mut self,
        left: &Expr,
        right: &Expr,
        node_id: crate::ast::NodeId,
        span: Span,
    ) -> Option<Expr> {
        let dict_expr = self.resolve_dict(SEMIGROUP, node_id, span)?;
        let combine_fn = Expr::synth(
            span,
            ExprKind::DictMethodAccess {
                dict: Box::new(dict_expr),
                trait_name: SEMIGROUP.to_string(),
                method_index: 0,
            },
        );
        let elab_left = self.elaborate_expr(left);
        let elab_right = self.elaborate_expr(right);

        Some(Expr::synth(
            span,
            ExprKind::App {
                func: Box::new(Expr::synth(
                    span,
                    ExprKind::App {
                        func: Box::new(combine_fn),
                        arg: Box::new(elab_left),
                    },
                )),
                arg: Box::new(elab_right),
            },
        ))
    }

    /// If a `KnownSymbol` evidence record at `node_id` carries a concrete symbol
    /// name, return a lambda `fun _proxy -> SymbolIntrinsic { symbol }`. For
    /// the polymorphic case (where-bound `n : KnownSymbol`), return a lambda
    /// `fun _proxy -> __dict_KnownSymbol_n` referring to the in-scope dict
    /// parameter (which is itself the symbol's string at runtime — the
    /// KnownSymbol dict is carried as a bare String). The lambda ignores its
    /// Proxy argument (Proxy is a phantom). This shape preserves the trait-
    /// method calling convention so both bare references (`symbol_name`) and
    /// direct applications (`symbol_name p`) work uniformly.
    pub(crate) fn try_symbol_intrinsic_lambda(
        &self,
        node_id: crate::ast::NodeId,
        span: Span,
    ) -> Option<Expr> {
        let evidence_list = self.evidence_by_node.get(&node_id)?;
        let body = evidence_list.iter().find_map(|ev| {
            if ev.trait_name != KNOWN_SYMBOL_TRAIT {
                return None;
            }
            if let Some(name) = &ev.resolved_symbol {
                Some(Expr::synth(
                    span,
                    ExprKind::SymbolIntrinsic {
                        symbol: name.clone(),
                    },
                ))
            } else if let Some(var_name) = &ev.type_var_name {
                let bare = ev.trait_name.rsplit('.').next().unwrap_or(&ev.trait_name);
                let param_name = format!("__dict_{}_{}", bare, var_name);
                Some(Expr::synth(span, ExprKind::Var { name: param_name }))
            } else {
                None
            }
        })?;
        Some(Expr::synth(
            span,
            ExprKind::Lambda {
                params: vec![Pat::Var {
                    id: NodeId::fresh(),
                    name: "__proxy".into(),
                    span,
                }],
                body: Box::new(body),
            },
        ))
    }
}
