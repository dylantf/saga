//! Elaboration pass: transforms the AST to make trait dictionary passing explicit.
//!
//! Runs after typechecking, before lowering to Core Erlang. Uses the typechecker's
//! evidence (resolved trait constraints) to:
//! - Emit dictionary constructor functions for each trait impl
//! - Replace trait method calls with dictionary lookups
//! - Add dictionary parameters to functions with where clauses
//! - Insert dictionary arguments at call sites

use std::collections::HashMap;

use crate::ast::*;
use crate::token::Span;
use crate::typechecker::{CheckResult, TraitEvidence, TraitInfo, Type};

/// Elaborate a program using typechecker results.
/// Returns a new program with dictionary passing made explicit.
pub fn elaborate(program: &Program, result: &CheckResult) -> Program {
    elaborate_module(program, result, "")
}

/// Elaborate with a module name for module-qualified dict names.
pub fn elaborate_module(program: &Program, result: &CheckResult, module_name: &str) -> Program {
    let mut elab = Elaborator::new(result, module_name);
    elab.elaborate_program(program)
}

struct Elaborator {
    /// method_name -> (trait_name, method_index_in_trait)
    trait_methods: HashMap<String, (String, usize)>,
    /// fun_name -> [(trait_name, type_var_name)] from where clauses
    fun_dict_params: HashMap<String, Vec<(String, String)>>,
    /// (trait_name, target_type) -> dict constructor name
    dict_names: HashMap<(String, String), String>,
    /// (trait_name, target_type) -> ordered list of (constraint_trait, param_index) for dict params.
    /// Used to pass the correct sub-dicts when building parameterized dicts.
    impl_dict_params: HashMap<(String, String), Vec<(String, usize)>>,
    /// trait_name -> TraitInfo
    traits: HashMap<String, TraitInfo>,
    /// Evidence from typechecking: node_id -> Vec<TraitEvidence>
    evidence_by_node: HashMap<crate::ast::NodeId, Vec<TraitEvidence>>,
    /// The name of the function currently being elaborated (for dict param lookup)
    current_fun: Option<String>,
    /// Current function's dict param names: trait_name -> param_name
    current_dict_params: HashMap<String, String>,
    /// Current function's dict params keyed by (trait_name, type_var_suffix):
    /// e.g. ("Show", "v42") -> "__dict_Show_v42"
    current_dict_params_by_var: HashMap<(String, String), String>,
    /// Erlang module name for this module (e.g. "animals"), used for dict name qualification
    erlang_module: String,
}

impl Elaborator {
    fn new(result: &CheckResult, module_name: &str) -> Self {
        // Build inferred dict params from checker's env (for functions without
        // explicit where clauses that still have inferred trait constraints).
        // Traits that use operator dispatch, not dictionary dispatch.
        // These should not generate dict params.
        let operator_traits: std::collections::HashSet<&str> = ["Num", "Eq"].into_iter().collect();

        let mut inferred_dict_params: HashMap<String, Vec<(String, String)>> = HashMap::new();
        for (name, scheme) in result.env.iter() {
            if !scheme.constraints.is_empty() {
                let dict_params: Vec<(String, String)> = scheme
                    .constraints
                    .iter()
                    .filter(|(trait_name, _)| !operator_traits.contains(trait_name.as_str()))
                    .map(|(trait_name, var_id)| (trait_name.clone(), format!("v{}", var_id)))
                    .collect();
                if !dict_params.is_empty() {
                    inferred_dict_params.insert(name.to_string(), dict_params);
                }
            }
        }

        // Build evidence lookup by node ID
        let mut evidence_by_node: HashMap<crate::ast::NodeId, Vec<TraitEvidence>> = HashMap::new();
        for ev in &result.evidence {
            evidence_by_node
                .entry(ev.node_id)
                .or_default()
                .push(ev.clone());
        }

        // Erlang module name: "Foo.Bar" -> "foo_bar", "" -> ""
        let erlang_module = if module_name.is_empty() {
            String::new()
        } else {
            module_name
                .split('.')
                .map(|s| s.to_lowercase())
                .collect::<Vec<_>>()
                .join("_")
        };

        // Pre-populate dict_names from imported modules' codegen info
        let mut dict_names = HashMap::new();
        let mut impl_dict_params_from_imports: HashMap<(String, String), Vec<(String, usize)>> =
            HashMap::new();
        for info in result.codegen_info().values() {
            for d in &info.trait_impl_dicts {
                dict_names.insert(
                    (d.trait_name.clone(), d.target_type.clone()),
                    d.dict_name.clone(),
                );
                if !d.param_constraints.is_empty() {
                    impl_dict_params_from_imports.insert(
                        (d.trait_name.clone(), d.target_type.clone()),
                        d.param_constraints.clone(),
                    );
                }
            }
        }

        Elaborator {
            trait_methods: HashMap::new(),
            fun_dict_params: inferred_dict_params,
            dict_names,
            impl_dict_params: impl_dict_params_from_imports,
            traits: result.traits.clone(),
            evidence_by_node,
            current_fun: None,
            current_dict_params: HashMap::new(),
            current_dict_params_by_var: HashMap::new(),
            erlang_module,
        }
    }

    fn elaborate_program(&mut self, program: &Program) -> Program {
        // Pass 1: Collect trait method info and function where clauses
        for decl in program {
            match decl {
                Decl::TraitDef { name, methods, .. } => {
                    for (idx, method) in methods.iter().enumerate() {
                        if let Some((existing_trait, _)) = self.trait_methods.get(&method.name) {
                            panic!(
                                "trait method `{}` is defined in both `{}` and `{}`",
                                method.name, existing_trait, name
                            );
                        }
                        self.trait_methods
                            .insert(method.name.clone(), (name.clone(), idx));
                    }
                }
                Decl::FunAnnotation {
                    name, where_clause, ..
                }
                | Decl::ExternalFun {
                    name, where_clause, ..
                } => {
                    if !where_clause.is_empty() {
                        let mut dict_params = Vec::new();
                        for bound in where_clause {
                            for trait_name in &bound.traits {
                                if trait_name != "Num" && trait_name != "Eq" {
                                    dict_params
                                        .push((trait_name.clone(), bound.type_var.clone()));
                                }
                            }
                        }
                        if !dict_params.is_empty() {
                            self.fun_dict_params.insert(name.clone(), dict_params);
                        }
                    }
                }
                Decl::ImplDef {
                    trait_name,
                    target_type,
                    type_params,
                    where_clause,
                    ..
                } => {
                    let dict_name = if self.erlang_module.is_empty() {
                        format!("__dict_{}_{}", trait_name, target_type)
                    } else {
                        format!(
                            "__dict_{}_{}_{}",
                            trait_name, self.erlang_module, target_type
                        )
                    };
                    self.dict_names
                        .insert((trait_name.clone(), target_type.clone()), dict_name);
                    // Capture where-clause constraints as (trait, param_index) pairs.
                    // This tells dict_for_type which sub-dicts to pass for parameterized impls.
                    if !where_clause.is_empty() {
                        let var_to_idx: HashMap<&str, usize> = type_params
                            .iter()
                            .enumerate()
                            .map(|(i, name)| (name.as_str(), i))
                            .collect();
                        let params: Vec<(String, usize)> = where_clause
                            .iter()
                            .flat_map(|bound| {
                                let idx = var_to_idx
                                    .get(bound.type_var.as_str())
                                    .copied()
                                    .unwrap_or(0);
                                bound.traits.iter().map(move |t| (t.clone(), idx))
                            })
                            .collect();
                        self.impl_dict_params
                            .insert((trait_name.clone(), target_type.clone()), params);
                    }
                }
                _ => {}
            }
        }

        // Register trait methods from checker's trait info (for traits not
        // defined in the current program, e.g. Show in Std modules).
        for (trait_name, info) in &self.traits {
            for (idx, (method_name, _, _)) in info.methods.iter().enumerate() {
                self.trait_methods
                    .entry(method_name.clone())
                    .or_insert_with(|| (trait_name.clone(), idx));
            }
        }

        // Pass 2: Emit new program with dict constructors and elaborated functions
        let mut output = Vec::new();

        for decl in program {
            match decl {
                // Emit DictConstructor for each impl
                Decl::ImplDef {
                    trait_name,
                    target_type,
                    type_params,
                    where_clause,
                    methods,
                    span,
                    ..
                } => {
                    let dict_name = self
                        .dict_names
                        .get(&(trait_name.clone(), target_type.clone()))
                        .cloned()
                        .unwrap();

                    let trait_info = self.traits.get(trait_name).cloned();

                    // Build dict_params for conditional impls
                    let mut dict_params = Vec::new();
                    for bound in where_clause {
                        for req_trait in &bound.traits {
                            dict_params.push(format!("__dict_{}_{}", req_trait, bound.type_var));
                        }
                    }

                    // Set up current dict params for elaborating method bodies
                    let saved_dict_params = std::mem::take(&mut self.current_dict_params);
                    let saved_dict_params_by_var =
                        std::mem::take(&mut self.current_dict_params_by_var);
                    for bound in where_clause {
                        for req_trait in &bound.traits {
                            let param_name = format!("__dict_{}_{}", req_trait, bound.type_var);
                            self.current_dict_params
                                .insert(req_trait.clone(), param_name.clone());
                            self.current_dict_params_by_var
                                .insert((req_trait.clone(), bound.type_var.clone()), param_name);
                        }
                    }

                    // Order methods by trait declaration order
                    let mut ordered_methods = Vec::new();
                    if let Some(ref info) = trait_info {
                        for (trait_method_name, _, _) in &info.methods {
                            if let Some((_, params, body)) =
                                methods.iter().find(|(n, _, _)| n == trait_method_name)
                            {
                                let elab_body = self.elaborate_expr(body);
                                ordered_methods.push(Expr::synth(
                                    *span,
                                    ExprKind::Lambda {
                                        params: params.clone(),
                                        body: Box::new(elab_body),
                                    },
                                ));
                            }
                        }
                    }

                    self.current_dict_params = saved_dict_params;
                    self.current_dict_params_by_var = saved_dict_params_by_var;

                    // For parameterized types, if there are type_params but no where_clause,
                    // no dict params are needed. The dict is still nullary.
                    let _ = type_params; // acknowledge but don't use for now

                    output.push(Decl::DictConstructor {
                        name: dict_name,
                        dict_params,
                        methods: ordered_methods,
                        span: *span,
                    });
                }

                // TraitDef and FunAnnotation are consumed (not emitted)
                Decl::TraitDef { .. } => {}
                Decl::FunAnnotation { .. } => {
                    // Keep annotations for the lowerer (it uses them for arity).
                    output.push(decl.clone());
                }

                // Elaborate function bodies
                Decl::FunBinding {
                    name,
                    params,
                    guard,
                    body,
                    span,
                } => {
                    self.current_fun = Some(name.clone());

                    // Set up dict params for this function
                    let saved_dict_params = std::mem::take(&mut self.current_dict_params);
                    let saved_dict_params_by_var =
                        std::mem::take(&mut self.current_dict_params_by_var);
                    let mut extra_params = Vec::new();

                    if let Some(dict_param_info) = self.fun_dict_params.get(name) {
                        for (trait_name, type_var) in dict_param_info {
                            let param_name = format!("__dict_{}_{}", trait_name, type_var);
                            self.current_dict_params
                                .insert(trait_name.clone(), param_name.clone());
                            self.current_dict_params_by_var
                                .insert((trait_name.clone(), type_var.clone()), param_name.clone());
                            extra_params.push(Pat::Var {
                                name: param_name,
                                span: *span,
                            });
                        }
                    }

                    let elab_body = self.elaborate_expr(body);
                    let elab_guard = guard.as_ref().map(|g| Box::new(self.elaborate_expr(g)));

                    // Prepend dict params to the function's params
                    let mut full_params = extra_params;
                    full_params.extend(params.clone());

                    self.current_dict_params = saved_dict_params;
                    self.current_dict_params_by_var = saved_dict_params_by_var;
                    self.current_fun = None;

                    output.push(Decl::FunBinding {
                        name: name.clone(),
                        params: full_params,
                        guard: elab_guard,
                        body: elab_body,
                        span: *span,
                    });
                }

                // Elaborate handler arm bodies (so print/show get dicts inserted)
                Decl::HandlerDef {
                    public,
                    name,
                    name_span,
                    effects,
                    needs,
                    arms,
                    return_clause,
                    span,
                } => {
                    let elab_arms: Vec<HandlerArm> = arms
                        .iter()
                        .map(|arm| HandlerArm {
                            op_name: arm.op_name.clone(),
                            params: arm.params.clone(),
                            body: Box::new(self.elaborate_expr(&arm.body)),
                            span: arm.span,
                        })
                        .collect();
                    let elab_return = return_clause.as_ref().map(|rc| {
                        Box::new(HandlerArm {
                            op_name: rc.op_name.clone(),
                            params: rc.params.clone(),
                            body: Box::new(self.elaborate_expr(&rc.body)),
                            span: rc.span,
                        })
                    });
                    output.push(Decl::HandlerDef {
                        public: *public,
                        name: name.clone(),
                        name_span: *name_span,
                        effects: effects.clone(),
                        needs: needs.clone(),
                        arms: elab_arms,
                        return_clause: elab_return,
                        span: *span,
                    });
                }

                // Pass through everything else
                _ => output.push(decl.clone()),
            }
        }

        output
    }

    fn elaborate_expr(&mut self, expr: &Expr) -> Expr {
        let span = expr.span;
        let node_id = expr.id;
        match &expr.kind {
            // Trait method reference: look up evidence to determine dispatch
            ExprKind::Var { name } => {
                // Evidence-first: only treat as a trait method if the typechecker
                // recorded evidence at this node. This correctly handles shadowing
                // (a user function named `compare` won't be mistaken for Ord.compare).
                if let Some((trait_name, method_index)) = self.resolve_trait_method(name, node_id) {
                    if let Some(dict_expr) = self.resolve_dict(&trait_name, node_id, span) {
                        return Expr::synth(
                            span,
                            ExprKind::DictMethodAccess {
                                dict: Box::new(dict_expr),
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
                if let Some(dict_param_info) = self.fun_dict_params.get(name).cloned() {
                    let mut result: Expr = expr.clone();
                    for (trait_name, _type_var) in &dict_param_info {
                        if let Some(dict_expr) = self.resolve_dict(trait_name, node_id, span) {
                            result = Expr::synth(
                                span,
                                ExprKind::App {
                                    func: Box::new(result),
                                    arg: Box::new(dict_expr),
                                },
                            );
                        }
                    }
                    return result;
                }

                expr.clone()
            }

            // Function application: check if we need to insert dict args
            ExprKind::App { func, arg } => {
                // Check if this is a direct call to a function with where clauses
                if let ExprKind::Var { name, .. } = &func.kind {
                    // Evidence-first: check if the typechecker identified this as
                    // a trait method call before attempting dict dispatch.
                    if let Some((trait_name, method_index)) =
                        self.resolve_trait_method(name, func.id)
                    {
                        if let Some(dict_expr) = self.resolve_dict(&trait_name, func.id, func.span)
                        {
                            let elab_arg = self.elaborate_expr(arg);
                            let method = Expr::synth(
                                func.span,
                                ExprKind::DictMethodAccess {
                                    dict: Box::new(dict_expr),
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
                    if let Some(dict_param_info) = self.fun_dict_params.get(name).cloned() {
                        let elab_arg = self.elaborate_expr(arg);
                        // Build the call with dict args prepended
                        let mut result: Expr =
                            Expr::synth(func.span, ExprKind::Var { name: name.clone() });
                        for (trait_name, _type_var) in &dict_param_info {
                            // Use the Var's span for evidence lookup (that's where
                            // the typechecker recorded it), not the App's span.
                            if let Some(dict_expr) =
                                self.resolve_dict(trait_name, func.id, func.span)
                            {
                                result = Expr::synth(
                                    span,
                                    ExprKind::App {
                                        func: Box::new(result),
                                        arg: Box::new(dict_expr),
                                    },
                                );
                            }
                        }
                        return Expr::synth(
                            span,
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
                        && let Some(dict_expr) = self.resolve_dict(&trait_name, func.id, func.span)
                    {
                        let elab_arg = self.elaborate_expr(arg);
                        let method = Expr::synth(
                            func.span,
                            ExprKind::DictMethodAccess {
                                dict: Box::new(dict_expr),
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
                    if let Some(dict_param_info) = self.fun_dict_params.get(&qualified).cloned() {
                        let elab_arg = self.elaborate_expr(arg);
                        let mut result: Expr = func.as_ref().clone();
                        for (trait_name, _type_var) in &dict_param_info {
                            if let Some(dict_expr) =
                                self.resolve_dict(trait_name, func.id, func.span)
                            {
                                result = Expr::synth(
                                    span,
                                    ExprKind::App {
                                        func: Box::new(result),
                                        arg: Box::new(dict_expr),
                                    },
                                );
                            }
                        }
                        return Expr::synth(
                            span,
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

                Expr::synth(
                    span,
                    ExprKind::App {
                        func: Box::new(self.elaborate_expr(func)),
                        arg: Box::new(self.elaborate_expr(arg)),
                    },
                )
            }

            // Recurse into all other expression forms
            ExprKind::Lit { .. } | ExprKind::Constructor { .. } => expr.clone(),

            ExprKind::BinOp { op, left, right } => {
                // Rewrite comparison operators to `compare` calls for non-primitive types.
                // Primitives (Int, Float, String) keep using BEAM BIFs directly.
                if matches!(op, BinOp::Lt | BinOp::Gt | BinOp::LtEq | BinOp::GtEq) {
                    let is_primitive = self
                        .evidence_by_node
                        .get(&node_id)
                        .and_then(|evs| evs.iter().find(|ev| ev.trait_name == "Ord"))
                        .and_then(|ev| ev.resolved_type.as_ref())
                        .is_some_and(|(name, _)| {
                            matches!(name.as_str(), "Int" | "Float" | "String")
                        });

                    if !is_primitive
                        && let Some(compare_expr) =
                            self.desugar_comparison(op, left, right, node_id, span)
                    {
                        return compare_expr;
                    }
                }

                // Rewrite Div to IntDiv when the Num constraint resolved to Int
                let elaborated_op = if *op == BinOp::FloatDiv {
                    let is_int = self
                        .evidence_by_node
                        .get(&node_id)
                        .and_then(|evs| evs.iter().find(|ev| ev.trait_name == "Num"))
                        .and_then(|ev| ev.resolved_type.as_ref())
                        .is_some_and(|(name, _)| name == "Int");
                    if is_int {
                        BinOp::IntDiv
                    } else {
                        BinOp::FloatDiv
                    }
                } else {
                    op.clone()
                };
                Expr::synth(
                    span,
                    ExprKind::BinOp {
                        op: elaborated_op,
                        left: Box::new(self.elaborate_expr(left)),
                        right: Box::new(self.elaborate_expr(right)),
                    },
                )
            }

            ExprKind::UnaryMinus { expr: e } => Expr::synth(
                span,
                ExprKind::UnaryMinus {
                    expr: Box::new(self.elaborate_expr(e)),
                },
            ),

            ExprKind::If {
                cond,
                then_branch,
                else_branch,
            } => Expr::synth(
                span,
                ExprKind::If {
                    cond: Box::new(self.elaborate_expr(cond)),
                    then_branch: Box::new(self.elaborate_expr(then_branch)),
                    else_branch: Box::new(self.elaborate_expr(else_branch)),
                },
            ),

            ExprKind::Case { scrutinee, arms } => Expr::synth(
                span,
                ExprKind::Case {
                    scrutinee: Box::new(self.elaborate_expr(scrutinee)),
                    arms: arms
                        .iter()
                        .map(|arm| CaseArm {
                            pattern: arm.pattern.clone(),
                            guard: arm.guard.as_ref().map(|g| self.elaborate_expr(g)),
                            body: self.elaborate_expr(&arm.body),
                            span: arm.span,
                        })
                        .collect(),
                },
            ),

            ExprKind::Block { stmts } => Expr::synth(
                span,
                ExprKind::Block {
                    stmts: stmts
                        .iter()
                        .map(|s| match s {
                            Stmt::Let {
                                pattern,
                                annotation,
                                value,
                                assert,
                                span,
                            } => Stmt::Let {
                                pattern: pattern.clone(),
                                annotation: annotation.clone(),
                                value: self.elaborate_expr(value),
                                assert: *assert,
                                span: *span,
                            },
                            Stmt::LetFun {
                                name,
                                params,
                                guard,
                                body,
                                span,
                            } => Stmt::LetFun {
                                name: name.clone(),
                                params: params.clone(),
                                guard: guard.as_ref().map(|g| Box::new(self.elaborate_expr(g))),
                                body: self.elaborate_expr(body),
                                span: *span,
                            },
                            Stmt::Expr(e) => Stmt::Expr(self.elaborate_expr(e)),
                        })
                        .collect(),
                },
            ),

            ExprKind::Lambda { params, body } => Expr::synth(
                span,
                ExprKind::Lambda {
                    params: params.clone(),
                    body: Box::new(self.elaborate_expr(body)),
                },
            ),

            ExprKind::FieldAccess { expr: e, field } => Expr::synth(
                span,
                ExprKind::FieldAccess {
                    expr: Box::new(self.elaborate_expr(e)),
                    field: field.clone(),
                },
            ),

            ExprKind::RecordCreate { name, fields } => Expr::synth(
                span,
                ExprKind::RecordCreate {
                    name: name.clone(),
                    fields: fields
                        .iter()
                        .map(|(n, e)| (n.clone(), self.elaborate_expr(e)))
                        .collect(),
                },
            ),

            ExprKind::RecordUpdate { record, fields } => Expr::synth(
                span,
                ExprKind::RecordUpdate {
                    record: Box::new(self.elaborate_expr(record)),
                    fields: fields
                        .iter()
                        .map(|(n, e)| (n.clone(), self.elaborate_expr(e)))
                        .collect(),
                },
            ),

            ExprKind::Tuple { elements } => Expr::synth(
                span,
                ExprKind::Tuple {
                    elements: elements.iter().map(|e| self.elaborate_expr(e)).collect(),
                },
            ),

            ExprKind::Do {
                bindings,
                success,
                else_arms,
            } => Expr::synth(
                span,
                ExprKind::Do {
                    bindings: bindings
                        .iter()
                        .map(|(p, e)| (p.clone(), self.elaborate_expr(e)))
                        .collect(),
                    success: Box::new(self.elaborate_expr(success)),
                    else_arms: else_arms
                        .iter()
                        .map(|arm| CaseArm {
                            pattern: arm.pattern.clone(),
                            guard: arm.guard.as_ref().map(|g| self.elaborate_expr(g)),
                            body: self.elaborate_expr(&arm.body),
                            span: arm.span,
                        })
                        .collect(),
                },
            ),

            ExprKind::QualifiedName { module, name } => {
                let qualified = format!("{}.{}", module, name);
                // Dict-parameterized function used as a bare value (not directly applied).
                if let Some(dict_param_info) = self.fun_dict_params.get(&qualified).cloned() {
                    let mut result: Expr = expr.clone();
                    for (trait_name, _type_var) in &dict_param_info {
                        if let Some(dict_expr) = self.resolve_dict(trait_name, node_id, span) {
                            result = Expr::synth(
                                span,
                                ExprKind::App {
                                    func: Box::new(result),
                                    arg: Box::new(dict_expr),
                                },
                            );
                        }
                    }
                    return result;
                }
                expr.clone()
            }

            ExprKind::EffectCall {
                name,
                qualifier,
                args,
            } => Expr::synth(
                span,
                ExprKind::EffectCall {
                    name: name.clone(),
                    qualifier: qualifier.clone(),
                    args: args.iter().map(|a| self.elaborate_expr(a)).collect(),
                },
            ),

            ExprKind::With { expr: e, handler } => Expr::synth(
                span,
                ExprKind::With {
                    expr: Box::new(self.elaborate_expr(e)),
                    handler: Box::new(self.elaborate_handler(handler)),
                },
            ),

            ExprKind::Resume { value } => Expr::synth(
                span,
                ExprKind::Resume {
                    value: Box::new(self.elaborate_expr(value)),
                },
            ),

            ExprKind::ForeignCall { module, func, args } => Expr::synth(
                span,
                ExprKind::ForeignCall {
                    module: module.clone(),
                    func: func.clone(),
                    args: args.iter().map(|a| self.elaborate_expr(a)).collect(),
                },
            ),

            ExprKind::Receive { arms, after_clause } => Expr::synth(
                span,
                ExprKind::Receive {
                    arms: arms
                        .iter()
                        .map(|arm| CaseArm {
                            pattern: arm.pattern.clone(),
                            guard: arm.guard.as_ref().map(|g| self.elaborate_expr(g)),
                            body: self.elaborate_expr(&arm.body),
                            span: arm.span,
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

            // Elaboration-only variants (shouldn't appear in input)
            ExprKind::DictMethodAccess { .. } | ExprKind::DictRef { .. } => expr.clone(),
        }
    }

    fn elaborate_handler(&mut self, handler: &Handler) -> Handler {
        match handler {
            Handler::Named(_, _) => handler.clone(),
            Handler::Inline {
                named,
                arms,
                return_clause,
            } => Handler::Inline {
                named: named.clone(),
                arms: arms
                    .iter()
                    .map(|arm| HandlerArm {
                        op_name: arm.op_name.clone(),
                        params: arm.params.clone(),
                        body: Box::new(self.elaborate_expr(&arm.body)),
                        span: arm.span,
                    })
                    .collect(),
                return_clause: return_clause.as_ref().map(|arm| {
                    Box::new(HandlerArm {
                        op_name: arm.op_name.clone(),
                        params: arm.params.clone(),
                        body: Box::new(self.elaborate_expr(&arm.body)),
                        span: arm.span,
                    })
                }),
            },
        }
    }

    /// Check if a node has trait evidence that matches a known trait method name.
    /// Returns (trait_name, method_index) if this is a trait method call.
    /// This is the evidence-first approach: the typechecker is the authority on
    /// whether a name refers to a trait method or a user-defined function.
    fn resolve_trait_method(
        &self,
        name: &str,
        node_id: crate::ast::NodeId,
    ) -> Option<(String, usize)> {
        let evidence_list = self.evidence_by_node.get(&node_id)?;
        for ev in evidence_list {
            if let Some((trait_name, method_index)) = self.trait_methods.get(name)
                && *trait_name == ev.trait_name
            {
                return Some((trait_name.clone(), *method_index));
            }
        }
        None
    }

    /// Rewrite `a < b` (etc.) into `compare a b == Lt` (etc.) using the Ord dict.
    ///
    /// Mapping: `<` -> `== Lt`, `>` -> `== Gt`, `<=` -> `!= Gt`, `>=` -> `!= Lt`
    fn desugar_comparison(
        &mut self,
        op: &BinOp,
        left: &Expr,
        right: &Expr,
        node_id: crate::ast::NodeId,
        span: Span,
    ) -> Option<Expr> {
        let dict_expr = self.resolve_dict("Ord", node_id, span)?;

        // Build: (DictMethodAccess(dict, 0)) left right
        // compare is method index 0 in Ord
        let compare_fn = Expr::synth(
            span,
            ExprKind::DictMethodAccess {
                dict: Box::new(dict_expr),
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

    /// Resolve which dictionary to use for a given trait at a given node.
    /// Returns a DictRef expression or None if no evidence found.
    fn resolve_dict(
        &self,
        trait_name: &str,
        node_id: crate::ast::NodeId,
        span: Span,
    ) -> Option<Expr> {
        // Check if we have evidence for this node
        if let Some(evidence_list) = self.evidence_by_node.get(&node_id) {
            for ev in evidence_list {
                if ev.trait_name == trait_name {
                    return match &ev.resolved_type {
                        Some((type_name, args)) => {
                            // Concrete type: build the dict via dict_for_type,
                            // which handles where-clause constraints correctly.
                            let ty = Type::Con(type_name.clone(), args.clone());
                            self.dict_for_type(trait_name, &ty, span)
                        }
                        None => {
                            // Polymorphic: use the dict param from current function.
                            // If evidence has a type_var_name, use it to build the
                            // specific dict param name (handles multiple where-clause
                            // bounds for the same trait, e.g. `where {e: Show, a: Show}`).
                            if let Some(ref var_name) = ev.type_var_name {
                                let param_name = format!("__dict_{}_{}", trait_name, var_name);
                                Some(Expr::synth(span, ExprKind::Var { name: param_name }))
                            } else {
                                self.current_dict_params.get(trait_name).map(|name| {
                                    Expr::synth(span, ExprKind::Var { name: name.clone() })
                                })
                            }
                        }
                    };
                }
            }
        }

        // No evidence at this node -- fall back to current function's dict param
        // (handles inferred constraints where the typechecker absorbed the constraint
        // into the function's scheme rather than recording node-level evidence).
        if let Some(name) = self.current_dict_params.get(trait_name) {
            return Some(Expr::synth(span, ExprKind::Var { name: name.clone() }));
        }

        // No matching evidence for this trait. Might be a built-in trait
        // (Num, Eq, Ord) that doesn't use dictionary dispatch.
        None
    }

    /// Build the show function expression for a concrete type.
    /// Returns an expression that, when applied to a value of that type, produces a string.
    fn show_fn_for_type(&self, trait_name: &str, ty: &Type, span: Span) -> Option<Expr> {
        let dict = self.dict_for_type(trait_name, ty, span)?;
        Some(Expr::synth(
            span,
            ExprKind::DictMethodAccess {
                dict: Box::new(dict),
                method_index: 0,
            },
        ))
    }

    /// Build the dict expression for a concrete type (the dict itself, not the method).
    fn dict_for_type(&self, trait_name: &str, ty: &Type, span: Span) -> Option<Expr> {
        match ty {
            Type::Con(name, args) if name == "Tuple" && (trait_name == "Show" || trait_name == "Debug") => {
                // Tuples don't have a dict constructor; build an inline dict
                // containing the show lambda: {fun t -> "(" ++ ... ++ ")"}
                let show_lambda = self.build_tuple_show_lambda(trait_name, args, span)?;
                Some(Expr::synth(
                    span,
                    ExprKind::Tuple {
                        elements: vec![show_lambda],
                    },
                ))
            }
            Type::Con(name, args) => {
                let dict_name = self.dict_names.get(&(trait_name.into(), name.clone()))?;
                let mut dict_expr: Expr = Expr::synth(
                    span,
                    ExprKind::DictRef {
                        name: dict_name.clone(),
                    },
                );
                let key = (trait_name.to_string(), name.clone());
                if let Some(constraints) = self.impl_dict_params.get(&key) {
                    // Use explicit where-clause constraints (handles cases like
                    // Ord where the impl needs both Ord and Eq dicts per type param).
                    for (constraint_trait, param_idx) in constraints {
                        if let Some(arg_ty) = args.get(*param_idx) {
                            let sub_dict = self.dict_for_type(constraint_trait, arg_ty, span)?;
                            dict_expr = Expr::synth(
                                span,
                                ExprKind::App {
                                    func: Box::new(dict_expr),
                                    arg: Box::new(sub_dict),
                                },
                            );
                        }
                    }
                } else {
                    // Fallback: one sub-dict per type arg for the main trait.
                    // Works for simple cases like Show for List a where {a: Show}.
                    for arg_ty in args {
                        let sub_dict = self.dict_for_type(trait_name, arg_ty, span)?;
                        dict_expr = Expr::synth(
                            span,
                            ExprKind::App {
                                func: Box::new(dict_expr),
                                arg: Box::new(sub_dict),
                            },
                        );
                    }
                }
                Some(dict_expr)
            }
            Type::Var(id) => {
                // Polymorphic type var: look up the current function's dict param
                // for this trait + var combination.
                let var_key = format!("v{}", id);
                if let Some(param_name) = self
                    .current_dict_params_by_var
                    .get(&(trait_name.into(), var_key))
                {
                    return Some(Expr::synth(
                        span,
                        ExprKind::Var {
                            name: param_name.clone(),
                        },
                    ));
                }
                // Fall back to single-trait lookup
                self.current_dict_params
                    .get(trait_name)
                    .map(|name| Expr::synth(span, ExprKind::Var { name: name.clone() }))
            }
            _ => None,
        }
    }

    /// Check if the evidence at a node indicates Show for a Tuple type.
    /// If so, build an inline show expression for the tuple rather than
    /// using dictionary dispatch (since tuples are variable-arity).
    ///
    /// Returns a lambda: fun t -> "(" ++ show_T1(element(1,t)) ++ ", " ++ ... ++ ")"
    fn try_inline_tuple_show(
        &self,
        trait_name: &str,
        node_id: crate::ast::NodeId,
        span: Span,
    ) -> Option<Expr> {
        if trait_name != "Show" && trait_name != "Debug" {
            return None;
        }
        let evidence_list = self.evidence_by_node.get(&node_id)?;
        let tuple_ev = evidence_list.iter().find(|ev| {
            ev.trait_name == trait_name
                && ev
                    .resolved_type
                    .as_ref()
                    .is_some_and(|(name, _)| name == "Tuple")
        })?;
        let (_type_name, type_args) = tuple_ev.resolved_type.as_ref()?;
        self.build_tuple_show_lambda(trait_name, type_args, span)
    }

    /// Build a show/debug lambda for a tuple with the given element types.
    fn build_tuple_show_lambda(&self, trait_name: &str, type_args: &[Type], span: Span) -> Option<Expr> {
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
                        name: "__tup".into(),
                        span: s,
                    }],
                    body: Box::new(Expr::synth(
                        s,
                        ExprKind::Lit {
                            value: Lit::String("()".into()),
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
                                value: Lit::Int((i + 1) as i64),
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
                value: Lit::String("(".into()),
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
                                value: Lit::String(", ".into()),
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
                        value: Lit::String(")".into()),
                    },
                )),
            },
        );

        Some(Expr::synth(
            s,
            ExprKind::Lambda {
                params: vec![Pat::Var {
                    name: "__tup".into(),
                    span: s,
                }],
                body: Box::new(result),
            },
        ))
    }
}
