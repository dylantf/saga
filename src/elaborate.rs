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
use crate::typechecker::{Checker, TraitEvidence, TraitInfo, Type};

/// Elaborate a program using typechecker results.
/// Returns a new program with dictionary passing made explicit.
pub fn elaborate(program: &Program, checker: &Checker) -> Program {
    elaborate_module(program, checker, "")
}

/// Elaborate with a module name for module-qualified dict names.
pub fn elaborate_module(program: &Program, checker: &Checker, module_name: &str) -> Program {
    let mut elab = Elaborator::new(checker, module_name);
    elab.elaborate_program(program)
}

struct Elaborator {
    /// method_name -> (trait_name, method_index_in_trait)
    trait_methods: HashMap<String, (String, usize)>,
    /// fun_name -> [(trait_name, type_var_name)] from where clauses
    fun_dict_params: HashMap<String, Vec<(String, String)>>,
    /// (trait_name, target_type) -> dict constructor name
    dict_names: HashMap<(String, String), String>,
    /// trait_name -> TraitInfo
    traits: HashMap<String, TraitInfo>,
    /// Evidence from typechecking: span -> Vec<TraitEvidence>
    evidence_by_span: HashMap<Span, Vec<TraitEvidence>>,
    /// The name of the function currently being elaborated (for dict param lookup)
    current_fun: Option<String>,
    /// Current function's dict param names: trait_name -> param_name
    current_dict_params: HashMap<String, String>,
    /// Erlang module name for this module (e.g. "animals"), used for dict name qualification
    erlang_module: String,
}

impl Elaborator {
    fn new(checker: &Checker, module_name: &str) -> Self {
        // Build evidence lookup by span
        let mut evidence_by_span: HashMap<Span, Vec<TraitEvidence>> = HashMap::new();
        for ev in &checker.evidence {
            evidence_by_span
                .entry(ev.span)
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
        for info in checker.tc_codegen_info.values() {
            for (trait_name, target_type, dict_name, _arity) in &info.trait_impl_dicts {
                dict_names.insert((trait_name.clone(), target_type.clone()), dict_name.clone());
            }
        }

        Elaborator {
            trait_methods: HashMap::new(),
            fun_dict_params: HashMap::new(),
            dict_names,
            traits: checker.traits.clone(),
            evidence_by_span,
            current_fun: None,
            current_dict_params: HashMap::new(),
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
                } => {
                    if !where_clause.is_empty() {
                        let mut dict_params = Vec::new();
                        for bound in where_clause {
                            for trait_name in &bound.traits {
                                dict_params.push((trait_name.clone(), bound.type_var.clone()));
                            }
                        }
                        self.fun_dict_params.insert(name.clone(), dict_params);
                    }
                }
                Decl::ImplDef {
                    trait_name,
                    target_type,
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
                }
                _ => {}
            }
        }

        // Register built-in trait methods (Show is built-in, not in user TraitDefs)
        for (trait_name, info) in &self.traits {
            for (idx, (method_name, _, _)) in info.methods.iter().enumerate() {
                self.trait_methods
                    .entry(method_name.clone())
                    .or_insert_with(|| (trait_name.clone(), idx));
            }
        }

        // Register `print` as a dict-parameterized function (Show a => a -> Unit)
        self.fun_dict_params
            .insert("print".into(), vec![("Show".into(), "a".into())]);

        // Register built-in Show dicts
        for type_name in [
            "Int", "Float", "String", "Bool", "Unit", "List", "Maybe", "Result", "Dict",
        ] {
            let key = ("Show".to_string(), type_name.to_string());
            self.dict_names
                .entry(key)
                .or_insert_with(|| format!("__dict_Show_{}", type_name));
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
                    for bound in where_clause {
                        for req_trait in &bound.traits {
                            self.current_dict_params.insert(
                                req_trait.clone(),
                                format!("__dict_{}_{}", req_trait, bound.type_var),
                            );
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
                                ordered_methods.push(Expr::Lambda {
                                    params: params.clone(),
                                    body: Box::new(elab_body),
                                    span: *span,
                                });
                            }
                        }
                    }

                    self.current_dict_params = saved_dict_params;

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
                    // Keep annotations for the lowerer (it uses them for arity)
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
                    let mut extra_params = Vec::new();

                    if let Some(dict_param_info) = self.fun_dict_params.get(name) {
                        for (trait_name, type_var) in dict_param_info {
                            let param_name = format!("__dict_{}_{}", trait_name, type_var);
                            self.current_dict_params
                                .insert(trait_name.clone(), param_name.clone());
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

        // Emit synthesized `print` function: print(__dict_Show_a, x) = io:format(...)
        {
            let s = Span { start: 0, end: 0 };
            // Annotation so the lowerer knows print/2
            output.push(Decl::FunAnnotation {
                public: false,
                name: "print".into(),
                params: vec![
                    ("__dict_Show_a".into(), TypeExpr::Var("a".into())),
                    ("x".into(), TypeExpr::Var("a".into())),
                ],
                return_type: TypeExpr::Named("Unit".into()),
                effects: vec![],
                where_clause: vec![],
                span: s,
            });
            // Body: let s = show(x) in io:format("~s~n", [s])
            let show_x = Expr::App {
                func: Box::new(Expr::DictMethodAccess {
                    dict: Box::new(Expr::Var {
                        name: "__dict_Show_a".into(),
                        span: s,
                    }),
                    method_index: 0,
                    span: s,
                }),
                arg: Box::new(Expr::Var {
                    name: "x".into(),
                    span: s,
                }),
                span: s,
            };
            // io:format("~s~n", [show(x)]) -- build [show_x] as Cons(show_x, Nil)
            let args_list = Expr::App {
                func: Box::new(Expr::App {
                    func: Box::new(Expr::Constructor {
                        name: "Cons".into(),
                        span: s,
                    }),
                    arg: Box::new(show_x),
                    span: s,
                }),
                arg: Box::new(Expr::Constructor {
                    name: "Nil".into(),
                    span: s,
                }),
                span: s,
            };
            let print_body = Expr::ForeignCall {
                module: "io".into(),
                func: "format".into(),
                args: vec![
                    Expr::Lit {
                        value: Lit::String("~s~n".into()),
                        span: s,
                    },
                    args_list,
                ],
                span: s,
            };
            output.push(Decl::FunBinding {
                name: "print".into(),
                params: vec![
                    Pat::Var {
                        name: "__dict_Show_a".into(),
                        span: s,
                    },
                    Pat::Var {
                        name: "x".into(),
                        span: s,
                    },
                ],
                guard: None,
                body: print_body,
                span: s,
            });
        }

        // Emit built-in Show dict constructors
        let builtin_show_types: Vec<(&str, Vec<String>)> = vec![
            ("Int", vec![]),
            ("Float", vec![]),
            ("String", vec![]),
            ("Bool", vec![]),
            ("Unit", vec![]),
            ("List", vec!["__dict_Show_a".into()]),
            ("Maybe", vec!["__dict_Show_a".into()]),
            (
                "Result",
                vec!["__dict_Show_a".into(), "__dict_Show_b".into()],
            ),
            ("Dict", vec!["__dict_Show_a".into(), "__dict_Show_b".into()]),
        ];
        for (type_name, dict_params) in builtin_show_types {
            if let Some(methods) = self.builtin_show_methods(type_name) {
                output.push(Decl::DictConstructor {
                    name: format!("__dict_Show_{}", type_name),
                    dict_params,
                    methods,
                    span: Span { start: 0, end: 0 },
                });
            }
        }

        output
    }

    fn elaborate_expr(&mut self, expr: &Expr) -> Expr {
        match expr {
            // Trait method reference: look up evidence to determine dispatch
            Expr::Var { name, span } => {
                if let Some((trait_name, method_index)) = self.trait_methods.get(name).cloned() {
                    // This is a trait method name used as a bare value (not
                    // directly applied). Extract the method from the dict so
                    // it can be passed around as a first-class function.
                    if let Some(dict_expr) = self.resolve_dict(&trait_name, *span) {
                        return Expr::DictMethodAccess {
                            dict: Box::new(dict_expr),
                            method_index,
                            span: *span,
                        };
                    }
                    // Tuple Show: inline expansion (no dict constructor for tuples)
                    if let Some(show_lambda) = self.try_inline_tuple_show(&trait_name, *span) {
                        return show_lambda;
                    }
                    // No evidence resolved -- this trait method will be emitted as a
                    // bare variable, which will fail at runtime. This can happen if
                    // the typechecker recorded evidence at a different span.
                    debug_assert!(
                        false,
                        "unresolved trait method `{}` (trait `{}`) at {:?}",
                        name, trait_name, span
                    );
                }

                // Dict-parameterized function used as a bare value (not directly applied).
                // Partially apply the dict args so it can be passed as a first-class function.
                // e.g. `let p = print` becomes `let p = print __dict_Show_String`
                if let Some(dict_param_info) = self.fun_dict_params.get(name).cloned() {
                    let mut result: Expr = expr.clone();
                    for (trait_name, _type_var) in &dict_param_info {
                        if let Some(dict_expr) = self.resolve_dict(trait_name, *span) {
                            result = Expr::App {
                                func: Box::new(result),
                                arg: Box::new(dict_expr),
                                span: *span,
                            };
                        }
                    }
                    return result;
                }

                expr.clone()
            }

            // Function application: check if we need to insert dict args
            Expr::App { func, arg, span } => {
                // Check if this is a direct call to a function with where clauses
                if let Expr::Var { name, .. } = func.as_ref() {
                    // If calling a trait method directly with an argument,
                    // extract method from dict then apply normally.
                    if let Some((trait_name, method_index)) = self.trait_methods.get(name).cloned()
                    {
                        // Use the Var's span for evidence lookup (that's where
                        // the typechecker recorded it), not the App's span.
                        if let Some(dict_expr) = self.resolve_dict(&trait_name, func.span()) {
                            let elab_arg = self.elaborate_expr(arg);
                            let method = Expr::DictMethodAccess {
                                dict: Box::new(dict_expr),
                                method_index,
                                span: func.span(),
                            };
                            return Expr::App {
                                func: Box::new(method),
                                arg: Box::new(elab_arg),
                                span: *span,
                            };
                        }
                        // Tuple Show: inline expansion directly applied to the arg
                        if let Some(show_lambda) =
                            self.try_inline_tuple_show(&trait_name, func.span())
                        {
                            let elab_arg = self.elaborate_expr(arg);
                            return Expr::App {
                                func: Box::new(show_lambda),
                                arg: Box::new(elab_arg),
                                span: *span,
                            };
                        }
                    }

                    // If calling a function that has dict params, insert them
                    if let Some(dict_param_info) = self.fun_dict_params.get(name).cloned() {
                        let elab_arg = self.elaborate_expr(arg);
                        // Build the call with dict args prepended
                        let mut result: Expr = Expr::Var {
                            name: name.clone(),
                            span: func.span(),
                        };
                        for (trait_name, _type_var) in &dict_param_info {
                            // Use the Var's span for evidence lookup (that's where
                            // the typechecker recorded it), not the App's span.
                            if let Some(dict_expr) = self.resolve_dict(trait_name, func.span()) {
                                result = Expr::App {
                                    func: Box::new(result),
                                    arg: Box::new(dict_expr),
                                    span: *span,
                                };
                            }
                        }
                        return Expr::App {
                            func: Box::new(result),
                            arg: Box::new(elab_arg),
                            span: *span,
                        };
                    }
                }

                // Also handle nested App chains (multi-arg calls)
                // For App(App(Var(f), arg1), arg2) where f has dict params,
                // we need to insert dicts before the first user arg.
                // The single-arg case above handles most uses; multi-arg
                // is handled by the lowerer's collect_fun_call.

                Expr::App {
                    func: Box::new(self.elaborate_expr(func)),
                    arg: Box::new(self.elaborate_expr(arg)),
                    span: *span,
                }
            }

            // Recurse into all other expression forms
            Expr::Lit { .. } | Expr::Constructor { .. } => expr.clone(),

            Expr::BinOp {
                op,
                left,
                right,
                span,
            } => {
                // Rewrite Div to IntDiv when the Num constraint resolved to Int
                let elaborated_op = if *op == BinOp::FloatDiv {
                    let is_int = self
                        .evidence_by_span
                        .get(span)
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
                Expr::BinOp {
                    op: elaborated_op,
                    left: Box::new(self.elaborate_expr(left)),
                    right: Box::new(self.elaborate_expr(right)),
                    span: *span,
                }
            }

            Expr::UnaryMinus { expr: e, span } => Expr::UnaryMinus {
                expr: Box::new(self.elaborate_expr(e)),
                span: *span,
            },

            Expr::If {
                cond,
                then_branch,
                else_branch,
                span,
            } => Expr::If {
                cond: Box::new(self.elaborate_expr(cond)),
                then_branch: Box::new(self.elaborate_expr(then_branch)),
                else_branch: Box::new(self.elaborate_expr(else_branch)),
                span: *span,
            },

            Expr::Case {
                scrutinee,
                arms,
                span,
            } => Expr::Case {
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
                span: *span,
            },

            Expr::Block { stmts, span } => Expr::Block {
                stmts: stmts
                    .iter()
                    .map(|s| match s {
                        Stmt::Let {
                            pattern,
                            annotation,
                            value,
                            span,
                        } => Stmt::Let {
                            pattern: pattern.clone(),
                            annotation: annotation.clone(),
                            value: self.elaborate_expr(value),
                            span: *span,
                        },
                        Stmt::Expr(e) => Stmt::Expr(self.elaborate_expr(e)),
                    })
                    .collect(),
                span: *span,
            },

            Expr::Lambda { params, body, span } => Expr::Lambda {
                params: params.clone(),
                body: Box::new(self.elaborate_expr(body)),
                span: *span,
            },

            Expr::FieldAccess {
                expr: e,
                field,
                span,
            } => Expr::FieldAccess {
                expr: Box::new(self.elaborate_expr(e)),
                field: field.clone(),
                span: *span,
            },

            Expr::RecordCreate { name, fields, span } => Expr::RecordCreate {
                name: name.clone(),
                fields: fields
                    .iter()
                    .map(|(n, e)| (n.clone(), self.elaborate_expr(e)))
                    .collect(),
                span: *span,
            },

            Expr::RecordUpdate {
                record,
                fields,
                span,
            } => Expr::RecordUpdate {
                record: Box::new(self.elaborate_expr(record)),
                fields: fields
                    .iter()
                    .map(|(n, e)| (n.clone(), self.elaborate_expr(e)))
                    .collect(),
                span: *span,
            },

            Expr::Tuple { elements, span } => Expr::Tuple {
                elements: elements.iter().map(|e| self.elaborate_expr(e)).collect(),
                span: *span,
            },

            Expr::Do {
                bindings,
                success,
                else_arms,
                span,
            } => Expr::Do {
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
                span: *span,
            },

            Expr::QualifiedName { .. } => expr.clone(),

            Expr::EffectCall {
                name,
                qualifier,
                args,
                span,
            } => Expr::EffectCall {
                name: name.clone(),
                qualifier: qualifier.clone(),
                args: args.iter().map(|a| self.elaborate_expr(a)).collect(),
                span: *span,
            },

            Expr::With {
                expr: e,
                handler,
                span,
            } => Expr::With {
                expr: Box::new(self.elaborate_expr(e)),
                handler: Box::new(self.elaborate_handler(handler)),
                span: *span,
            },

            Expr::Resume { value, span } => Expr::Resume {
                value: Box::new(self.elaborate_expr(value)),
                span: *span,
            },

            Expr::ForeignCall {
                module,
                func,
                args,
                span,
            } => Expr::ForeignCall {
                module: module.clone(),
                func: func.clone(),
                args: args.iter().map(|a| self.elaborate_expr(a)).collect(),
                span: *span,
            },

            // Elaboration-only variants (shouldn't appear in input)
            Expr::DictMethodAccess { .. } | Expr::DictRef { .. } => expr.clone(),
        }
    }

    fn elaborate_handler(&mut self, handler: &Handler) -> Handler {
        match handler {
            Handler::Named(_) => handler.clone(),
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

    /// Resolve which dictionary to use for a given trait at a given span.
    /// Returns a DictRef expression or None if no evidence found.
    fn resolve_dict(&self, trait_name: &str, span: Span) -> Option<Expr> {
        // Check if we have evidence for this span
        let evidence_list = self.evidence_by_span.get(&span)?;
        for ev in evidence_list {
            if ev.trait_name == trait_name {
                return match &ev.resolved_type {
                    Some((type_name, args)) => {
                        // Concrete type: reference the dict constructor
                        let dict_name = self
                            .dict_names
                            .get(&(trait_name.to_string(), type_name.clone()))?;
                        let mut dict_expr: Expr = Expr::DictRef {
                            name: dict_name.clone(),
                            span,
                        };
                        // Apply sub-dictionaries for each type argument
                        for arg_ty in args {
                            if let Some(sub_dict) = self.dict_for_type(trait_name, arg_ty, span) {
                                dict_expr = Expr::App {
                                    func: Box::new(dict_expr),
                                    arg: Box::new(sub_dict),
                                    span,
                                };
                            }
                        }
                        Some(dict_expr)
                    }
                    None => {
                        // Polymorphic: use the dict param from current function
                        self.current_dict_params
                            .get(trait_name)
                            .map(|name| Expr::Var {
                                name: name.clone(),
                                span,
                            })
                    }
                };
            }
        }

        // No matching evidence for this trait. Might be a built-in trait
        // (Num, Eq, Ord) that doesn't use dictionary dispatch.
        None
    }

    /// Build the show function expression for a concrete type.
    /// Returns an expression that, when applied to a value of that type, produces a string.
    fn show_fn_for_type(&self, ty: &Type, span: Span) -> Option<Expr> {
        let dict = self.dict_for_type("Show", ty, span)?;
        Some(Expr::DictMethodAccess {
            dict: Box::new(dict),
            method_index: 0,
            span,
        })
    }

    /// Build the dict expression for a concrete type (the dict itself, not the method).
    fn dict_for_type(&self, trait_name: &str, ty: &Type, span: Span) -> Option<Expr> {
        match ty {
            Type::Con(name, args) => {
                let dict_name = self.dict_names.get(&(trait_name.into(), name.clone()))?;
                let mut dict_expr: Expr = Expr::DictRef {
                    name: dict_name.clone(),
                    span,
                };
                for arg_ty in args {
                    let sub_dict = self.dict_for_type(trait_name, arg_ty, span)?;
                    dict_expr = Expr::App {
                        func: Box::new(dict_expr),
                        arg: Box::new(sub_dict),
                        span,
                    };
                }
                Some(dict_expr)
            }
            _ => None,
        }
    }

    /// Check if the evidence at a span indicates Show for a Tuple type.
    /// If so, build an inline show expression for the tuple rather than
    /// using dictionary dispatch (since tuples are variable-arity).
    ///
    /// Returns a lambda: fun t -> "(" ++ show_T1(element(1,t)) ++ ", " ++ ... ++ ")"
    fn try_inline_tuple_show(&self, trait_name: &str, span: Span) -> Option<Expr> {
        if trait_name != "Show" {
            return None;
        }
        let evidence_list = self.evidence_by_span.get(&span)?;
        let tuple_ev = evidence_list.iter().find(|ev| {
            ev.trait_name == "Show"
                && ev
                    .resolved_type
                    .as_ref()
                    .is_some_and(|(name, _)| name == "Tuple")
        })?;
        let (_type_name, type_args) = tuple_ev.resolved_type.as_ref()?;

        let s = span;
        let t_var = Expr::Var {
            name: "__tup".into(),
            span: s,
        };

        // Build: "(" ++ show_T1(element(1, t)) ++ ", " ++ show_T2(element(2, t)) ++ ... ++ ")"
        let arity = type_args.len();
        if arity == 0 {
            // Empty tuple = unit, but this shouldn't happen (Unit is separate)
            return Some(Expr::Lambda {
                params: vec![Pat::Var {
                    name: "__tup".into(),
                    span: s,
                }],
                body: Box::new(Expr::Lit {
                    value: Lit::String("()".into()),
                    span: s,
                }),
                span: s,
            });
        }

        // Build the shown elements and join with ", "
        let mut parts: Vec<Expr> = Vec::new();
        for (i, elem_ty) in type_args.iter().enumerate() {
            let show_fn = self.show_fn_for_type(elem_ty, s)?;
            let elem = Expr::ForeignCall {
                module: "erlang".into(),
                func: "element".into(),
                args: vec![
                    Expr::Lit {
                        value: Lit::Int((i + 1) as i64),
                        span: s,
                    },
                    t_var.clone(),
                ],
                span: s,
            };
            parts.push(Expr::App {
                func: Box::new(show_fn),
                arg: Box::new(elem),
                span: s,
            });
        }

        // Join parts with ", " separators: "(" ++ p1 ++ ", " ++ p2 ++ ... ++ ")"
        let mut result = Expr::Lit {
            value: Lit::String("(".into()),
            span: s,
        };
        for (i, part) in parts.into_iter().enumerate() {
            if i > 0 {
                result = Expr::BinOp {
                    op: BinOp::Concat,
                    left: Box::new(result),
                    right: Box::new(Expr::Lit {
                        value: Lit::String(", ".into()),
                        span: s,
                    }),
                    span: s,
                };
            }
            result = Expr::BinOp {
                op: BinOp::Concat,
                left: Box::new(result),
                right: Box::new(part),
                span: s,
            };
        }
        result = Expr::BinOp {
            op: BinOp::Concat,
            left: Box::new(result),
            right: Box::new(Expr::Lit {
                value: Lit::String(")".into()),
                span: s,
            }),
            span: s,
        };

        Some(Expr::Lambda {
            params: vec![Pat::Var {
                name: "__tup".into(),
                span: s,
            }],
            body: Box::new(result),
            span: s,
        })
    }

    /// Generate the method lambdas for a built-in Show impl.
    /// Show has exactly one method (`show`), so returns a vec of one lambda.
    fn builtin_show_methods(&self, type_name: &str) -> Option<Vec<Expr>> {
        let s = Span { start: 0, end: 0 };
        let x_var = || Expr::Var {
            name: "x".into(),
            span: s,
        };
        let x_pat = Pat::Var {
            name: "x".into(),
            span: s,
        };

        let body = match type_name {
            "Int" => Expr::ForeignCall {
                module: "erlang".into(),
                func: "integer_to_list".into(),
                args: vec![x_var()],
                span: s,
            },
            "Float" => Expr::ForeignCall {
                module: "erlang".into(),
                func: "float_to_list".into(),
                args: vec![x_var()],
                span: s,
            },
            "String" => x_var(),
            "Bool" => Expr::Case {
                scrutinee: Box::new(x_var()),
                arms: vec![
                    CaseArm {
                        pattern: Pat::Constructor {
                            name: "True".into(),
                            args: vec![],
                            span: s,
                        },
                        guard: None,
                        body: Expr::Lit {
                            value: Lit::String("True".into()),
                            span: s,
                        },
                        span: s,
                    },
                    CaseArm {
                        pattern: Pat::Constructor {
                            name: "False".into(),
                            args: vec![],
                            span: s,
                        },
                        guard: None,
                        body: Expr::Lit {
                            value: Lit::String("False".into()),
                            span: s,
                        },
                        span: s,
                    },
                ],
                span: s,
            },
            "Unit" => Expr::Lit {
                value: Lit::String("()".into()),
                span: s,
            },
            "List" => {
                // fun xs ->
                //   let show_fn = element(1, __dict_Show_a)
                //   let mapped = lists:map(show_fn, xs)
                //   let joined = lists:join(", ", mapped)
                //   "[" ++ lists:flatten(joined) ++ "]"
                let show_fn = Expr::DictMethodAccess {
                    dict: Box::new(Expr::Var {
                        name: "__dict_Show_a".into(),
                        span: s,
                    }),
                    method_index: 0,
                    span: s,
                };
                let mapped = Expr::ForeignCall {
                    module: "lists".into(),
                    func: "map".into(),
                    args: vec![show_fn, x_var()],
                    span: s,
                };
                let joined = Expr::ForeignCall {
                    module: "lists".into(),
                    func: "join".into(),
                    args: vec![
                        Expr::Lit {
                            value: Lit::String(", ".into()),
                            span: s,
                        },
                        mapped,
                    ],
                    span: s,
                };
                let flat = Expr::ForeignCall {
                    module: "lists".into(),
                    func: "flatten".into(),
                    args: vec![joined],
                    span: s,
                };
                // "[" ++ flat ++ "]"
                Expr::BinOp {
                    op: BinOp::Concat,
                    left: Box::new(Expr::Lit {
                        value: Lit::String("[".into()),
                        span: s,
                    }),
                    right: Box::new(Expr::BinOp {
                        op: BinOp::Concat,
                        left: Box::new(flat),
                        right: Box::new(Expr::Lit {
                            value: Lit::String("]".into()),
                            span: s,
                        }),
                        span: s,
                    }),
                    span: s,
                }
            }
            "Maybe" => {
                // fun x -> case x { None -> "None", Some(v) -> "Some(" ++ show(v) ++ ")" }
                let show_v = Expr::App {
                    func: Box::new(Expr::DictMethodAccess {
                        dict: Box::new(Expr::Var {
                            name: "__dict_Show_a".into(),
                            span: s,
                        }),
                        method_index: 0,
                        span: s,
                    }),
                    arg: Box::new(Expr::Var {
                        name: "v".into(),
                        span: s,
                    }),
                    span: s,
                };
                Expr::Case {
                    scrutinee: Box::new(x_var()),
                    arms: vec![
                        CaseArm {
                            pattern: Pat::Constructor {
                                name: "None".into(),
                                args: vec![],
                                span: s,
                            },
                            guard: None,
                            body: Expr::Lit {
                                value: Lit::String("None".into()),
                                span: s,
                            },
                            span: s,
                        },
                        CaseArm {
                            pattern: Pat::Constructor {
                                name: "Some".into(),
                                args: vec![Pat::Var {
                                    name: "v".into(),
                                    span: s,
                                }],
                                span: s,
                            },
                            guard: None,
                            body: Expr::BinOp {
                                op: BinOp::Concat,
                                left: Box::new(Expr::Lit {
                                    value: Lit::String("Some(".into()),
                                    span: s,
                                }),
                                right: Box::new(Expr::BinOp {
                                    op: BinOp::Concat,
                                    left: Box::new(show_v),
                                    right: Box::new(Expr::Lit {
                                        value: Lit::String(")".into()),
                                        span: s,
                                    }),
                                    span: s,
                                }),
                                span: s,
                            },
                            span: s,
                        },
                    ],
                    span: s,
                }
            }
            "Result" => {
                // fun x -> case x {
                //   Ok(v) -> "Ok(" ++ show_a(v) ++ ")"
                //   Err(e) -> "Err(" ++ show_b(e) ++ ")"
                // }
                let show_a = |arg: Expr| Expr::App {
                    func: Box::new(Expr::DictMethodAccess {
                        dict: Box::new(Expr::Var {
                            name: "__dict_Show_a".into(),
                            span: s,
                        }),
                        method_index: 0,
                        span: s,
                    }),
                    arg: Box::new(arg),
                    span: s,
                };
                let show_b = |arg: Expr| Expr::App {
                    func: Box::new(Expr::DictMethodAccess {
                        dict: Box::new(Expr::Var {
                            name: "__dict_Show_b".into(),
                            span: s,
                        }),
                        method_index: 0,
                        span: s,
                    }),
                    arg: Box::new(arg),
                    span: s,
                };
                Expr::Case {
                    scrutinee: Box::new(x_var()),
                    arms: vec![
                        CaseArm {
                            pattern: Pat::Constructor {
                                name: "Ok".into(),
                                args: vec![Pat::Var {
                                    name: "v".into(),
                                    span: s,
                                }],
                                span: s,
                            },
                            guard: None,
                            body: Expr::BinOp {
                                op: BinOp::Concat,
                                left: Box::new(Expr::Lit {
                                    value: Lit::String("Ok(".into()),
                                    span: s,
                                }),
                                right: Box::new(Expr::BinOp {
                                    op: BinOp::Concat,
                                    left: Box::new(show_a(Expr::Var {
                                        name: "v".into(),
                                        span: s,
                                    })),
                                    right: Box::new(Expr::Lit {
                                        value: Lit::String(")".into()),
                                        span: s,
                                    }),
                                    span: s,
                                }),
                                span: s,
                            },
                            span: s,
                        },
                        CaseArm {
                            pattern: Pat::Constructor {
                                name: "Err".into(),
                                args: vec![Pat::Var {
                                    name: "e".into(),
                                    span: s,
                                }],
                                span: s,
                            },
                            guard: None,
                            body: Expr::BinOp {
                                op: BinOp::Concat,
                                left: Box::new(Expr::Lit {
                                    value: Lit::String("Err(".into()),
                                    span: s,
                                }),
                                right: Box::new(Expr::BinOp {
                                    op: BinOp::Concat,
                                    left: Box::new(show_b(Expr::Var {
                                        name: "e".into(),
                                        span: s,
                                    })),
                                    right: Box::new(Expr::Lit {
                                        value: Lit::String(")".into()),
                                        span: s,
                                    }),
                                    span: s,
                                }),
                                span: s,
                            },
                            span: s,
                        },
                    ],
                    span: s,
                }
            }
            "Dict" => {
                // fun d ->
                //   let pairs = maps:to_list(d)
                //   let show_pair = fun({k, v}) -> show_k(k) ++ ": " ++ show_v(v)
                //   let mapped = lists:map(show_pair, pairs)
                //   let joined = lists:join(", ", mapped)
                //   "{" ++ lists:flatten(joined) ++ "}"
                let show_k = |arg: Expr| Expr::App {
                    func: Box::new(Expr::DictMethodAccess {
                        dict: Box::new(Expr::Var {
                            name: "__dict_Show_a".into(),
                            span: s,
                        }),
                        method_index: 0,
                        span: s,
                    }),
                    arg: Box::new(arg),
                    span: s,
                };
                let show_v = |arg: Expr| Expr::App {
                    func: Box::new(Expr::DictMethodAccess {
                        dict: Box::new(Expr::Var {
                            name: "__dict_Show_b".into(),
                            span: s,
                        }),
                        method_index: 0,
                        span: s,
                    }),
                    arg: Box::new(arg),
                    span: s,
                };

                let pairs = Expr::ForeignCall {
                    module: "maps".into(),
                    func: "to_list".into(),
                    args: vec![x_var()],
                    span: s,
                };

                // Build: fun (k, v) -> show_k(k) ++ ": " ++ show_v(v)
                // On the BEAM, maps:to_list returns [{K,V}], so the lambda
                // receives an Erlang 2-tuple. Use erlang:element to extract.
                let pair_k = Expr::ForeignCall {
                    module: "erlang".into(),
                    func: "element".into(),
                    args: vec![
                        Expr::Lit {
                            value: Lit::Int(1),
                            span: s,
                        },
                        Expr::Var {
                            name: "pair".into(),
                            span: s,
                        },
                    ],
                    span: s,
                };
                let pair_v = Expr::ForeignCall {
                    module: "erlang".into(),
                    func: "element".into(),
                    args: vec![
                        Expr::Lit {
                            value: Lit::Int(2),
                            span: s,
                        },
                        Expr::Var {
                            name: "pair".into(),
                            span: s,
                        },
                    ],
                    span: s,
                };
                let show_pair_body = Expr::BinOp {
                    op: BinOp::Concat,
                    left: Box::new(show_k(pair_k)),
                    right: Box::new(Expr::BinOp {
                        op: BinOp::Concat,
                        left: Box::new(Expr::Lit {
                            value: Lit::String(": ".into()),
                            span: s,
                        }),
                        right: Box::new(show_v(pair_v)),
                        span: s,
                    }),
                    span: s,
                };
                let show_pair_fn = Expr::Lambda {
                    params: vec![Pat::Var {
                        name: "pair".into(),
                        span: s,
                    }],
                    body: Box::new(show_pair_body),
                    span: s,
                };

                let mapped = Expr::ForeignCall {
                    module: "lists".into(),
                    func: "map".into(),
                    args: vec![show_pair_fn, pairs],
                    span: s,
                };
                let joined = Expr::ForeignCall {
                    module: "lists".into(),
                    func: "join".into(),
                    args: vec![
                        Expr::Lit {
                            value: Lit::String(", ".into()),
                            span: s,
                        },
                        mapped,
                    ],
                    span: s,
                };
                let flat = Expr::ForeignCall {
                    module: "lists".into(),
                    func: "flatten".into(),
                    args: vec![joined],
                    span: s,
                };
                Expr::BinOp {
                    op: BinOp::Concat,
                    left: Box::new(Expr::Lit {
                        value: Lit::String("{".into()),
                        span: s,
                    }),
                    right: Box::new(Expr::BinOp {
                        op: BinOp::Concat,
                        left: Box::new(flat),
                        right: Box::new(Expr::Lit {
                            value: Lit::String("}".into()),
                            span: s,
                        }),
                        span: s,
                    }),
                    span: s,
                }
            }
            _ => return None,
        };

        Some(vec![Expr::Lambda {
            params: vec![x_pat],
            body: Box::new(body),
            span: s,
        }])
    }
}
