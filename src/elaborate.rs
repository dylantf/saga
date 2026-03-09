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
use crate::typechecker::{Checker, TraitEvidence, TraitInfo};

/// Elaborate a program using typechecker results.
/// Returns a new program with dictionary passing made explicit.
pub fn elaborate(program: &Program, checker: &Checker) -> Program {
    let mut elab = Elaborator::new(checker);
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
}

impl Elaborator {
    fn new(checker: &Checker) -> Self {
        // Build evidence lookup by span
        let mut evidence_by_span: HashMap<Span, Vec<TraitEvidence>> = HashMap::new();
        for ev in &checker.evidence {
            evidence_by_span
                .entry(ev.span)
                .or_default()
                .push(ev.clone());
        }

        Elaborator {
            trait_methods: HashMap::new(),
            fun_dict_params: HashMap::new(),
            dict_names: HashMap::new(),
            traits: checker.traits.clone(),
            evidence_by_span,
            current_fun: None,
            current_dict_params: HashMap::new(),
        }
    }

    fn elaborate_program(&mut self, program: &Program) -> Program {
        // Pass 1: Collect trait method info and function where clauses
        for decl in program {
            match decl {
                Decl::TraitDef { name, methods, .. } => {
                    for (idx, method) in methods.iter().enumerate() {
                        if let Some((existing_trait, _)) =
                            self.trait_methods.get(&method.name)
                        {
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
                    let dict_name = format!("__dict_{}_{}", trait_name, target_type);
                    self.dict_names
                        .insert((trait_name.clone(), target_type.clone()), dict_name);
                }
                _ => {}
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

                // Pass through everything else
                _ => output.push(decl.clone()),
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
                            if let Some(dict_expr) = self.resolve_dict(trait_name, *span) {
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
            } => Expr::BinOp {
                op: op.clone(),
                left: Box::new(self.elaborate_expr(left)),
                right: Box::new(self.elaborate_expr(right)),
                span: *span,
            },

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
                    Some((type_name, _args)) => {
                        // Concrete type: reference the dict constructor
                        let dict_name = self
                            .dict_names
                            .get(&(trait_name.to_string(), type_name.clone()));
                        dict_name.map(|name| Expr::DictRef {
                            name: name.clone(),
                            span,
                        })
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
}
