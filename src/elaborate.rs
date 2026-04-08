//! Elaboration pass: transforms the AST to make trait dictionary passing explicit.
//!
//! Runs after typechecking, before lowering to Core Erlang. Uses the typechecker's
//! evidence (resolved trait constraints) to:
//! - Emit dictionary constructor functions for each trait impl
//! - Replace trait method calls with dictionary lookups
//! - Add dictionary parameters to functions with where clauses
//! - Insert dictionary arguments at call sites

use std::collections::{HashMap, HashSet};

use crate::ast::*;
use crate::token::{Span, StringKind};
use crate::typechecker::{CheckResult, TraitEvidence, TraitInfo, Type};

/// Well-known canonical trait names used for special-cased codegen.
const SHOW: &str = "Std.Base.Show";
const DEBUG: &str = "Std.Base.Debug";
const ORD: &str = "Std.Base.Ord";

/// Impl key: (trait_name, trait_type_args, target_type).
/// e.g. ("ConvertTo", ["NOK"], "USD") or ("Show", [], "Int").
type ImplKey = (String, Vec<String>, String);

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
    /// handler_name -> [(trait_name, type_var_name)] from handler where clauses
    handler_dict_params: HashMap<String, Vec<(String, String)>>,
    /// impl key -> dict constructor name
    dict_names: HashMap<ImplKey, String>,
    /// impl key -> ordered list of (constraint_trait, param_index) for dict params.
    /// Used to pass the correct sub-dicts when building parameterized dicts.
    impl_dict_params: HashMap<ImplKey, Vec<(String, usize)>>,
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
    /// Arity of let-bound values with trait constraints (for eta-expansion)
    let_binding_arities: HashMap<String, usize>,
    /// Pat node IDs of let bindings that actually need dict wrapping.
    /// Used to avoid wrapping same-named bindings in different scopes.
    let_dict_pat_ids: HashMap<String, HashSet<crate::ast::NodeId>>,
    /// Scope map values for canonical name bridging (user name -> canonical)
    scope_map_values: HashMap<String, String>,
    /// Scope map traits for resolving bare trait names to canonical
    scope_map_traits: HashMap<String, String>,
}

impl Elaborator {
    fn new(result: &CheckResult, module_name: &str) -> Self {
        // Build inferred dict params from checker's env (for functions without
        // explicit where clauses that still have inferred trait constraints).
        // Traits that use operator dispatch, not dictionary dispatch.
        // These should not generate dict params.
        let operator_traits: std::collections::HashSet<&str> =
            ["Num", "Semigroup", "Eq"].into_iter().collect();

        let mut inferred_dict_params: HashMap<String, Vec<(String, String)>> = HashMap::new();
        for (name, scheme) in result.env.iter() {
            if !scheme.constraints.is_empty() {
                let dict_params: Vec<(String, String)> = scheme
                    .constraints
                    .iter()
                    .filter(|(trait_name, _, _)| !operator_traits.contains(trait_name.as_str()))
                    .map(|(trait_name, var_id, _)| (trait_name.clone(), format!("v{}", var_id)))
                    .collect();
                if !dict_params.is_empty() {
                    inferred_dict_params.insert(name.to_string(), dict_params);
                }
            }
        }
        // Register dict params under all user-facing name forms that resolve
        // to a canonical name with dict params (so "List.sort" finds the params
        // registered under "Std.List.sort").
        for (user_name, canonical) in &result.scope_map.values {
            if user_name != canonical
                && let Some(params) = inferred_dict_params.get(canonical).cloned()
            {
                inferred_dict_params
                    .entry(user_name.clone())
                    .or_insert(params);
            }
        }

        // Merge let-binding dict params (from local let bindings with trait constraints).
        // Keyed by (name, pat_id) to avoid collisions between same-named bindings
        // in different scopes. We store the pat_id set so the elaborator can check
        // whether a specific binding needs dict wrapping.
        let mut let_binding_arities: HashMap<String, usize> = HashMap::new();
        let mut let_dict_pat_ids: HashMap<String, HashSet<crate::ast::NodeId>> = HashMap::new();
        for ((name, pat_id), info) in &result.let_dict_params {
            inferred_dict_params
                .entry(name.clone())
                .or_insert_with(|| info.params.clone());
            let_binding_arities.insert(name.clone(), info.value_arity);
            let_dict_pat_ids
                .entry(name.clone())
                .or_default()
                .insert(*pat_id);
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
        let mut impl_dict_params_from_imports: HashMap<ImplKey, Vec<(String, usize)>> =
            HashMap::new();
        for info in result.codegen_info().values() {
            for d in &info.trait_impl_dicts {
                dict_names.insert(
                    (
                        d.trait_name.clone(),
                        d.trait_type_args.clone(),
                        d.target_type.clone(),
                    ),
                    d.dict_name.clone(),
                );
                if !d.param_constraints.is_empty() {
                    impl_dict_params_from_imports.insert(
                        (
                            d.trait_name.clone(),
                            d.trait_type_args.clone(),
                            d.target_type.clone(),
                        ),
                        d.param_constraints.clone(),
                    );
                }
            }
        }

        Elaborator {
            trait_methods: HashMap::new(),
            fun_dict_params: inferred_dict_params,
            handler_dict_params: HashMap::new(),
            dict_names,
            impl_dict_params: impl_dict_params_from_imports,
            traits: result.traits.clone(),
            evidence_by_node,
            current_fun: None,
            current_dict_params: HashMap::new(),
            current_dict_params_by_var: HashMap::new(),
            erlang_module,
            let_binding_arities,
            let_dict_pat_ids,
            scope_map_values: result.scope_map.values.clone(),
            scope_map_traits: result.scope_map.traits.clone(),
        }
    }

    /// Extract dict param info from a where clause: [(trait_name, type_var_name)]
    /// for traits that use dictionary dispatch (excludes Eq which uses BIFs).
    ///
    /// Note: trait type args (the `_` in the destructure) are intentionally not used here.
    /// Dict params are keyed by (trait_name, self_type_var) - one dict per constraint.
    /// The extra type args (e.g. `b` in `a: ConvertTo b`) are resolved separately
    /// through TraitEvidence when looking up which concrete dict to pass at call sites.
    fn dict_params_from_where(&self, where_clause: &[TraitBound]) -> Vec<(String, String)> {
        let mut dict_params = Vec::new();
        for bound in where_clause {
            for (trait_name, _, _) in &bound.traits {
                if trait_name != "Num" && trait_name != "Semigroup" && trait_name != "Eq" {
                    let resolved = self
                        .scope_map_traits
                        .get(trait_name)
                        .cloned()
                        .unwrap_or_else(|| trait_name.clone());
                    dict_params.push((resolved, bound.type_var.clone()));
                }
            }
        }
        dict_params
    }

    /// Set up `current_dict_params` from a where clause, saving the previous state.
    /// Returns the saved state to be restored later via `restore_dict_params`.
    fn setup_dict_params(
        &mut self,
        where_clause: &[TraitBound],
    ) -> (HashMap<String, String>, HashMap<(String, String), String>) {
        let saved = (
            std::mem::take(&mut self.current_dict_params),
            std::mem::take(&mut self.current_dict_params_by_var),
        );
        for bound in where_clause {
            for (req_trait, _, _) in &bound.traits {
                let resolved = self
                    .scope_map_traits
                    .get(req_trait)
                    .cloned()
                    .unwrap_or_else(|| req_trait.clone());
                // Use bare trait name in param name to avoid dots in Erlang identifiers
                let bare = req_trait.rsplit('.').next().unwrap_or(req_trait);
                let param_name = format!("__dict_{}_{}", bare, bound.type_var);
                self.current_dict_params
                    .insert(resolved.clone(), param_name.clone());
                self.current_dict_params_by_var
                    .insert((resolved, bound.type_var.clone()), param_name);
            }
        }
        saved
    }

    /// Restore `current_dict_params` from a previous `setup_dict_params` call.
    fn restore_dict_params(
        &mut self,
        saved: (HashMap<String, String>, HashMap<(String, String), String>),
    ) {
        self.current_dict_params = saved.0;
        self.current_dict_params_by_var = saved.1;
    }

    fn elaborate_program(&mut self, program: &Program) -> Program {
        // Pass 1: Collect trait method info and function where clauses
        for decl in program {
            match decl {
                Decl::TraitDef { name, methods, .. } => {
                    for (idx, ann) in methods.iter().enumerate() {
                        let method = &ann.node;
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
                Decl::FunSignature {
                    name, where_clause, ..
                } => {
                    let dict_params = self.dict_params_from_where(where_clause);
                    if !dict_params.is_empty() {
                        self.fun_dict_params.insert(name.clone(), dict_params);
                    }
                }
                Decl::ImplDef {
                    trait_name,
                    trait_type_args,
                    target_type,
                    type_params,
                    where_clause,
                    ..
                } => {
                    // Resolve trait name to canonical form
                    let canonical_trait = self
                        .scope_map_traits
                        .get(trait_name)
                        .cloned()
                        .unwrap_or_else(|| trait_name.clone());
                    // Include trait type args in dict name for uniqueness
                    let type_args_suffix = if trait_type_args.is_empty() {
                        String::new()
                    } else {
                        format!("_{}", trait_type_args.join("_"))
                    };
                    let dict_name = if self.erlang_module.is_empty() {
                        format!("__dict_{}{}_{}", trait_name, type_args_suffix, target_type)
                    } else {
                        format!(
                            "__dict_{}{}_{}_{}",
                            trait_name, type_args_suffix, self.erlang_module, target_type
                        )
                    };
                    self.dict_names.insert(
                        (
                            canonical_trait.clone(),
                            trait_type_args.clone(),
                            target_type.clone(),
                        ),
                        dict_name,
                    );
                    // Capture where-clause constraints as (trait, param_index) pairs.
                    // This tells dict_for_type which sub-dicts to pass for parameterized impls.
                    // Always insert (even empty) so dict_for_type doesn't fall back to
                    // guessing one sub-dict per type arg (which breaks phantom type params).
                    let var_to_idx: HashMap<&str, usize> = type_params
                        .iter()
                        .enumerate()
                        .map(|(i, name)| (name.as_str(), i))
                        .collect();
                    let scope_traits = &self.scope_map_traits;
                    let params: Vec<(String, usize)> = where_clause
                        .iter()
                        .flat_map(|bound| {
                            let idx = var_to_idx
                                .get(bound.type_var.as_str())
                                .copied()
                                .unwrap_or(0);
                            bound.traits.iter().map(move |(t, _, _)| {
                                let resolved =
                                    scope_traits.get(t).cloned().unwrap_or_else(|| t.clone());
                                (resolved, idx)
                            })
                        })
                        .collect();
                    self.impl_dict_params.insert(
                        (
                            canonical_trait,
                            trait_type_args.clone(),
                            target_type.clone(),
                        ),
                        params,
                    );
                }
                Decl::HandlerDef { name, body, .. } => {
                    let dict_params = self.dict_params_from_where(&body.where_clause);
                    if !dict_params.is_empty() {
                        self.handler_dict_params.insert(name.clone(), dict_params);
                    }
                }
                _ => {}
            }
        }

        // Register trait methods from checker's trait info (for traits not
        // defined in the current program, e.g. Show in Std modules).
        // Register under both bare name and canonical name so lookups work
        // before and after the resolve pass rewrites Var nodes.
        for (trait_name, info) in &self.traits {
            for (idx, (method_name, _, _, _)) in info.methods.iter().enumerate() {
                self.trait_methods
                    .entry(method_name.clone())
                    .or_insert_with(|| (trait_name.clone(), idx));
            }
        }
        // Add canonical-name entries from scope_map: if "show" -> "Std.Base.Show.show",
        // register "Std.Base.Show.show" -> ("Show", idx) too.
        for (bare_name, canonical) in &self.scope_map_values {
            if bare_name != canonical
                && let Some(entry) = self.trait_methods.get(bare_name).cloned()
            {
                self.trait_methods.entry(canonical.clone()).or_insert(entry);
            }
        }

        // Pass 2: Emit new program with dict constructors and elaborated functions
        let mut output = Vec::new();

        for decl in program {
            match decl {
                // Emit DictConstructor for each impl
                Decl::ImplDef {
                    trait_name,
                    trait_type_args,
                    target_type,
                    type_params,
                    where_clause,
                    methods,
                    span,
                    ..
                } => {
                    let canonical_trait = self
                        .scope_map_traits
                        .get(trait_name)
                        .cloned()
                        .unwrap_or_else(|| trait_name.clone());
                    let dict_name = self
                        .dict_names
                        .get(&(
                            canonical_trait.clone(),
                            trait_type_args.clone(),
                            target_type.clone(),
                        ))
                        .cloned()
                        .unwrap();

                    let trait_info = self.traits.get(&canonical_trait).cloned();

                    // Build dict_params for conditional impls
                    let mut dict_params = Vec::new();
                    for bound in where_clause {
                        for (req_trait, _, _) in &bound.traits {
                            dict_params.push(format!("__dict_{}_{}", req_trait, bound.type_var));
                        }
                    }

                    // Set up current dict params for elaborating method bodies
                    let saved = self.setup_dict_params(where_clause);

                    // Order methods by trait declaration order
                    let mut ordered_methods = Vec::new();
                    if let Some(ref info) = trait_info {
                        for (trait_method_name, _, _, _) in &info.methods {
                            if let Some(ann) = methods
                                .iter()
                                .find(|ann| ann.node.name == *trait_method_name)
                            {
                                let ImplMethod { params, body, .. } = &ann.node;
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

                    self.restore_dict_params(saved);

                    // For parameterized types, if there are type_params but no where_clause,
                    // no dict params are needed. The dict is still nullary.
                    let _ = type_params; // acknowledge but don't use for now

                    output.push(Decl::DictConstructor {
                        id: NodeId::fresh(),
                        name: dict_name,
                        dict_params,
                        methods: ordered_methods,
                        span: *span,
                    });
                }

                // TraitDef and FunAnnotation are consumed (not emitted)
                Decl::TraitDef { .. } => {}
                Decl::FunSignature { .. } => {
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
                    ..
                } => {
                    self.current_fun = Some(name.clone());

                    // Set up dict params for this function
                    let saved = (
                        std::mem::take(&mut self.current_dict_params),
                        std::mem::take(&mut self.current_dict_params_by_var),
                    );
                    let mut extra_params = Vec::new();

                    if let Some(dict_param_info) = self.fun_dict_params.get(name) {
                        for (trait_name, type_var) in dict_param_info {
                            // Use bare trait name in param name to avoid dots in Erlang identifiers
                            let bare = trait_name.rsplit('.').next().unwrap_or(trait_name);
                            let param_name = format!("__dict_{}_{}", bare, type_var);
                            self.current_dict_params
                                .insert(trait_name.clone(), param_name.clone());
                            self.current_dict_params_by_var
                                .insert((trait_name.clone(), type_var.clone()), param_name.clone());
                            extra_params.push(Pat::Var {
                                id: NodeId::fresh(),
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

                    self.restore_dict_params(saved);
                    self.current_fun = None;

                    output.push(Decl::FunBinding {
                        id: NodeId::fresh(),
                        name: name.clone(),
                        name_span: *span, // elaborated binding, reuse span
                        params: full_params,
                        guard: elab_guard,
                        body: elab_body,
                        span: *span,
                    });
                }

                // Elaborate handler arm bodies (so print/show get dicts inserted)
                Decl::HandlerDef {
                    doc,
                    public,
                    name,
                    name_span,
                    body,
                    span,
                    ..
                } => {
                    // Set up dict params from where clause so arm bodies can
                    // reference trait dicts (e.g. `show entity` -> `__dict_Show_a`)
                    let saved = self.setup_dict_params(&body.where_clause);

                    let elab_arms: Vec<Annotated<HandlerArm>> = body
                        .arms
                        .iter()
                        .map(|ann| {
                            let arm = &ann.node;
                            Annotated::bare(HandlerArm {
                                op_name: arm.op_name.clone(),
                                qualifier: arm.qualifier.clone(),
                                params: arm.params.clone(),
                                body: Box::new(self.elaborate_expr(&arm.body)),
                                finally_block: arm
                                    .finally_block
                                    .as_ref()
                                    .map(|fb| Box::new(self.elaborate_expr(fb))),
                                span: arm.span,
                            })
                        })
                        .collect();
                    let elab_return = body.return_clause.as_ref().map(|rc| {
                        Box::new(HandlerArm {
                            op_name: rc.op_name.clone(),
                            qualifier: rc.qualifier.clone(),
                            params: rc.params.clone(),
                            body: Box::new(self.elaborate_expr(&rc.body)),
                            finally_block: None,
                            span: rc.span,
                        })
                    });

                    self.restore_dict_params(saved);

                    output.push(Decl::HandlerDef {
                        id: NodeId::fresh(),
                        doc: doc.clone(),
                        public: *public,
                        name: name.clone(),
                        name_span: *name_span,
                        body: HandlerBody {
                            effects: body.effects.clone(),
                            needs: body.needs.clone(),
                            where_clause: body.where_clause.clone(),
                            arms: elab_arms,
                            return_clause: elab_return,
                        },
                        recovered_arms: vec![],
                        span: *span,
                        dangling_trivia: vec![],
                    });
                }

                Decl::Val {
                    doc,
                    public,
                    name,
                    name_span,
                    annotations,
                    value,
                    span,
                    ..
                } => {
                    let elab_value = self.elaborate_expr(value);
                    output.push(Decl::Val {
                        id: NodeId::fresh(),
                        doc: doc.clone(),
                        public: *public,
                        name: name.clone(),
                        name_span: *name_span,
                        annotations: annotations.clone(),
                        value: elab_value,
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
                        let mut trait_occurrences: HashMap<&str, usize> = HashMap::new();
                        for (trait_name, _type_var) in &dict_param_info {
                            let occ = trait_occurrences.entry(trait_name).or_insert(0);
                            if let Some(dict_expr) =
                                self.resolve_dict_nth(trait_name, func.id, func.span, *occ)
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
                        let mut trait_occurrences: HashMap<&str, usize> = HashMap::new();
                        for (trait_name, _type_var) in &dict_param_info {
                            let occ = trait_occurrences.entry(trait_name).or_insert(0);
                            if let Some(dict_expr) =
                                self.resolve_dict_nth(trait_name, func.id, func.span, *occ)
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
                        .and_then(|evs| evs.iter().find(|ev| ev.trait_name == ORD))
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

                // Rewrite Div to IntDiv when the Num constraint resolved to Int,
                // and Mod to FloatMod when resolved to Float.
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
                } else if *op == BinOp::Mod {
                    let is_float = self
                        .evidence_by_node
                        .get(&node_id)
                        .and_then(|evs| evs.iter().find(|ev| ev.trait_name == "Num"))
                        .and_then(|ev| ev.resolved_type.as_ref())
                        .is_some_and(|(name, _)| name == "Float");
                    if is_float {
                        BinOp::FloatMod
                    } else {
                        BinOp::Mod
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
                ..
            } => Expr::synth(
                span,
                ExprKind::If {
                    cond: Box::new(self.elaborate_expr(cond)),
                    then_branch: Box::new(self.elaborate_expr(then_branch)),
                    else_branch: Box::new(self.elaborate_expr(else_branch)),
                    multiline: false,
                },
            ),

            ExprKind::Case {
                scrutinee, arms, ..
            } => Expr::synth(
                span,
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

            ExprKind::Block { stmts, .. } => Expr::synth(
                span,
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
                                            self.fun_dict_params.get(name).cloned()
                                        } else {
                                            None
                                        }
                                    } else {
                                        None
                                    };

                                    if let Some(dict_param_info) = dict_info {
                                        // Set up dict params for elaborating the value.
                                        // Eta-expand: `let f = val` becomes
                                        // `let f = fun (dict, __arg) -> (elaborated_val)(__arg)`
                                        // so the lowerer sees a single function of arity N+1.
                                        let saved = (
                                            std::mem::take(&mut self.current_dict_params),
                                            std::mem::take(&mut self.current_dict_params_by_var),
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
                        .map(|(n, s, e)| (n.clone(), *s, self.elaborate_expr(e)))
                        .collect(),
                },
            ),

            ExprKind::AnonRecordCreate { fields } => Expr::synth(
                span,
                ExprKind::AnonRecordCreate {
                    fields: fields
                        .iter()
                        .map(|(n, s, e)| (n.clone(), *s, self.elaborate_expr(e)))
                        .collect(),
                },
            ),

            ExprKind::RecordUpdate { record, fields } => Expr::synth(
                span,
                ExprKind::RecordUpdate {
                    record: Box::new(self.elaborate_expr(record)),
                    fields: fields
                        .iter()
                        .map(|(n, s, e)| (n.clone(), *s, self.elaborate_expr(e)))
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
                ..
            } => Expr::synth(
                span,
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
                if let Some(dict_param_info) = self.fun_dict_params.get(&qualified).cloned() {
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
            } => Expr::synth(
                span,
                ExprKind::EffectCall {
                    name: name.clone(),
                    qualifier: qualifier.clone(),
                    args: args.iter().map(|a| self.elaborate_expr(a)).collect(),
                },
            ),

            ExprKind::With { expr: e, handler } => {
                let with_expr = Expr::synth(
                    span,
                    ExprKind::With {
                        expr: Box::new(self.elaborate_expr(e)),
                        handler: Box::new(self.elaborate_handler(handler)),
                    },
                );

                // For named handlers with where clauses, bind the dict variables
                // so handler arm bodies (which reference e.g. `__dict_Show_a`) can
                // capture them from the enclosing scope.
                if let Handler::Named(handler_name, _) = handler.as_ref() {
                    if let Some(dict_param_info) =
                        self.handler_dict_params.get(handler_name).cloned()
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

            ExprKind::HandlerExpr { body } => Expr::synth(
                span,
                ExprKind::HandlerExpr {
                    body: HandlerBody {
                        effects: body.effects.clone(),
                        needs: body.needs.clone(),
                        where_clause: body.where_clause.clone(),
                        arms: body
                            .arms
                            .iter()
                            .map(|ann| {
                                Annotated::bare(HandlerArm {
                                    op_name: ann.node.op_name.clone(),
                                    qualifier: ann.node.qualifier.clone(),
                                    params: ann.node.params.clone(),
                                    body: Box::new(self.elaborate_expr(&ann.node.body)),
                                    finally_block: ann
                                        .node
                                        .finally_block
                                        .as_ref()
                                        .map(|fb| Box::new(self.elaborate_expr(fb))),
                                    span: ann.node.span,
                                })
                            })
                            .collect(),
                        return_clause: body.return_clause.as_ref().map(|rc| {
                            Box::new(HandlerArm {
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

            ExprKind::Receive {
                arms, after_clause, ..
            } => Expr::synth(
                span,
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

            ExprKind::BitString { segments } => Expr::synth(
                span,
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
            ExprKind::DictMethodAccess { .. } | ExprKind::DictRef { .. } => expr.clone(),

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

    fn elaborate_handler(&mut self, handler: &Handler) -> Handler {
        match handler {
            Handler::Named(_, _) => handler.clone(),
            Handler::Inline {
                named,
                arms,
                return_clause,
                ..
            } => Handler::Inline {
                dangling_trivia: vec![],
                named: named.clone(),
                arms: arms
                    .iter()
                    .map(|ann| {
                        let arm = &ann.node;
                        Annotated::bare(HandlerArm {
                            op_name: arm.op_name.clone(),
                            qualifier: arm.qualifier.clone(),
                            params: arm.params.clone(),
                            body: Box::new(self.elaborate_expr(&arm.body)),
                            finally_block: arm
                                .finally_block
                                .as_ref()
                                .map(|fb| Box::new(self.elaborate_expr(fb))),
                            span: arm.span,
                        })
                    })
                    .collect(),
                return_clause: return_clause.as_ref().map(|arm| {
                    Box::new(HandlerArm {
                        op_name: arm.op_name.clone(),
                        qualifier: arm.qualifier.clone(),
                        params: arm.params.clone(),
                        body: Box::new(self.elaborate_expr(&arm.body)),
                        finally_block: None,
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
        let dict_expr = self.resolve_dict(ORD, node_id, span)?;

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
        self.resolve_dict_nth(trait_name, node_id, span, 0)
    }

    /// Resolve the `occurrence`-th evidence entry for `trait_name` at `node_id`.
    /// When a function has multiple where-clause bounds for the same trait
    /// (e.g. `where {a: Debug, b: Debug}`), each dict param needs a different
    /// evidence entry. The occurrence index selects which one.
    fn resolve_dict_nth(
        &self,
        trait_name: &str,
        node_id: crate::ast::NodeId,
        span: Span,
        occurrence: usize,
    ) -> Option<Expr> {
        // Check if we have evidence for this node
        if let Some(evidence_list) = self.evidence_by_node.get(&node_id) {
            let mut count = 0;
            for ev in evidence_list {
                if ev.trait_name == trait_name {
                    if count < occurrence {
                        count += 1;
                        continue;
                    }
                    return match &ev.resolved_type {
                        Some((type_name, args)) => {
                            // Concrete type: build the dict via dict_for_type,
                            // which handles where-clause constraints correctly.
                            // Resolve extra type args to concrete type names for dict key.
                            let resolved_type_args: Vec<String> = ev
                                .trait_type_args
                                .iter()
                                .filter_map(|t| match t {
                                    Type::Con(name, _) => Some(name.clone()),
                                    _ => None,
                                })
                                .collect();
                            let ty = Type::Con(type_name.clone(), args.clone());
                            self.dict_for_type(trait_name, &resolved_type_args, &ty, span)
                        }
                        None => {
                            // Polymorphic: use the dict param from current function.
                            // If evidence has a type_var_name, use it to build the
                            // specific dict param name (handles multiple where-clause
                            // bounds for the same trait, e.g. `where {e: Show, a: Show}`).
                            if let Some(ref var_name) = ev.type_var_name {
                                let bare = trait_name.rsplit('.').next().unwrap_or(trait_name);
                                let param_name = format!("__dict_{}_{}", bare, var_name);
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
        // (Num, Semigroup, Eq) that uses direct BEAM BIF dispatch rather than dictionary dispatch.
        None
    }

    /// Build the show function expression for a concrete type.
    /// Returns an expression that, when applied to a value of that type, produces a string.
    fn show_fn_for_type(&self, trait_name: &str, ty: &Type, span: Span) -> Option<Expr> {
        let dict = self.dict_for_type(trait_name, &[], ty, span)?;
        Some(Expr::synth(
            span,
            ExprKind::DictMethodAccess {
                dict: Box::new(dict),
                method_index: 0,
            },
        ))
    }

    /// Build the dict expression for a concrete type (the dict itself, not the method).
    /// `trait_type_args` are the resolved extra type arguments for multi-param traits.
    fn dict_for_type(
        &self,
        trait_name: &str,
        trait_type_args: &[String],
        ty: &Type,
        span: Span,
    ) -> Option<Expr> {
        match ty {
            Type::Con(name, args)
                if name == "Tuple" && (trait_name == SHOW || trait_name == DEBUG) =>
            {
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
                let key = (
                    trait_name.to_string(),
                    trait_type_args.to_vec(),
                    name.clone(),
                );
                let dict_name = self.dict_names.get(&key)?;
                let mut dict_expr: Expr = Expr::synth(
                    span,
                    ExprKind::DictRef {
                        name: dict_name.clone(),
                    },
                );
                if let Some(constraints) = self.impl_dict_params.get(&key) {
                    // Use explicit where-clause constraints (handles cases like
                    // Ord where the impl needs both Ord and Eq dicts per type param).
                    for (constraint_trait, param_idx) in constraints {
                        if let Some(arg_ty) = args.get(*param_idx) {
                            let sub_dict =
                                self.dict_for_type(constraint_trait, &[], arg_ty, span)?;
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
                        let sub_dict =
                            self.dict_for_type(trait_name, trait_type_args, arg_ty, span)?;
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
        if trait_name != SHOW && trait_name != DEBUG {
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
    fn build_tuple_show_lambda(
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
