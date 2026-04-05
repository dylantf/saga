mod builtins;
mod effects;
pub mod errors;
mod exprs;
pub(crate) mod init;
mod pats;
pub mod util;

use crate::ast::{self, Decl, Expr, ExprKind, HandlerArm, Lit, Pat};
use crate::codegen::cerl::{CArm, CExpr, CFunDef, CLit, CModule, CPat};
use std::collections::HashMap;

use errors::{ErrorInfo, ErrorKind, SourceInfo};
use init::{PendingAnnotation, extract_external};
use pats::{lower_params, lower_pat};
use util::{
    cerl_call, collect_ctor_call, collect_effect_call, collect_fun_call, collect_qualified_call,
    core_var, field_access_record_name, has_nested_effect_call, lower_lit, lower_string_to_binary,
    process_string_escapes,
};

type Clause<'a> = (&'a [Pat], &'a Option<Box<Expr>>, &'a Expr);

/// Lower a simple expression used as a bitstring segment size.
/// Handles integer literals and variable references — the common cases
/// for pattern-position sizes like `<<len:8, data:len/binary>>`.
pub(crate) fn lower_size_expr(expr: &Expr) -> CExpr {
    match &expr.kind {
        ExprKind::Lit {
            value: Lit::Int(_, n),
            ..
        } => CExpr::Lit(CLit::Int(*n)),
        ExprKind::Var { name, .. } => CExpr::Var(core_var(name)),
        _ => unreachable!("bitstring segment size must be an integer literal or variable"),
    }
}

/// Count how many lambda params can be absorbed from the body of a top-level
/// function definition. Peels nested lambdas so `fun x -> fun y -> body` counts 2.
fn count_lambda_params(body: &Expr) -> usize {
    match &body.kind {
        ExprKind::Lambda { params, body, .. } => params.len() + count_lambda_params(body),
        _ => 0,
    }
}

/// Stored handler definition for CPS inlining at `with` sites.
#[derive(Clone)]
struct HandlerInfo {
    effects: Vec<String>,
    arms: Vec<HandlerArm>,
    return_clause: Option<Box<HandlerArm>>,
    /// The module this handler was defined in (e.g. "Std.Actor").
    /// Used to identify BEAM-native handlers that need special lowering.
    source_module: Option<String>,
}

/// Stored effect definition: maps op_name -> number of parameters.
#[allow(dead_code)]
struct EffectInfo {
    /// op_name -> param count
    ops: HashMap<String, usize>,
}

/// All information about a top-level function needed by the lowerer.
/// CPS metadata for a function. Used by the lowerer to determine how to
/// thread handler parameters and return continuations through effectful calls.
/// This is NOT name resolution -- name resolution is handled by the ResolutionMap.
/// FunInfo only tracks arity/effects needed for CPS transformation.
#[derive(Debug, Clone, Default)]
struct FunInfo {
    /// Exported arity (including handler params). 0 if not yet known (set by FunBinding).
    arity: usize,
    /// Effect names from `needs` clause (sorted). Used to determine which
    /// handler params to thread through at call sites.
    effects: Vec<String>,
    /// For EffArrow params: param_index -> absorbed effects. Used to inject
    /// handler params into lambdas passed to effectful higher-order functions.
    param_absorbed_effects: HashMap<usize, Vec<String>>,
}

pub struct Lowerer<'a> {
    counter: usize,
    /// Cross-module codegen context (compiled modules, effect bindings, prelude imports).
    ctx: &'a super::CodegenContext,
    /// Source location info for error terms. None for stdlib modules (no user source).
    source_info: Option<SourceInfo>,
    /// Current dylang module name (e.g. "MyApp.Server"). Set in lower_module.
    current_module: String,
    /// Current function being lowered (e.g. "handle_request"). Set per function.
    current_function: String,
    /// Maps module alias -> Erlang module atom (e.g. "List" -> "std_list").
    /// Used by lower_qualified_call as a fallback for unresolved qualified names.
    module_aliases: HashMap<String, String>,
    /// Names declared as `pub` in the current module (for export filtering).
    pub_names: std::collections::HashSet<String>,
    /// Maps record name -> ordered field names (from RecordDef declarations).
    record_fields: HashMap<String, Vec<String>>,
    /// CPS metadata for top-level functions. Populated from FunBinding/FunSignature
    /// during init_module. NOT used for name resolution (that's the ResolutionMap).
    fun_info: HashMap<String, FunInfo>,
    /// Maps effect name -> EffectInfo (op names and param counts).
    effect_defs: HashMap<String, EffectInfo>,
    /// Maps handler name -> handler arms + return clause.
    handler_defs: HashMap<String, HandlerInfo>,
    /// Maps op_name -> effect name (reverse lookup).
    op_to_effect: HashMap<String, String>,
    /// When lowering inside an effectful function, maps effect name -> handler param var name.
    current_handler_params: HashMap<String, String>,
    /// Set of "effect.op" keys whose current handler arm never calls resume.
    /// Used to pass a cheap atom instead of a real continuation closure at the call site,
    /// avoiding the Erlang "a term is constructed but never used" warning.
    no_resume_ops: std::collections::HashSet<String>,
    /// When lowering inside a function, maps local variable name -> effects it absorbs.
    /// Set from FunInfo.param_absorbed_effects for the current function.
    current_effectful_vars: HashMap<String, Vec<String>>,
    /// Effects that the next lambda being lowered should accept as extra params.
    /// Set by the call site that passes the lambda to an effectful parameter.
    lambda_effect_context: Option<Vec<String>>,
    /// Return continuation for the current `with` expression's return clause.
    /// Set by `lower_with`, consumed by `lower_block` at its terminal cases.
    /// This places the return clause inside the CPS chain so handler aborts
    /// (which don't call K) naturally bypass the return clause.
    current_return_k: Option<CExpr>,
    /// Return continuation to pass as `_ReturnK` to the next effectful call.
    /// Set by `lower_with` when the inner expression is a direct function call,
    /// consumed by the saturated call path.
    pending_callee_return_k: Option<CExpr>,
    /// Variable name for the continuation parameter in the current handler function.
    /// Set by `build_handler_fun`, read by `Expr::Resume`.
    current_handler_k: Option<String>,
    /// When lowering a handler arm with `finally`, this holds the finally block AST.
    /// At each `resume` site, the cleanup code is lowered inline (wrapped in try/catch
    /// around the K call) so it can capture variables from the arm body's lexical scope.
    current_handler_finally: Option<crate::ast::Expr>,
    /// Pre-resolved constructor name -> mangled Erlang atom.
    /// e.g. "NotFound" -> "std_file_NotFound", "Ok" -> "ok".
    /// Built by resolve::build_constructor_atoms before lowering.
    constructor_atoms: super::resolve::ConstructorAtoms,
    /// Pre-resolved name resolution map: NodeId -> ResolvedName.
    /// Built by resolve::resolve_names before lowering.
    resolved: super::resolve::ResolutionMap,
    /// @inline val name -> lowered expression. Substituted at reference sites.
    inline_vals: HashMap<String, CExpr>,
    /// Bare handler name -> canonical handler name (e.g. "collect_handler" -> "Std.Test.collect_handler").
    /// Built during init_module for resolving handler references in `with` expressions.
    handler_canonical: HashMap<String, String>,
    /// Bare effect name -> canonical effect name (e.g. "Assert" -> "Std.Test.Assert").
    /// Built during init_module for canonicalizing effect names from the type system.
    effect_canonical: HashMap<String, String>,
    /// Typechecker result for the module currently being lowered.
    /// Provides resolved types, handler info, effect info, etc.
    /// None for modules compiled without full typechecking (e.g. codegen tests).
    check_result: Option<crate::typechecker::CheckResult>,
    /// Conditional handle bindings: name -> (cond_var, cond_expr, then_canonical, else_canonical).
    /// Used during lower_with to generate conditional handler dispatch.
    handle_cond_vars: HashMap<String, (String, CExpr, String, String)>,
    /// Dynamic handle bindings: name -> (lowered_var, canonical_effect_names, has_return_clause).
    /// For `handle name = some_function_call()` where the handler isn't statically
    /// resolvable, the RHS is lowered to a tuple-of-lambdas and bound to a variable.
    /// At `with` sites, the tuple is destructured to extract per-op handler functions.
    handle_dynamic_vars: HashMap<String, (String, Vec<String>, bool)>,
}

impl<'a> Lowerer<'a> {
    pub fn new(
        ctx: &'a super::CodegenContext,
        constructor_atoms: super::resolve::ConstructorAtoms,
        resolved: super::resolve::ResolutionMap,
        check_result: Option<&crate::typechecker::CheckResult>,
        source_info: Option<SourceInfo>,
    ) -> Self {
        Lowerer {
            counter: 0,
            ctx,
            source_info,
            current_module: String::new(),
            current_function: String::new(),
            module_aliases: HashMap::new(),
            pub_names: std::collections::HashSet::new(),
            record_fields: HashMap::new(),
            fun_info: HashMap::new(),
            effect_defs: HashMap::new(),
            handler_defs: HashMap::new(),
            op_to_effect: HashMap::new(),
            current_handler_params: HashMap::new(),
            no_resume_ops: std::collections::HashSet::new(),
            current_effectful_vars: HashMap::new(),
            lambda_effect_context: None,
            current_return_k: None,
            pending_callee_return_k: None,
            constructor_atoms,
            resolved,
            current_handler_k: None,
            current_handler_finally: None,
            inline_vals: HashMap::new(),
            handler_canonical: HashMap::new(),
            effect_canonical: HashMap::new(),
            check_result: check_result.cloned(),
            handle_cond_vars: HashMap::new(),
            handle_dynamic_vars: HashMap::new(),
        }
    }

    pub(super) fn fresh(&mut self) -> String {
        let n = self.counter;
        self.counter += 1;
        format!("_Cor{}", n)
    }

    /// Build a structured error term and wrap it in `erlang:error(Term)`.
    /// Falls back to the old `{dylang_panic, Msg}` tuple when no source info is available.
    pub(super) fn make_error(
        &self,
        kind: ErrorKind,
        message: CExpr,
        span: Option<&crate::token::Span>,
    ) -> CExpr {
        let error_term = if let Some(si) = &self.source_info {
            let line = span.map_or(0, |s| si.line_number(s));
            ErrorInfo {
                kind,
                message,
                module: self.current_module.clone(),
                function: self.current_function.clone(),
                file: si.file.clone(),
                line,
            }
            .to_cexpr()
        } else {
            // Stdlib modules don't have source info — use the old format
            CExpr::Tuple(vec![
                CExpr::Lit(CLit::Atom("dylang_error".into())),
                CExpr::Lit(CLit::Atom(kind.as_atom().into())),
                message,
                lower_string_to_binary(&self.current_module),
                lower_string_to_binary(&self.current_function),
                lower_string_to_binary(""),
                CExpr::Lit(CLit::Int(0)),
            ])
        };
        cerl_call("erlang", "error", vec![error_term])
    }

    /// Wrap a CExpr with a source location annotation for BEAM stack traces.
    /// No-op if source info is unavailable or span is missing.
    pub(super) fn annotate(&self, expr: CExpr, span: Option<&crate::token::Span>) -> CExpr {
        if let Some(si) = &self.source_info
            && let Some(span) = span
        {
            let line = si.line_number(span);
            if line > 0 {
                return CExpr::Annotated {
                    expr: Box::new(expr),
                    line,
                    file: si.file.clone(),
                };
            }
        }
        expr
    }

    /// Known BEAM-native handlers: (module, handler_name) pairs.
    /// These handlers' effects are lowered to direct BEAM calls instead of CPS.
    const BEAM_NATIVE_HANDLERS: &'static [(&'static str, &'static str)] =
        &[("Std.Actor", "Std.Actor.beam_actor")];

    /// Resolve a bare effect name to its canonical form.
    fn canonicalize_effect(&self, bare: &str) -> String {
        self.effect_canonical
            .get(bare)
            .cloned()
            .unwrap_or_else(|| bare.to_string())
    }

    /// Canonicalize a list of effect names from the type system (which uses bare names).
    fn canonicalize_effects(&self, effects: Vec<String>) -> Vec<String> {
        effects
            .into_iter()
            .map(|e| self.canonicalize_effect(&e))
            .collect()
    }

    /// Resolve a bare handler name to its canonical form.
    fn resolve_handler_name(&self, name: &str) -> String {
        self.handler_canonical
            .get(name)
            .cloned()
            .unwrap_or_else(|| name.to_string())
    }

    /// Try to resolve a handler name to a known handler definition.
    /// Returns Some(canonical) if the handler exists in handler_defs, None otherwise.
    fn resolve_handler_name_opt(&self, name: &str) -> Option<String> {
        let canonical = self.resolve_handler_name(name);
        if self.handler_defs.contains_key(&canonical) {
            Some(canonical)
        } else {
            None
        }
    }

    /// Check if a handler is BEAM-native (should be lowered to direct BEAM calls).
    pub(super) fn is_beam_native_handler(&self, name: &str) -> bool {
        let canonical = self.resolve_handler_name(name);
        self.handler_defs
            .get(&canonical)
            .and_then(|info| info.source_module.as_deref())
            .is_some_and(|module| {
                Self::BEAM_NATIVE_HANDLERS
                    .iter()
                    .any(|(m, h)| *m == module && *h == canonical.as_str())
            })
    }

    /// Given a list of effect names (from a `needs` clause), return all
    /// (effect_name, op_name) pairs. This is the single source of truth for
    /// what handler params a function needs.
    pub(super) fn effect_handler_ops(&self, effects: &[String]) -> Vec<(String, String)> {
        let mut ops = Vec::new();
        for eff_name in effects {
            if let Some(info) = self.effect_defs.get(eff_name) {
                // Sort op names for deterministic ordering
                let mut op_names: Vec<&String> = info.ops.keys().collect();
                op_names.sort();
                for op_name in op_names {
                    ops.push((eff_name.clone(), op_name.clone()));
                }
            }
        }
        ops
    }

    /// Generate the handler param variable name for a specific effect op.
    /// e.g. ("Std.Process.Process", "spawn") -> "_Handle_Std_Process_Process_spawn"
    /// Dots are replaced with underscores for valid Core Erlang variable names.
    pub(super) fn handler_param_name(effect: &str, op: &str) -> String {
        format!("_Handle_{}_{}", effect.replace('.', "_"), op)
    }

    /// Compute the expanded arity for a function with the given base arity
    /// and effect requirements. Accounts for one handler param per op plus
    /// a _ReturnK param if there are any effects.
    pub(super) fn expanded_arity(&self, base_arity: usize, effects: &[String]) -> usize {
        let ops = self.effect_handler_ops(effects);
        let op_count = ops.len();
        base_arity + op_count + if op_count > 0 { 1 } else { 0 }
    }

    /// Try to generate a wrapper lambda for an effectful function used as a
    /// value (eta reduction). The wrapper takes only user-visible args and
    /// captures handler params from scope, threading them + a return
    /// continuation to the CPS-expanded callee.
    ///
    /// Returns `None` if the required handler params aren't in scope (e.g.
    /// the function is being passed to a HOF that handles the effects).
    /// The caller should fall back to `make_fun`/`FunRef` in that case.
    fn lower_effectful_fun_ref(
        &mut self,
        effects: &[String],
        total_arity: usize,
        make_call: impl FnOnce(Vec<CExpr>) -> CExpr,
    ) -> Option<CExpr> {
        let handler_ops = self.effect_handler_ops(effects);
        let return_k_count = if handler_ops.is_empty() { 0 } else { 1 };
        let user_arity = total_arity - handler_ops.len() - return_k_count;

        // Check that all required handler params are in scope
        for (eff, op) in &handler_ops {
            let key = format!("{}.{}", eff, op);
            if !self.current_handler_params.contains_key(&key) {
                return None;
            }
        }

        let mut params = Vec::new();
        let mut call_args = Vec::new();
        for _ in 0..user_arity {
            let p = self.fresh();
            call_args.push(CExpr::Var(p.clone()));
            params.push(p);
        }

        for (eff, op) in &handler_ops {
            let key = format!("{}.{}", eff, op);
            let param = self.current_handler_params.get(&key).unwrap();
            call_args.push(CExpr::Var(param.clone()));
        }

        if !handler_ops.is_empty() {
            let rk = self.fresh();
            call_args.push(CExpr::Fun(
                vec![rk.clone()],
                Box::new(CExpr::Var(rk)),
            ));
        }

        Some(CExpr::Fun(params, Box::new(make_call(call_args))))
    }

    /// Check if a function is effectful.
    fn is_effectful(&self, name: &str) -> bool {
        self.fun_info
            .get(name)
            .is_some_and(|f| !f.effects.is_empty())
    }

    /// Get a function's arity.
    fn fun_arity(&self, name: &str) -> Option<usize> {
        self.fun_info.get(name).map(|f| f.arity)
    }

    /// Get a function's effects.
    fn fun_effects(&self, name: &str) -> Option<&Vec<String>> {
        self.fun_info
            .get(name)
            .map(|f| &f.effects)
            .filter(|e| !e.is_empty())
    }

    /// Get a function's effects from the resolution map, falling back to fun_info
    /// for resolved names whose effect list was empty in the resolver.
    fn resolved_effects(&self, node_id: crate::ast::NodeId, name: &str) -> Option<Vec<String>> {
        use super::resolve::ResolvedName;
        match self.resolved.get(&node_id) {
            Some(ResolvedName::ImportedFun { effects, .. })
            | Some(ResolvedName::LocalFun { effects, .. })
                if !effects.is_empty() =>
            {
                Some(effects.clone())
            }
            Some(ResolvedName::ImportedFun { .. }) | Some(ResolvedName::LocalFun { .. }) => {
                // Resolved as a function but effects were empty in the resolver.
                // Fall back to fun_info which has CPS-expanded effect info.
                self.fun_effects(name).cloned()
            }
            Some(ResolvedName::ExternalFun { .. }) => None,
            // Not in resolution map → local variable, no effects.
            None => None,
        }
    }

    /// Emit a function call using the resolution map.
    fn emit_call(
        &self,
        func_name: &str,
        head_node_id: crate::ast::NodeId,
        arity: usize,
        call_args: Vec<CExpr>,
        span: Option<&crate::token::Span>,
    ) -> CExpr {
        use super::resolve::ResolvedName;
        let call = match self.resolved.get(&head_node_id) {
            Some(ResolvedName::ExternalFun {
                erlang_mod,
                erlang_func,
                ..
            }) => {
                // float_to_list/1 -> float_to_list/2 with [short] option
                if erlang_mod == "erlang" && erlang_func == "float_to_list" && call_args.len() == 1
                {
                    let opts = CExpr::Cons(
                        Box::new(CExpr::Lit(CLit::Atom("short".into()))),
                        Box::new(CExpr::Nil),
                    );
                    CExpr::Call(
                        erlang_mod.clone(),
                        erlang_func.clone(),
                        vec![call_args.into_iter().next().unwrap(), opts],
                    )
                } else {
                    CExpr::Call(erlang_mod.clone(), erlang_func.clone(), call_args)
                }
            }
            Some(ResolvedName::ImportedFun {
                erlang_mod,
                name: erl_name,
                ..
            }) => CExpr::Call(erlang_mod.clone(), erl_name.clone(), call_args),
            Some(ResolvedName::LocalFun { name, .. }) => {
                CExpr::Apply(Box::new(CExpr::FunRef(name.clone(), arity)), call_args)
            }
            _ => {
                // Not in resolution map: local function or variable apply
                CExpr::Apply(
                    Box::new(CExpr::FunRef(func_name.to_string(), arity)),
                    call_args,
                )
            }
        };
        self.annotate(call, span)
    }

    /// Get a function's param absorbed effects.
    fn param_absorbed_effects(&self, name: &str) -> Option<&HashMap<usize, Vec<String>>> {
        self.fun_info
            .get(name)
            .map(|f| &f.param_absorbed_effects)
            .filter(|m| !m.is_empty())
    }

    /// Find a record name that contains the given field.
    fn find_record_by_field(&self, field: &str) -> Option<&str> {
        self.record_fields.iter().find_map(|(rname, fields)| {
            if fields.iter().any(|f| f == field) {
                Some(rname.as_str())
            } else {
                None
            }
        })
    }

    /// Find a record name whose field list contains all the given update field names.
    fn find_record_by_fields(&self, field_names: &[String]) -> Option<&str> {
        self.record_fields.iter().find_map(|(rname, fields)| {
            if field_names.iter().all(|f| fields.contains(f)) {
                Some(rname.as_str())
            } else {
                None
            }
        })
    }

    pub fn lower_module(&mut self, module_name: &str, program: &ast::Program) -> CModule {
        self.current_module = module_name.to_string();
        let mut pending_annotations = self.init_module(module_name, program);

        // Group FunBindings by name, preserving declaration order, and simultaneously
        // populate top_level_funs. Handler params are added to the arity for effectful funs.
        let mut clause_groups: Vec<(String, usize, Vec<Clause>, crate::token::Span)> = Vec::new();
        let mut dict_constructors: Vec<(&str, &[String], &[Expr])> = Vec::new();
        let mut val_bindings: Vec<(&str, bool, &Expr)> = Vec::new(); // (name, is_inline, value)
        for decl in program {
            match decl {
                Decl::FunBinding {
                    name,
                    params,
                    guard,
                    body,
                    span,
                    ..
                } => {
                    let PendingAnnotation {
                        mut effects,
                        mut param_absorbed_effects,
                    } = pending_annotations
                        .remove(name.as_str())
                        .unwrap_or(PendingAnnotation {
                            effects: Vec::new(),
                            param_absorbed_effects: HashMap::new(),
                        });
                    if effects.is_empty()
                        && let Some(cr) = &self.check_result
                        && let Some(scheme) = cr.env.get(name)
                    {
                        let resolved_ty = cr.sub.apply(&scheme.ty);
                        effects = self.canonicalize_effects(
                            util::arity_and_effects_from_type(&resolved_ty).1,
                        );
                        param_absorbed_effects =
                            util::param_absorbed_effects_from_type(&resolved_ty)
                                .into_iter()
                                .map(|(idx, effs)| (idx, self.canonicalize_effects(effs)))
                                .collect();
                    }
                    let base_arity = lower_params(params).len() + count_lambda_params(body);
                    let arity = self.expanded_arity(base_arity, &effects);
                    if let Some(group) = clause_groups.iter_mut().find(|(n, _, _, _)| n == name) {
                        // Additional clause: just add to existing group
                        group.2.push((params, guard, body));
                    } else {
                        // First clause: register fun_info for arity/effects lookup.
                        self.fun_info.insert(
                            name.clone(),
                            FunInfo {
                                arity,
                                effects,
                                param_absorbed_effects,
                            },
                        );
                        clause_groups.push((
                            name.clone(),
                            arity,
                            vec![(params, guard, body)],
                            *span,
                        ));
                    }
                }
                Decl::DictConstructor {
                    name,
                    dict_params,
                    methods,
                    ..
                } => {
                    self.fun_info.insert(
                        name.clone(),
                        FunInfo {
                            arity: dict_params.len(),
                            ..Default::default()
                        },
                    );
                    dict_constructors.push((name, dict_params, methods));
                }
                Decl::Val {
                    name,
                    annotations,
                    value,
                    ..
                } => {
                    let is_inline = annotations.iter().any(|a| a.name == "inline");
                    val_bindings.push((name, is_inline, value));
                }
                _ => {}
            }
        }

        let mut exports = Vec::new();
        let mut fun_defs = Vec::new();

        // If there's no module declaration, it's a single-file script -- export everything.
        let is_module = program.iter().any(|d| matches!(d, Decl::ModuleDecl { .. }));

        // Generate wrapper functions for external declarations so cross-module
        // imports can call them by the local name.
        for decl in program {
            if let Decl::FunSignature {
                public,
                name,
                params,
                annotations,
                ..
            } = decl
            {
                let Some((erl_module, erl_func)) = extract_external(annotations) else {
                    continue;
                };
                let arity = params.len();
                let arg_vars: Vec<String> = (0..arity).map(|i| format!("_Ext{}", i)).collect();
                let call_args: Vec<CExpr> =
                    arg_vars.iter().map(|v| CExpr::Var(v.clone())).collect();
                let call = CExpr::Call(erl_module.clone(), erl_func.clone(), call_args);
                fun_defs.push(CFunDef {
                    name: name.clone(),
                    arity,
                    body: CExpr::Fun(arg_vars, Box::new(call)),
                });
                if *public || !is_module {
                    exports.push((name.clone(), arity));
                }
            }
        }

        // Process @inline vals first so their expressions are available for substitution
        // when lowering function bodies.
        for &(name, is_inline, value) in &val_bindings {
            if is_inline {
                let lowered = self.lower_expr(value);
                self.inline_vals.insert(name.to_string(), lowered);
            }
        }

        for (name, arity, clauses, fun_span) in clause_groups {
            self.current_function = name.clone();
            if !is_module || self.pub_names.contains(&name) {
                exports.push((name.clone(), arity));
            }

            // Set up handler param context for effectful functions.
            let effects = self.fun_effects(&name).cloned().unwrap_or_default();
            let mut handler_entries: Vec<(String, String)> = Vec::new();
            for (eff, op) in &self.effect_handler_ops(&effects) {
                let key = format!("{}.{}", eff, op);
                let param = Self::handler_param_name(eff, op);
                handler_entries.push((key, param));
            }

            let saved_handler_params = std::mem::take(&mut self.current_handler_params);
            for (key, param) in &handler_entries {
                self.current_handler_params
                    .insert(key.clone(), param.clone());
            }
            let handler_param_names: Vec<String> =
                handler_entries.iter().map(|(_, p)| p.clone()).collect();
            // Set up effectful variable tracking for HOF absorption.
            // Map param indices to param names from the first clause's patterns.
            let saved_effectful_vars = std::mem::take(&mut self.current_effectful_vars);
            if let Some(param_effs) = self.param_absorbed_effects(&name).cloned() {
                let first_clause_params = clauses[0].0;
                for (idx, effs) in &param_effs {
                    if let Some(pat) = first_clause_params.get(*idx)
                        && let Pat::Var { name: src_name, .. } = pat
                    {
                        self.current_effectful_vars
                            .insert(src_name.clone(), effs.clone());
                    }
                }
            }

            let has_effects = !handler_param_names.is_empty();
            let base_arity = arity - handler_param_names.len() - if has_effects { 1 } else { 0 };

            // For effectful functions, set _ReturnK as current_return_k so
            // lower_block applies it at terminal positions. Handler aborts
            // bypass the function's normal return, so they skip _ReturnK.
            let saved_return_k = self.current_return_k.take();
            if has_effects {
                self.current_return_k = Some(CExpr::Var("_ReturnK".to_string()));
            }

            let all_simple_params = clauses.len() == 1
                && clauses[0].0.iter().all(|p| {
                    matches!(
                        p,
                        Pat::Var { .. }
                            | Pat::Wildcard { .. }
                            | Pat::Lit {
                                value: ast::Lit::Unit,
                                ..
                            }
                    )
                });
            let fun_body = if clauses.len() == 1 && clauses[0].1.is_none() && all_simple_params {
                // Single clause, no guard: emit directly without a case wrapper.
                let (params, _, body) = clauses[0];
                let mut params_ce = lower_params(params);
                // Absorb nested lambda params into the function's param list.
                // e.g. `f dict = fun x -> body` becomes `f(dict, x) = body`
                let mut body = body;
                while let ExprKind::Lambda {
                    params: lam_params,
                    body: lam_body,
                    ..
                } = &body.kind
                {
                    params_ce.extend(lower_params(lam_params));
                    body = lam_body;
                }
                params_ce.extend(handler_param_names.iter().cloned());
                if has_effects {
                    params_ce.push("_ReturnK".to_string());
                }
                // For non-block bodies, lower_block didn't run, so apply return_k.
                // Special case: if the body is a terminal effect call, pass _ReturnK
                // directly as K so abort-style handlers skip the rest (proper CPS).
                let body_ce = if has_effects && !matches!(body.kind, ExprKind::Block { .. }) {
                    if let Some((op_name, qualifier, args)) = collect_effect_call(body) {
                        let args_owned: Vec<Expr> = args.into_iter().cloned().collect();
                        self.lower_effect_call(
                            op_name,
                            qualifier,
                            &args_owned,
                            self.current_return_k.clone(),
                        )
                    } else if has_nested_effect_call(body) {
                        // Nested effect calls in branches (e.g. if/case with fail!):
                        // thread _ReturnK through branches so abort skips the wrap.
                        let k_var = self.fresh();
                        let k_ce = self.current_return_k.clone().unwrap();
                        let body_ce = self.lower_expr_with_k(body, &k_var);
                        CExpr::Let(k_var, Box::new(k_ce), Box::new(body_ce))
                    } else {
                        // Check for effectful function call: pass _ReturnK directly
                        let is_eff_call = collect_fun_call(body)
                            .map(|(name, _, _)| {
                                self.is_effectful(name)
                                    || self.current_effectful_vars.contains_key(name)
                            })
                            .unwrap_or(false);
                        if is_eff_call {
                            let saved = self.pending_callee_return_k.take();
                            self.pending_callee_return_k = self.current_return_k.clone();
                            let result = self.lower_expr(body);
                            self.pending_callee_return_k = saved;
                            result
                        } else {
                            let body_ce = self.lower_expr(body);
                            self.apply_return_k(body_ce)
                        }
                    }
                } else {
                    self.lower_expr(body)
                };
                CExpr::Fun(params_ce, Box::new(body_ce))
            } else {
                // Multi-clause or single clause with a guard: generate fresh arg vars
                // and case-match on them using proper Core Erlang values syntax.
                let mut arg_vars: Vec<String> =
                    (0..base_arity).map(|i| format!("_Arg{}", i)).collect();
                arg_vars.extend(handler_param_names.iter().cloned());
                if has_effects {
                    arg_vars.push("_ReturnK".to_string());
                }

                let arms: Vec<CArm> = clauses
                    .iter()
                    .map(|(params, guard, body)| {
                        // Unit params were dropped in arity counting; filter here too.
                        let non_unit_pats: Vec<&Pat> = params
                            .iter()
                            .filter(|p| {
                                !matches!(
                                    p,
                                    Pat::Lit {
                                        value: ast::Lit::Unit,
                                        ..
                                    }
                                )
                            })
                            .collect();
                        // Pattern only matches user params, not handler params
                        let pat = if base_arity == 1 {
                            lower_pat(
                                non_unit_pats[0],
                                &self.record_fields,
                                &self.constructor_atoms,
                            )
                        } else if base_arity == 0 {
                            // No user params to match on -- use wildcard
                            CPat::Wildcard
                        } else {
                            CPat::Values(
                                non_unit_pats
                                    .iter()
                                    .map(|p| {
                                        lower_pat(p, &self.record_fields, &self.constructor_atoms)
                                    })
                                    .collect(),
                            )
                        };
                        let guard_ce = guard.as_deref().map(|g| self.lower_expr(g));
                        let body_ce = if has_effects && !matches!(body.kind, ExprKind::Block { .. })
                        {
                            if let Some((op_name, qualifier, args)) = collect_effect_call(body) {
                                let args_owned: Vec<Expr> = args.into_iter().cloned().collect();
                                self.lower_effect_call(
                                    op_name,
                                    qualifier,
                                    &args_owned,
                                    self.current_return_k.clone(),
                                )
                            } else if has_nested_effect_call(body) {
                                let k_var = self.fresh();
                                let k_ce = self.current_return_k.clone().unwrap();
                                let body_ce = self.lower_expr_with_k(body, &k_var);
                                CExpr::Let(k_var, Box::new(k_ce), Box::new(body_ce))
                            } else {
                                let body_ce = self.lower_expr(body);
                                self.apply_return_k(body_ce)
                            }
                        } else {
                            self.lower_expr(body)
                        };
                        CArm {
                            pat,
                            guard: guard_ce,
                            body: body_ce,
                        }
                    })
                    .collect();

                // Scrutinee: bare variable for base_arity==1, Values expression otherwise.
                // For effectful arity-0 functions, case on a dummy atom.
                let scrut_ce = if base_arity == 0 {
                    CExpr::Lit(CLit::Atom("unit".to_string()))
                } else if base_arity == 1 {
                    CExpr::Var(arg_vars[0].clone())
                } else {
                    CExpr::Values(
                        arg_vars[..base_arity]
                            .iter()
                            .map(|v| CExpr::Var(v.clone()))
                            .collect(),
                    )
                };
                let case_ce = CExpr::Case(Box::new(scrut_ce), arms);
                CExpr::Fun(arg_vars, Box::new(case_ce))
            };

            self.current_return_k = saved_return_k;

            self.current_handler_params = saved_handler_params;
            self.current_effectful_vars = saved_effectful_vars;

            // fun_span is available for future use (e.g. function-level metadata)
            let _ = fun_span;
            fun_defs.push(CFunDef {
                name,
                arity,
                body: fun_body,
            });
        }

        // Emit dictionary constructor functions
        for (name, dict_params, methods) in dict_constructors {
            let arity = dict_params.len();
            let params: Vec<String> = dict_params.iter().map(|p| core_var(p)).collect();
            let method_exprs: Vec<CExpr> = methods.iter().map(|m| self.lower_expr(m)).collect();
            let body = CExpr::Tuple(method_exprs);
            exports.push((name.to_string(), arity));
            fun_defs.push(CFunDef {
                name: name.to_string(),
                arity,
                body: CExpr::Fun(params, Box::new(body)),
            });
        }

        // Lower non-inline val bindings to zero-arity functions.
        // (Inline vals were already processed before function clause lowering.)
        for (name, is_inline, value) in val_bindings {
            if is_inline {
                continue; // already in self.inline_vals
            }
            let lowered = self.lower_expr(value);
            if !is_module || self.pub_names.contains(name) {
                exports.push((name.to_string(), 0));
            }
            fun_defs.push(CFunDef {
                name: name.to_string(),
                arity: 0,
                body: CExpr::Fun(vec![], Box::new(lowered)),
            });
        }

        CModule {
            name: module_name.to_string(),
            exports,
            funs: fun_defs,
        }
    }

    pub(super) fn lower_expr(&mut self, expr: &Expr) -> CExpr {
        match &expr.kind {
            ExprKind::Lit { value, .. } => match value {
                Lit::String(s, kind) => {
                    let resolved = if kind.is_multiline() {
                        process_string_escapes(s)
                    } else {
                        s.clone()
                    };
                    lower_string_to_binary(&resolved)
                }
                _ => CExpr::Lit(lower_lit(value)),
            },

            ExprKind::Var { name, .. } => {
                use super::resolve::ResolvedName;
                match self.resolved.get(&expr.id) {
                    Some(ResolvedName::ImportedFun {
                        erlang_mod,
                        name: erl_name,
                        arity,
                        effects,
                    }) => {
                        if *arity == 0 {
                            CExpr::Call(erlang_mod.clone(), erl_name.clone(), vec![])
                        } else if !effects.is_empty() {
                            // Effectful function used as a value (eta reduction).
                            // Try to generate a wrapper that captures handlers
                            // from scope. Falls back to make_fun if handlers
                            // aren't available (e.g. passed to a HOF that
                            // handles effects internally).
                            let effects = effects.clone();
                            let arity = *arity;
                            let erl_mod = erlang_mod.clone();
                            let erl_fn = erl_name.clone();
                            self.lower_effectful_fun_ref(
                                &effects,
                                arity,
                                |args| CExpr::Call(erl_mod.clone(), erl_fn.clone(), args),
                            )
                            .unwrap_or_else(|| {
                                CExpr::Call(
                                    "erlang".to_string(),
                                    "make_fun".to_string(),
                                    vec![
                                        CExpr::Lit(CLit::Atom(erl_mod)),
                                        CExpr::Lit(CLit::Atom(erl_fn)),
                                        CExpr::Lit(CLit::Int(arity as i64)),
                                    ],
                                )
                            })
                        } else {
                            CExpr::Call(
                                "erlang".to_string(),
                                "make_fun".to_string(),
                                vec![
                                    CExpr::Lit(CLit::Atom(erlang_mod.clone())),
                                    CExpr::Lit(CLit::Atom(erl_name.clone())),
                                    CExpr::Lit(CLit::Int(*arity as i64)),
                                ],
                            )
                        }
                    }
                    Some(ResolvedName::ExternalFun {
                        erlang_mod,
                        erlang_func,
                        arity,
                    }) => CExpr::Call(
                        "erlang".to_string(),
                        "make_fun".to_string(),
                        vec![
                            CExpr::Lit(CLit::Atom(erlang_mod.clone())),
                            CExpr::Lit(CLit::Atom(erlang_func.clone())),
                            CExpr::Lit(CLit::Int(*arity as i64)),
                        ],
                    ),
                    Some(ResolvedName::LocalFun { name, arity, effects }) => {
                        if *arity == 0 {
                            // Val reference: check inline_vals first, then call
                            if let Some(inlined) = self.inline_vals.get(name) {
                                inlined.clone()
                            } else {
                                CExpr::Apply(Box::new(CExpr::FunRef(name.clone(), 0)), vec![])
                            }
                        } else {
                            // Check effects from resolution map first, then fall
                            // back to fun_info (needed for LetFun which the
                            // resolver registers with empty effects).
                            let eff = if !effects.is_empty() {
                                Some(effects.clone())
                            } else {
                                self.fun_effects(name).cloned().filter(|e| !e.is_empty())
                            };
                            if let Some(effects) = eff {
                                let fun_name = name.clone();
                                let lowered_arity =
                                    self.fun_arity(&fun_name).unwrap_or(*arity);
                                self.lower_effectful_fun_ref(
                                    &effects,
                                    lowered_arity,
                                    |args| {
                                        CExpr::Apply(
                                            Box::new(CExpr::FunRef(
                                                fun_name.clone(),
                                                lowered_arity,
                                            )),
                                            args,
                                        )
                                    },
                                )
                                .unwrap_or(CExpr::FunRef(fun_name, lowered_arity))
                            } else {
                                let lowered_arity = self.fun_arity(name).unwrap_or(*arity);
                                CExpr::FunRef(name.clone(), lowered_arity)
                            }
                        }
                    }
                    _ => {
                        // Not in resolution map: this is a local variable
                        // (function param, let binding, lambda param, case binding, etc.).
                        // The resolver is authoritative — if it didn't resolve the name,
                        // it's not a module-level or imported function.
                        if let Some(inlined) = self.inline_vals.get(name) {
                            inlined.clone()
                        } else if let Some(tuple) = self.lower_handler_def_to_tuple(name) {
                            // Handler used as a value (e.g. returned from a function,
                            // passed as argument): convert to tuple-of-lambdas.
                            tuple
                        } else {
                            CExpr::Var(core_var(name))
                        }
                    }
                }
            }

            ExprKind::App { .. } => {
                if let Some((ctor_name, args)) = collect_ctor_call(expr) {
                    return self.lower_ctor(ctor_name, args);
                }

                // Check for effect call: App(EffectCall { .. }, arg1, ...)
                if let Some((op_name, qualifier, args)) = collect_effect_call(expr) {
                    return self.lower_effect_call(
                        op_name,
                        qualifier,
                        &args.into_iter().cloned().collect::<Vec<_>>(),
                        None,
                    );
                }

                // Check for a qualified call: App(QualifiedName { module, name }, arg1, ...)
                // e.g. `Math.abs x` -> call 'math':'abs'(X)
                // Intercept Process.catch_panic as a builtin before general qualified call handling.
                if let Some((_module, func_name, _head, args)) = collect_qualified_call(expr)
                    && func_name == "catch_panic"
                    && args.len() == 1
                {
                    return self.lower_catch_panic(args[0]);
                }
                if let Some((module, func_name, head, args)) = collect_qualified_call(expr) {
                    // Check if this is a qualified constructor (e.g. M.Just, Std.Maybe.Just)
                    let qualified = format!("{}.{}", module, func_name);
                    if self.constructor_atoms.contains_key(&qualified)
                        || self.constructor_atoms.contains_key(func_name)
                    {
                        return self.lower_ctor(func_name, args);
                    }
                    return self.lower_qualified_call(
                        module,
                        func_name,
                        head,
                        &args,
                        Some(&expr.span),
                    );
                }

                // Lower print/println/eprint/eprintln to io:format, dbg to stderr+passthrough.
                // Match both bare names (builtins) and canonical names (after resolve pass).
                if let Some((func_name, _head, args)) = collect_fun_call(expr) {
                    let lowered = match func_name {
                        // todo maybe? these could be moved to the bridge files directly
                        "print_stdout" | "Std.IO.Unsafe.print_stdout" => {
                            self.lower_builtin_print(&args, false, false)
                        }
                        "print_stderr" | "Std.IO.Unsafe.print_stderr" => {
                            self.lower_builtin_print(&args, true, false)
                        }
                        "dbg" | "Std.IO.dbg" => self.lower_builtin_dbg(&args),
                        _ => None,
                    };
                    if let Some(ce) = lowered {
                        return ce;
                    }
                }

                // Lower `panic msg` / `todo ()` to erlang:error({dylang_error, ...})
                // These are true builtins (no module), so only bare names.
                if let Some((func_name, _head, args)) = collect_fun_call(expr)
                    && (func_name == "panic" || func_name == "todo")
                    && args.len() == 1
                {
                    let v = self.fresh();
                    let (kind, arg) = if func_name == "todo" {
                        (ErrorKind::Todo, lower_string_to_binary("not implemented"))
                    } else {
                        (ErrorKind::Panic, self.lower_expr(args[0]))
                    };
                    let error = self.make_error(kind, CExpr::Var(v.clone()), Some(&expr.span));
                    return CExpr::Let(v, Box::new(arg), Box::new(error));
                }

                // Lower `catch_panic thunk` to a Core Erlang try/catch.
                if let Some((func_name, _head, args)) = collect_fun_call(expr)
                    && (func_name == "catch_panic" || func_name == "Std.Process.catch_panic")
                    && args.len() == 1
                {
                    return self.lower_catch_panic(args[0]);
                }

                // Check for a saturated call to a known top-level function.
                // e.g. `add 3 4` -> App(App(Var("add"), 3), 4)
                // For effectful functions, the user provides N args but the function
                // takes N+M where M is the number of handler params. We thread
                // the caller's handler params through automatically.
                //
                // Only attempt saturation/partial-application if the resolver
                // confirmed the head is a function (top-level, imported, external,
                // or LetFun). If the head Var is not in the resolution map, it's a
                // local variable — fall through to generic apply.
                if let Some((func_name, head_expr, args)) = collect_fun_call(expr)
                    && self.resolved.contains_key(&head_expr.id)
                {
                    let callee_effects = self.resolved_effects(head_expr.id, func_name);
                    let callee_ops = callee_effects
                        .as_ref()
                        .map(|effs| self.effect_handler_ops(effs))
                        .unwrap_or_default();
                    // Build (key, param_name) list for callee handler params
                    let mut callee_handler_entries: Vec<(String, String)> = Vec::new();
                    for (eff, op) in &callee_ops {
                        callee_handler_entries
                            .push((format!("{}.{}", eff, op), Self::handler_param_name(eff, op)));
                    }
                    let effect_count = callee_handler_entries.len();
                    let total_arity = self.fun_arity(func_name);

                    // Filter out unit literal args (they don't count toward arity)
                    let non_unit_args: Vec<&Expr> = args
                        .into_iter()
                        .filter(|a| {
                            !matches!(
                                a.kind,
                                ExprKind::Lit {
                                    value: ast::Lit::Unit,
                                    ..
                                }
                            )
                        })
                        .collect();

                    let return_k_count = if effect_count > 0 { 1 } else { 0 };
                    if let Some(arity) = total_arity
                        && non_unit_args.len() + effect_count + return_k_count == arity
                    {
                        // Saturated call: apply fun 'name'/N(arg1, ..., argN, handler1, ...)
                        let mut arg_vars: Vec<String> = Vec::new();
                        let mut bindings: Vec<(String, CExpr)> = Vec::new();
                        let callee_param_effs = self.param_absorbed_effects(func_name).cloned();
                        for (i, arg) in non_unit_args.iter().enumerate() {
                            let v = self.fresh();
                            // If this arg position has absorbed effects, set context
                            // so lambdas at this position get handler params added.
                            let saved_ctx = self.lambda_effect_context.take();
                            if let Some(ref pe) = callee_param_effs
                                && let Some(effs) = pe.get(&i)
                            {
                                self.lambda_effect_context = Some(effs.clone());
                            }
                            let ce = self.lower_expr(arg);
                            self.lambda_effect_context = saved_ctx;
                            arg_vars.push(v.clone());
                            bindings.push((v, ce));
                        }
                        // Append per-op handler params for effectful callees.
                        // Every effect op must have a handler param in scope — either
                        // from the enclosing function's `needs` clause or from a `with` block.
                        // If one is missing, it's a compiler bug (the type system should
                        // have ensured all effects are handled).
                        if !callee_handler_entries.is_empty() {
                            for (key, _) in &callee_handler_entries {
                                let param =
                                    self.current_handler_params.get(key).unwrap_or_else(|| {
                                        panic!(
                                            "ICE: saturated call to '{}' needs handler for '{}' \
                                         but no handler param in scope. params: {:?}",
                                            func_name, key, self.current_handler_params,
                                        )
                                    });
                                arg_vars.push(param.clone());
                            }
                            // Pass _ReturnK: take from pending (set by `with`), or identity
                            let return_k =
                                self.pending_callee_return_k.take().unwrap_or_else(|| {
                                    let p = self.fresh();
                                    CExpr::Fun(vec![p.clone()], Box::new(CExpr::Var(p)))
                                });
                            let rk_var = self.fresh();
                            bindings.push((rk_var.clone(), return_k));
                            arg_vars.push(rk_var);
                        }
                        {
                            let call_args: Vec<CExpr> =
                                arg_vars.iter().map(|v| CExpr::Var(v.clone())).collect();
                            let call = self.emit_call(
                                func_name,
                                head_expr.id,
                                arity,
                                call_args,
                                Some(&expr.span),
                            );
                            return bindings.into_iter().rev().fold(call, |body, (var, val)| {
                                CExpr::Let(var, Box::new(val), Box::new(body))
                            });
                        }
                    }

                    // Partial application: fewer user args than user-arg slots.
                    // Wraps in a lambda taking the remaining user args.
                    // For effectful functions, handler params are captured from scope
                    // (bound by `with`) and the lambda also takes _ReturnK.
                    if let Some(arity) = total_arity {
                        let user_slots = arity - effect_count - return_k_count;
                        if non_unit_args.len() < user_slots {
                            let remaining_user = user_slots - non_unit_args.len();
                            let mut arg_vars: Vec<String> = Vec::new();
                            let mut bindings: Vec<(String, CExpr)> = Vec::new();
                            for arg in &non_unit_args {
                                let v = self.fresh();
                                let ce = self.lower_expr(arg);
                                arg_vars.push(v.clone());
                                bindings.push((v, ce));
                            }
                            // Remaining user-visible params
                            let mut params: Vec<String> = Vec::new();
                            for _ in 0..remaining_user {
                                params.push(self.fresh());
                            }
                            // Build call args: given args + remaining user params
                            let mut call_args: Vec<CExpr> =
                                arg_vars.iter().map(|v| CExpr::Var(v.clone())).collect();
                            call_args.extend(params.iter().map(|p| CExpr::Var(p.clone())));
                            // For effectful functions, include handler params and
                            // _ReturnK in the lambda. Handlers will be provided at
                            // the eventual call site via `with`.
                            if !callee_handler_entries.is_empty() {
                                for (_, p) in &callee_handler_entries {
                                    params.push(p.clone());
                                    call_args.push(CExpr::Var(p.clone()));
                                }
                                let rk = "_ReturnK".to_string();
                                params.push(rk.clone());
                                call_args.push(CExpr::Var(rk));
                            }
                            let call = self.emit_call(
                                func_name,
                                head_expr.id,
                                arity,
                                call_args,
                                Some(&expr.span),
                            );
                            let lambda = CExpr::Fun(params, Box::new(call));
                            return bindings.into_iter().rev().fold(lambda, |body, (var, val)| {
                                CExpr::Let(var, Box::new(val), Box::new(body))
                            });
                        }
                    }
                }

                // Check for call to an effectful variable (HOF absorption).
                // e.g. `computation ()` where computation absorbs Fail
                if let Some((var_name, _, args)) = collect_fun_call(expr)
                    && let Some(absorbed) = self.current_effectful_vars.get(var_name).cloned()
                {
                    let mut arg_vars: Vec<String> = Vec::new();
                    let mut bindings: Vec<(String, CExpr)> = Vec::new();
                    // Filter out unit literal args
                    let non_unit_args: Vec<&Expr> = args
                        .into_iter()
                        .filter(|a| {
                            !matches!(
                                a.kind,
                                ExprKind::Lit {
                                    value: ast::Lit::Unit,
                                    ..
                                }
                            )
                        })
                        .collect();
                    for arg in non_unit_args {
                        let v = self.fresh();
                        let ce = self.lower_expr(arg);
                        arg_vars.push(v.clone());
                        bindings.push((v, ce));
                    }
                    // Append per-op handler params for absorbed effects
                    let absorbed_ops = self.effect_handler_ops(&absorbed);
                    for (eff, op) in &absorbed_ops {
                        let key = format!("{}.{}", eff, op);
                        if let Some(param) = self.current_handler_params.get(&key) {
                            arg_vars.push(param.clone());
                        } else {
                            panic!(
                                "effectful variable '{}' needs handler for '{}.{}' but no handler param in scope",
                                var_name, eff, op
                            );
                        }
                    }
                    // Pass _ReturnK: take from pending (set by `with`), or identity
                    {
                        let return_k = self.pending_callee_return_k.take().unwrap_or_else(|| {
                            let p = self.fresh();
                            CExpr::Fun(vec![p.clone()], Box::new(CExpr::Var(p)))
                        });
                        let rk_var = self.fresh();
                        bindings.push((rk_var.clone(), return_k));
                        arg_vars.push(rk_var);
                    }
                    let call = CExpr::Apply(
                        Box::new(CExpr::Var(core_var(var_name))),
                        arg_vars.iter().map(|v| CExpr::Var(v.clone())).collect(),
                    );
                    return bindings.into_iter().rev().fold(call, |body, (var, val)| {
                        CExpr::Let(var, Box::new(val), Box::new(body))
                    });
                }

                // Collect the full App chain and emit a single multi-arg Apply.
                // e.g. `f acc h` = App(App(f, acc), h) -> apply F(Acc, H)
                let mut callee = expr;
                let mut args_rev = Vec::new();
                while let ExprKind::App { func, arg, .. } = &callee.kind {
                    args_rev.push(arg.as_ref());
                    callee = func.as_ref();
                }
                args_rev.reverse();

                // Filter out unit literal args
                let args: Vec<&Expr> = args_rev
                    .into_iter()
                    .filter(|a| {
                        !matches!(
                            a.kind,
                            ExprKind::Lit {
                                value: ast::Lit::Unit,
                                ..
                            }
                        )
                    })
                    .collect();

                // Check if callee is a known function with mismatched arity.
                // If so, split into a saturated call + apply of remaining args.
                // Only consult fun_info if the resolver confirmed this is a function.
                let callee_arity = match &callee.kind {
                    ExprKind::Var { name, .. } if self.resolved.contains_key(&callee.id) => {
                        self.fun_arity(name)
                    }
                    _ => None,
                };

                if let Some(arity) = callee_arity
                    && arity < args.len()
                {
                    let mut bindings = Vec::new();

                    // Lower all args
                    let mut arg_vars = Vec::new();
                    for arg in &args {
                        let v = self.fresh();
                        let ce = self.lower_expr(arg);
                        bindings.push((v.clone(), ce));
                        arg_vars.push(v);
                    }

                    // Saturated call with the first `arity` args
                    let sat_args: Vec<CExpr> = arg_vars[..arity]
                        .iter()
                        .map(|v| CExpr::Var(v.clone()))
                        .collect();
                    let func_ce = self.lower_expr(callee);
                    let result_var = self.fresh();
                    bindings.push((
                        result_var.clone(),
                        CExpr::Apply(Box::new(func_ce), sat_args),
                    ));

                    // Apply remaining args to the result
                    let extra_args: Vec<CExpr> = arg_vars[arity..]
                        .iter()
                        .map(|v| CExpr::Var(v.clone()))
                        .collect();
                    let call = CExpr::Apply(Box::new(CExpr::Var(result_var)), extra_args);
                    bindings.into_iter().rev().fold(call, |body, (var, val)| {
                        CExpr::Let(var, Box::new(val), Box::new(body))
                    })
                } else {
                    let mut bindings = Vec::new();
                    let func_var = self.fresh();
                    let func_ce = self.lower_expr(callee);
                    bindings.push((func_var.clone(), func_ce));

                    let mut arg_vars = Vec::new();
                    for arg in &args {
                        let v = self.fresh();
                        let ce = self.lower_expr(arg);
                        bindings.push((v.clone(), ce));
                        arg_vars.push(v);
                    }

                    let call = CExpr::Apply(
                        Box::new(CExpr::Var(func_var)),
                        arg_vars.into_iter().map(CExpr::Var).collect(),
                    );
                    bindings.into_iter().rev().fold(call, |body, (var, val)| {
                        CExpr::Let(var, Box::new(val), Box::new(body))
                    })
                }
            }

            ExprKind::Constructor { name, .. } => match name.as_str() {
                "Nil" => CExpr::Nil,
                // Booleans are bare atoms to match Erlang's native true/false
                "True" => CExpr::Lit(CLit::Atom("true".to_string())),
                "False" => CExpr::Lit(CLit::Atom("false".to_string())),
                // ExitReason constructors are bare atoms to match Erlang exit reasons
                "Normal" => CExpr::Lit(CLit::Atom("normal".to_string())),
                "Shutdown" => CExpr::Lit(CLit::Atom("shutdown".to_string())),
                "Killed" => CExpr::Lit(CLit::Atom("killed".to_string())),
                "Noproc" => CExpr::Lit(CLit::Atom("noproc".to_string())),
                _ => {
                    let atom = util::mangle_ctor_atom(name, &self.constructor_atoms);
                    // Wrap in a 1-tuple to match pattern representation and avoid atom collisions
                    CExpr::Tuple(vec![CExpr::Lit(CLit::Atom(atom))])
                }
            },

            ExprKind::BinOp {
                op, left, right, ..
            } => self.lower_binop(op, left, right, Some(&expr.span)),

            ExprKind::UnaryMinus { expr, .. } => {
                let v = self.fresh();
                let ce = self.lower_expr(expr);
                CExpr::Let(
                    v.clone(),
                    Box::new(ce),
                    Box::new(cerl_call(
                        "erlang",
                        "-",
                        vec![CExpr::Lit(CLit::Int(0)), CExpr::Var(v)],
                    )),
                )
            }

            ExprKind::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => {
                let cond_var = self.fresh();
                let cond_ce = self.lower_expr(cond);
                let then_ce = self.lower_expr(then_branch);
                let else_ce = self.lower_expr(else_branch);
                CExpr::Let(
                    cond_var.clone(),
                    Box::new(cond_ce),
                    Box::new(CExpr::Case(
                        Box::new(CExpr::Var(cond_var)),
                        vec![
                            CArm {
                                pat: CPat::Lit(CLit::Atom("true".to_string())),
                                guard: None,
                                body: then_ce,
                            },
                            CArm {
                                pat: CPat::Lit(CLit::Atom("false".to_string())),
                                guard: None,
                                body: else_ce,
                            },
                        ],
                    )),
                )
            }

            ExprKind::Block { stmts, .. } => {
                let stmts: Vec<_> = stmts.iter().map(|a| a.node.clone()).collect();
                self.lower_block(&stmts)
            }

            ExprKind::Lambda { params, body, .. } => {
                let all_simple = params.iter().all(|p| {
                    matches!(
                        p,
                        Pat::Var { .. }
                            | Pat::Wildcard { .. }
                            | Pat::Lit {
                                value: ast::Lit::Unit,
                                ..
                            }
                    )
                });
                let mut param_vars = lower_params(params);
                let saved_handler_params = self.current_handler_params.clone();
                let saved_return_k = self.current_return_k.take();
                // If a lambda_effect_context is set (from being passed to an
                // effectful HOF parameter), add handler params for those effects.
                // This ensures both pure and effectful lambdas have the right arity.
                let mut is_effectful_lambda = false;
                if let Some(effects) = self.lambda_effect_context.take() {
                    let lambda_ops = self.effect_handler_ops(&effects);
                    for (eff, op) in &lambda_ops {
                        let handler_var = Self::handler_param_name(eff, op);
                        param_vars.push(handler_var.clone());
                        let key = format!("{}.{}", eff, op);
                        self.current_handler_params.insert(key, handler_var);
                    }
                    // Add _ReturnK parameter for effectful lambdas
                    param_vars.push("_ReturnK".to_string());
                    self.current_return_k = Some(CExpr::Var("_ReturnK".to_string()));
                    is_effectful_lambda = true;
                } else {
                    // Not in a HOF context, but check if the body uses effects
                    // directly (e.g. lambda defined in a block that already has
                    // handler params in scope -- those are captured, not parameterized).
                }
                let body_ce = if is_effectful_lambda && !matches!(body.kind, ExprKind::Block { .. })
                {
                    if let Some((op_name, qualifier, args)) = collect_effect_call(body) {
                        let args_owned: Vec<Expr> = args.into_iter().cloned().collect();
                        self.lower_effect_call(
                            op_name,
                            qualifier,
                            &args_owned,
                            self.current_return_k.clone(),
                        )
                    } else if has_nested_effect_call(body) {
                        let k_var = self.fresh();
                        let k_ce = self.current_return_k.clone().unwrap();
                        let body_ce = self.lower_expr_with_k(body, &k_var);
                        CExpr::Let(k_var, Box::new(k_ce), Box::new(body_ce))
                    } else {
                        // Check for effectful function call: pass _ReturnK directly
                        let is_eff_call = collect_fun_call(body)
                            .map(|(name, _, _)| {
                                self.is_effectful(name)
                                    || self.current_effectful_vars.contains_key(name)
                            })
                            .unwrap_or(false);
                        if is_eff_call {
                            let saved = self.pending_callee_return_k.take();
                            self.pending_callee_return_k = self.current_return_k.clone();
                            let result = self.lower_expr(body);
                            self.pending_callee_return_k = saved;
                            result
                        } else {
                            let body_ce = self.lower_expr(body);
                            self.apply_return_k(body_ce)
                        }
                    }
                } else {
                    self.lower_expr(body)
                };
                self.current_handler_params = saved_handler_params;
                self.current_return_k = saved_return_k;
                // If lambda has complex params (tuples, constructors), wrap
                // the body in a case expression for destructuring.
                let body_ce = if !all_simple {
                    let scrutinee = if param_vars.len() == 1 {
                        CExpr::Var(param_vars[0].clone())
                    } else {
                        CExpr::Tuple(param_vars.iter().map(|v| CExpr::Var(v.clone())).collect())
                    };
                    let pat = if params.len() == 1 {
                        lower_pat(&params[0], &self.record_fields, &self.constructor_atoms)
                    } else {
                        CPat::Tuple(
                            params
                                .iter()
                                .map(|p| lower_pat(p, &self.record_fields, &self.constructor_atoms))
                                .collect(),
                        )
                    };
                    CExpr::Case(
                        Box::new(scrutinee),
                        vec![CArm {
                            pat,
                            guard: None,
                            body: body_ce,
                        }],
                    )
                } else {
                    body_ce
                };
                CExpr::Fun(param_vars, Box::new(body_ce))
            }

            ExprKind::Case {
                scrutinee, arms, ..
            } => {
                let scrut_var = self.fresh();
                let scrut_ce = self.lower_expr(scrutinee);
                let arms: Vec<_> = arms.iter().map(|a| a.node.clone()).collect();
                let arms_ce = self.lower_case_arms(&scrut_var, &arms);
                CExpr::Let(
                    scrut_var.clone(),
                    Box::new(scrut_ce),
                    Box::new(CExpr::Case(Box::new(CExpr::Var(scrut_var)), arms_ce)),
                )
            }

            ExprKind::Receive {
                arms, after_clause, ..
            } => {
                // Lower arms: same pattern/guard/body as case, but for receive
                // there is no scrutinee variable to fall through to.
                let lowered_arms: Vec<CArm> = arms
                    .iter()
                    .map(|annotated| {
                        let arm = &annotated.node;
                        // System message patterns: bind a raw reason variable
                        // and wrap the body with a conversion case.
                        let (pat, reason_wrapper) = if let Pat::Constructor { name, args, .. } =
                            &arm.pattern
                        {
                            if matches!(name.as_str(), "Down" | "Exit") && args.len() == 2 {
                                // Check if reason arg is a variable that needs conversion
                                let (reason_pat, wrapper) =
                                    if let Pat::Var { name: var_name, .. } = &args[1] {
                                        let raw = self.fresh();
                                        (CPat::Var(raw.clone()), Some((core_var(var_name), raw)))
                                    } else {
                                        (
                                            lower_pat(
                                                &args[1],
                                                &self.record_fields,
                                                &self.constructor_atoms,
                                            ),
                                            None,
                                        )
                                    };

                                let tuple_pat = if name == "Down" {
                                    // {'DOWN', _Ref, 'process', Pid, Reason}
                                    CPat::Tuple(vec![
                                        CPat::Lit(CLit::Atom("DOWN".into())),
                                        CPat::Wildcard,
                                        CPat::Lit(CLit::Atom("process".into())),
                                        lower_pat(
                                            &args[0],
                                            &self.record_fields,
                                            &self.constructor_atoms,
                                        ),
                                        reason_pat,
                                    ])
                                } else {
                                    // {'EXIT', Pid, Reason}
                                    CPat::Tuple(vec![
                                        CPat::Lit(CLit::Atom("EXIT".into())),
                                        lower_pat(
                                            &args[0],
                                            &self.record_fields,
                                            &self.constructor_atoms,
                                        ),
                                        reason_pat,
                                    ])
                                };
                                (tuple_pat, wrapper)
                            } else {
                                (
                                    lower_pat(
                                        &arm.pattern,
                                        &self.record_fields,
                                        &self.constructor_atoms,
                                    ),
                                    None,
                                )
                            }
                        } else {
                            (
                                lower_pat(
                                    &arm.pattern,
                                    &self.record_fields,
                                    &self.constructor_atoms,
                                ),
                                None,
                            )
                        };
                        let guard = arm.guard.as_ref().map(|g| self.lower_expr(g));
                        let raw_body = self.lower_expr(&arm.body);
                        // Convert raw Erlang exit reason to ExitReason type
                        let body = if let Some((user_var, raw_var)) = reason_wrapper {
                            let cm = &self.constructor_atoms;
                            let normal = util::mangle_ctor_atom("Normal", cm);
                            let shutdown = util::mangle_ctor_atom("Shutdown", cm);
                            let killed = util::mangle_ctor_atom("Killed", cm);
                            let noproc = util::mangle_ctor_atom("Noproc", cm);
                            let error = util::mangle_ctor_atom("Error", cm);
                            let other = util::mangle_ctor_atom("Other", cm);
                            // case RawReason of
                            //   'normal' -> Normal
                            //   'shutdown' -> Shutdown
                            //   'killed' -> Killed
                            //   'noproc' -> Noproc
                            //   {dylang_panic, Msg} -> Error(Msg)
                            //   {_, Msg, _Stacktrace} -> Error(Msg)
                            //   Other -> Other(io_lib:format("~p", [Other]))
                            let other_var = self.fresh();
                            let fmt_var = self.fresh();
                            let stringify = cerl_call(
                                "unicode",
                                "characters_to_binary",
                                vec![cerl_call(
                                    "io_lib",
                                    "format",
                                    vec![
                                        CExpr::Lit(CLit::Str("~p".into())),
                                        CExpr::Cons(
                                            Box::new(CExpr::Var(other_var.clone())),
                                            Box::new(CExpr::Nil),
                                        ),
                                    ],
                                )],
                            );
                            let error_msg_var = self.fresh();
                            let conversion = CExpr::Case(
                                Box::new(CExpr::Var(raw_var)),
                                vec![
                                    CArm {
                                        pat: CPat::Lit(CLit::Atom("normal".into())),
                                        guard: None,
                                        body: CExpr::Lit(CLit::Atom(normal.clone())),
                                    },
                                    CArm {
                                        pat: CPat::Lit(CLit::Atom("shutdown".into())),
                                        guard: None,
                                        body: CExpr::Lit(CLit::Atom(shutdown.clone())),
                                    },
                                    CArm {
                                        pat: CPat::Lit(CLit::Atom("killed".into())),
                                        guard: None,
                                        body: CExpr::Lit(CLit::Atom(killed.clone())),
                                    },
                                    CArm {
                                        pat: CPat::Lit(CLit::Atom("noproc".into())),
                                        guard: None,
                                        body: CExpr::Lit(CLit::Atom(noproc.clone())),
                                    },
                                    // {{dylang_error, _Kind, Msg, ...}, _Stacktrace} -> Error(Msg)
                                    CArm {
                                        pat: CPat::Tuple(vec![
                                            CPat::Tuple(vec![
                                                CPat::Lit(CLit::Atom("dylang_error".into())),
                                                CPat::Wildcard, // kind
                                                CPat::Var(error_msg_var.clone()),
                                                CPat::Wildcard, // module
                                                CPat::Wildcard, // function
                                                CPat::Wildcard, // file
                                                CPat::Wildcard, // line
                                            ]),
                                            CPat::Wildcard, // stacktrace
                                        ]),
                                        guard: None,
                                        body: CExpr::Tuple(vec![
                                            CExpr::Lit(CLit::Atom(error.clone())),
                                            CExpr::Var(error_msg_var.clone()),
                                        ]),
                                    },
                                    // {Msg, _Stacktrace} when is_binary(Msg) -> Error(Msg)
                                    {
                                        let error_msg_var2 = self.fresh();
                                        CArm {
                                            pat: CPat::Tuple(vec![
                                                CPat::Var(error_msg_var2.clone()),
                                                CPat::Wildcard, // stacktrace
                                            ]),
                                            guard: Some(cerl_call(
                                                "erlang",
                                                "is_binary",
                                                vec![CExpr::Var(error_msg_var2.clone())],
                                            )),
                                            body: CExpr::Tuple(vec![
                                                CExpr::Lit(CLit::Atom(error.clone())),
                                                CExpr::Var(error_msg_var2),
                                            ]),
                                        }
                                    },
                                    CArm {
                                        pat: CPat::Var(other_var.clone()),
                                        guard: None,
                                        body: CExpr::Let(
                                            fmt_var.clone(),
                                            Box::new(stringify),
                                            Box::new(CExpr::Tuple(vec![
                                                CExpr::Lit(CLit::Atom(other.clone())),
                                                CExpr::Var(fmt_var),
                                            ])),
                                        ),
                                    },
                                ],
                            );
                            CExpr::Let(user_var, Box::new(conversion), Box::new(raw_body))
                        } else {
                            raw_body
                        };
                        CArm { pat, guard, body }
                    })
                    .collect();

                let (timeout, timeout_body) = if let Some((t, b)) = after_clause {
                    (self.lower_expr(t), self.lower_expr(b))
                } else {
                    (
                        CExpr::Lit(CLit::Atom("infinity".into())),
                        CExpr::Lit(CLit::Atom("true".into())),
                    )
                };

                CExpr::Receive(lowered_arms, Box::new(timeout), Box::new(timeout_body))
            }

            ExprKind::Tuple { elements, .. } => self.lower_tuple_elems(elements),

            ExprKind::QualifiedName { module, name, .. } => {
                // Check if this is a qualified constructor with no args (e.g. M.Nothing)
                let qualified = format!("{}.{}", module, name);
                if self.constructor_atoms.contains_key(&qualified)
                    || self.constructor_atoms.contains_key(name.as_str())
                {
                    return self.lower_ctor(name, vec![]);
                }
                use super::resolve::ResolvedName;
                if let Some(resolved) = self.resolved.get(&expr.id) {
                    match resolved {
                        ResolvedName::ImportedFun {
                            erlang_mod,
                            name: erl_name,
                            arity,
                            ..
                        } => {
                            if *arity == 0 {
                                CExpr::Call(erlang_mod.clone(), erl_name.clone(), vec![])
                            } else {
                                CExpr::Call(
                                    "erlang".to_string(),
                                    "make_fun".to_string(),
                                    vec![
                                        CExpr::Lit(CLit::Atom(erlang_mod.clone())),
                                        CExpr::Lit(CLit::Atom(erl_name.clone())),
                                        CExpr::Lit(CLit::Int(*arity as i64)),
                                    ],
                                )
                            }
                        }
                        ResolvedName::ExternalFun {
                            erlang_mod,
                            erlang_func,
                            arity,
                        } => CExpr::Call(
                            "erlang".to_string(),
                            "make_fun".to_string(),
                            vec![
                                CExpr::Lit(CLit::Atom(erlang_mod.clone())),
                                CExpr::Lit(CLit::Atom(erlang_func.clone())),
                                CExpr::Lit(CLit::Int(*arity as i64)),
                            ],
                        ),
                        ResolvedName::LocalFun { name, arity, .. } => {
                            if *arity == 0 {
                                if let Some(inlined) = self.inline_vals.get(name) {
                                    inlined.clone()
                                } else {
                                    CExpr::Apply(Box::new(CExpr::FunRef(name.clone(), 0)), vec![])
                                }
                            } else {
                                let lowered_arity = self.fun_arity(name).unwrap_or(*arity);
                                CExpr::FunRef(name.clone(), lowered_arity)
                            }
                        }
                    }
                } else {
                    CExpr::Var(core_var(name))
                }
            }

            ExprKind::RecordCreate { name, fields, .. } => {
                let order = self.record_fields.get(name).cloned().unwrap_or_default();
                let field_map: HashMap<&str, &Expr> =
                    fields.iter().map(|(n, _, e)| (n.as_str(), e)).collect();
                let mut vars: Vec<String> = Vec::new();
                let mut bindings: Vec<(String, CExpr)> = Vec::new();
                for field_name in &order {
                    let v = self.fresh();
                    let e = field_map
                        .get(field_name.as_str())
                        .expect("field missing in RecordCreate");
                    let ce = self.lower_expr(e);
                    vars.push(v.clone());
                    bindings.push((v, ce));
                }
                let atom = util::mangle_ctor_atom(name, &self.constructor_atoms);
                let mut elems = vec![CExpr::Lit(CLit::Atom(atom))];
                elems.extend(vars.iter().map(|v| CExpr::Var(v.clone())));
                let tuple = CExpr::Tuple(elems);
                bindings.into_iter().rev().fold(tuple, |body, (var, val)| {
                    CExpr::Let(var, Box::new(val), Box::new(body))
                })
            }

            ExprKind::AnonRecordCreate { fields, .. } => {
                let mut sorted_names: Vec<String> =
                    fields.iter().map(|(n, _, _)| n.clone()).collect();
                sorted_names.sort();
                let tag = format!("__anon_{}", sorted_names.join("_"));
                let field_map: HashMap<&str, &Expr> =
                    fields.iter().map(|(n, _, e)| (n.as_str(), e)).collect();
                let mut vars: Vec<String> = Vec::new();
                let mut bindings: Vec<(String, CExpr)> = Vec::new();
                for field_name in &sorted_names {
                    let v = self.fresh();
                    let e = field_map
                        .get(field_name.as_str())
                        .expect("field missing in AnonRecordCreate");
                    let ce = self.lower_expr(e);
                    vars.push(v.clone());
                    bindings.push((v, ce));
                }
                let mut elems = vec![CExpr::Lit(CLit::Atom(tag))];
                elems.extend(vars.iter().map(|v| CExpr::Var(v.clone())));
                let tuple = CExpr::Tuple(elems);
                bindings.into_iter().rev().fold(tuple, |body, (var, val)| {
                    CExpr::Let(var, Box::new(val), Box::new(body))
                })
            }

            ExprKind::FieldAccess { expr, field, .. } => {
                let record_name =
                    field_access_record_name(expr).or_else(|| self.find_record_by_field(field));
                let idx = record_name
                    .and_then(|rname| self.record_fields.get(rname))
                    .and_then(|fields| fields.iter().position(|f| f == field))
                    .map(|pos| pos + 2) // +1 for tag, +1 for 1-based
                    .unwrap_or(2) as i64;
                let v = self.fresh();
                let ce = self.lower_expr(expr);
                CExpr::Let(
                    v.clone(),
                    Box::new(ce),
                    Box::new(cerl_call(
                        "erlang",
                        "element",
                        vec![CExpr::Lit(CLit::Int(idx)), CExpr::Var(v)],
                    )),
                )
            }

            ExprKind::RecordUpdate { record, fields, .. } => {
                let rec_var = self.fresh();
                let rec_ce = self.lower_expr(record);
                let update_field_names: Vec<String> =
                    fields.iter().map(|(n, _, _)| n.clone()).collect();
                let record_name = field_access_record_name(record)
                    .or_else(|| self.find_record_by_fields(&update_field_names));
                let order = record_name
                    .and_then(|rname| self.record_fields.get(rname))
                    .cloned()
                    .unwrap_or_default();
                let field_map: HashMap<&str, &Expr> =
                    fields.iter().map(|(n, _, e)| (n.as_str(), e)).collect();

                let mut vars: Vec<String> = Vec::new();
                let mut bindings: Vec<(String, CExpr)> = Vec::new();
                for (pos, field_name) in order.iter().enumerate() {
                    let v = self.fresh();
                    let ce = if let Some(new_expr) = field_map.get(field_name.as_str()) {
                        self.lower_expr(new_expr)
                    } else {
                        let idx = (pos + 2) as i64;
                        cerl_call(
                            "erlang",
                            "element",
                            vec![CExpr::Lit(CLit::Int(idx)), CExpr::Var(rec_var.clone())],
                        )
                    };
                    vars.push(v.clone());
                    bindings.push((v, ce));
                }
                // Preserve the tag via element(1, rec)
                let tag_var = self.fresh();
                let tag_ce = cerl_call(
                    "erlang",
                    "element",
                    vec![CExpr::Lit(CLit::Int(1)), CExpr::Var(rec_var.clone())],
                );
                let mut elems = vec![CExpr::Var(tag_var.clone())];
                elems.extend(vars.iter().map(|v| CExpr::Var(v.clone())));
                let tuple = CExpr::Tuple(elems);
                let inner = bindings.into_iter().rev().fold(tuple, |body, (var, val)| {
                    CExpr::Let(var, Box::new(val), Box::new(body))
                });
                let with_tag = CExpr::Let(tag_var, Box::new(tag_ce), Box::new(inner));
                CExpr::Let(rec_var, Box::new(rec_ce), Box::new(with_tag))
            }

            ExprKind::Do {
                bindings,
                success,
                else_arms,
                ..
            } => {
                let else_arms: Vec<_> = else_arms.iter().map(|a| a.node.clone()).collect();
                self.lower_do(bindings, success, &else_arms)
            }

            // --- Elaboration-only constructs ---
            ExprKind::DictMethodAccess {
                dict, method_index, ..
            } => {
                // Lower to: let D = <dict> in element(idx+1, D)
                let dict_var = self.fresh();
                let dict_ce = self.lower_expr(dict);
                let extract_method = cerl_call(
                    "erlang",
                    "element",
                    vec![
                        CExpr::Lit(CLit::Int(*method_index as i64 + 1)),
                        CExpr::Var(dict_var.clone()),
                    ],
                );
                CExpr::Let(dict_var, Box::new(dict_ce), Box::new(extract_method))
            }

            ExprKind::ForeignCall {
                module, func, args, ..
            } => {
                let mut vars = Vec::new();
                let mut bindings = Vec::new();
                for arg in args {
                    let v = self.fresh();
                    let ce = self.lower_expr(arg);
                    vars.push(v.clone());
                    bindings.push((v, ce));
                }
                // erlang:monitor/1 -> erlang:monitor/2 with 'process' atom
                let call = if module == "erlang" && func == "monitor" && vars.len() == 1 {
                    CExpr::Call(
                        module.clone(),
                        func.clone(),
                        vec![
                            CExpr::Lit(CLit::Atom("process".into())),
                            CExpr::Var(vars[0].clone()),
                        ],
                    )
                // float_to_list/1 -> float_to_list/2 with [short] option
                } else if module == "erlang" && func == "float_to_list" && vars.len() == 1 {
                    let opts = CExpr::Cons(
                        Box::new(CExpr::Lit(CLit::Atom("short".into()))),
                        Box::new(CExpr::Nil),
                    );
                    CExpr::Call(
                        module.clone(),
                        func.clone(),
                        vec![CExpr::Var(vars[0].clone()), opts],
                    )
                } else {
                    CExpr::Call(
                        module.clone(),
                        func.clone(),
                        vars.iter().map(|v| CExpr::Var(v.clone())).collect(),
                    )
                };
                bindings.into_iter().rev().fold(call, |body, (var, val)| {
                    CExpr::Let(var, Box::new(val), Box::new(body))
                })
            }

            ExprKind::DictRef { name, .. } => {
                use super::resolve::ResolvedName;
                match self.resolved.get(&expr.id) {
                    Some(ResolvedName::ImportedFun {
                        erlang_mod,
                        name: erl_name,
                        arity,
                        ..
                    }) => {
                        if *arity == 0 {
                            CExpr::Call(erlang_mod.clone(), erl_name.clone(), vec![])
                        } else {
                            CExpr::Call(
                                "erlang".to_string(),
                                "make_fun".to_string(),
                                vec![
                                    CExpr::Lit(CLit::Atom(erlang_mod.clone())),
                                    CExpr::Lit(CLit::Atom(erl_name.clone())),
                                    CExpr::Lit(CLit::Int(*arity as i64)),
                                ],
                            )
                        }
                    }
                    _ => {
                        if let Some(arity) = self.fun_arity(name) {
                            if arity == 0 {
                                CExpr::Apply(Box::new(CExpr::FunRef(name.clone(), 0)), vec![])
                            } else {
                                CExpr::FunRef(name.clone(), arity)
                            }
                        } else {
                            // Dict param variable (passed as function argument)
                            CExpr::Var(core_var(name))
                        }
                    }
                }
            }

            // --- Effect system (CPS transform) ---

            // `log! "hello"` -- standalone effect call (not in a block).
            // When an effect call appears as a bare expression (not in a block where
            // we can capture the continuation), we call the handler with an identity
            // continuation that just returns the value.
            ExprKind::EffectCall {
                name,
                qualifier,
                args,
                ..
            } => self.lower_effect_call(name, qualifier.as_deref(), args, None),

            // `expr with handler` -- attaches handler(s) to a computation
            ExprKind::With { expr, handler, .. } => self.lower_with(expr, handler),

            // `resume value` -- inside a handler arm, calls the continuation K.
            // When a `finally` block is active, the K call is wrapped in try/catch
            // so cleanup runs after K completes or panics. The cleanup is lowered
            // once into a lambda (at the resume site, where arm body variables are
            // in scope) and called in both the ok and catch branches.
            ExprKind::Resume { value, .. } => {
                let k_name = self
                    .current_handler_k
                    .clone()
                    .expect("resume used outside handler");
                let v = self.fresh();
                let ce = self.lower_expr(value);
                let k_call =
                    CExpr::Apply(Box::new(CExpr::Var(k_name)), vec![CExpr::Var(v.clone())]);
                let k_or_wrapped = if let Some(ref finally_expr) =
                    self.current_handler_finally.clone()
                {
                    // let Cleanup = fun() -> finally_body in
                    // try apply K(V)
                    // of OkVar -> let _ = apply Cleanup() in OkVar
                    // catch <C, R, T> -> let _ = apply Cleanup() in raise(C, R, T)
                    let cleanup_var = self.fresh();
                    let cleanup_body = self.lower_expr(finally_expr);
                    let cleanup_lambda = CExpr::Fun(vec![], Box::new(cleanup_body));
                    let cleanup_call_ok =
                        CExpr::Apply(Box::new(CExpr::Var(cleanup_var.clone())), vec![]);
                    let cleanup_call_catch =
                        CExpr::Apply(Box::new(CExpr::Var(cleanup_var.clone())), vec![]);
                    let ok_var = self.fresh();
                    let class_var = self.fresh();
                    let reason_var = self.fresh();
                    let trace_var = self.fresh();
                    CExpr::Let(
                        cleanup_var,
                        Box::new(cleanup_lambda),
                        Box::new(CExpr::Try {
                            expr: Box::new(k_call),
                            ok_var: ok_var.clone(),
                            ok_body: Box::new(CExpr::Let(
                                "_".to_string(),
                                Box::new(cleanup_call_ok),
                                Box::new(CExpr::Var(ok_var)),
                            )),
                            catch_vars: (class_var.clone(), reason_var.clone(), trace_var.clone()),
                            catch_body: Box::new(CExpr::Let(
                                "_".to_string(),
                                Box::new(cleanup_call_catch),
                                Box::new(CExpr::Call(
                                    "erlang".to_string(),
                                    "raise".to_string(),
                                    vec![
                                        CExpr::Var(class_var),
                                        CExpr::Var(reason_var),
                                        CExpr::Var(trace_var),
                                    ],
                                )),
                            )),
                        }),
                    )
                } else {
                    k_call
                };
                CExpr::Let(v, Box::new(ce), Box::new(k_or_wrapped))
            }

            // Handler expression as a value (e.g. returned from a function).
            // Produce a tuple of per-op handler lambdas for runtime use.
            ExprKind::HandlerExpr { body } => self.lower_handler_expr_to_tuple(body),

            ExprKind::BitString { segments } => self.lower_bitstring_expr(segments),

            // StringInterpolation should be desugared before reaching the lowerer,
            // but keep a fallback just in case.
            #[allow(unreachable_patterns)]
            other => CExpr::Lit(CLit::Atom(format!(
                "todo_{:?}",
                std::mem::discriminant(other)
            ))),
        }
    }

    /// Lower a qualified function call like `Math.abs x` to `call 'math':'abs'(X)`.
    /// For effectful imported functions, handler params and _ReturnK are threaded.
    fn lower_qualified_call(
        &mut self,
        module: &str,
        func_name: &str,
        head: &Expr,
        args: &[&Expr],
        call_span: Option<&crate::token::Span>,
    ) -> CExpr {
        let erlang_module = self
            .module_aliases
            .get(module)
            .cloned()
            .unwrap_or_else(|| module.to_lowercase());

        let qualified = format!("{}.{}", module, func_name);
        let callee_effects = self.resolved_effects(head.id, &qualified);
        let callee_ops = callee_effects
            .as_ref()
            .map(|effs| self.effect_handler_ops(effs))
            .unwrap_or_default();

        // Filter out unit literal args
        let non_unit_args: Vec<&&Expr> = args
            .iter()
            .filter(|a| {
                !matches!(
                    a.kind,
                    ExprKind::Lit {
                        value: ast::Lit::Unit,
                        ..
                    }
                )
            })
            .collect();

        let mut arg_vars: Vec<String> = Vec::new();
        let mut bindings: Vec<(String, CExpr)> = Vec::new();

        let callee_param_effs = self.param_absorbed_effects(&qualified).cloned();
        for (i, arg) in non_unit_args.iter().enumerate() {
            let v = self.fresh();
            // If this arg position has absorbed effects, set context
            // so lambdas at this position get handler params added.
            let saved_ctx = self.lambda_effect_context.take();
            if let Some(ref pe) = callee_param_effs
                && let Some(effs) = pe.get(&i)
            {
                self.lambda_effect_context = Some(effs.clone());
            }
            let ce = self.lower_expr(arg);
            self.lambda_effect_context = saved_ctx;
            arg_vars.push(v.clone());
            bindings.push((v, ce));
        }

        // Append per-op handler params for effectful callees
        if !callee_ops.is_empty() {
            for (eff, op) in &callee_ops {
                let key = format!("{}.{}", eff, op);
                if let Some(param) = self.current_handler_params.get(&key) {
                    arg_vars.push(param.clone());
                } else {
                    panic!(
                        "qualified call '{}.{}' needs handler for '{}.{}' but no handler param in scope",
                        module, func_name, eff, op
                    );
                }
            }
            // Pass _ReturnK
            let return_k = self.pending_callee_return_k.take().unwrap_or_else(|| {
                let p = self.fresh();
                CExpr::Fun(vec![p.clone()], Box::new(CExpr::Var(p)))
            });
            let rk_var = self.fresh();
            bindings.push((rk_var.clone(), return_k));
            arg_vars.push(rk_var);
        }

        let call_args: Vec<CExpr> = arg_vars.iter().map(|v| CExpr::Var(v.clone())).collect();
        use super::resolve::ResolvedName;
        let call = match self.resolved.get(&head.id) {
            Some(ResolvedName::ExternalFun {
                erlang_mod,
                erlang_func,
                ..
            }) => CExpr::Call(erlang_mod.clone(), erlang_func.clone(), call_args),
            Some(ResolvedName::ImportedFun {
                erlang_mod, name, ..
            }) => CExpr::Call(erlang_mod.clone(), name.clone(), call_args),
            _ => CExpr::Call(erlang_module, func_name.to_string(), call_args),
        };
        let call = self.annotate(call, call_span);

        bindings.into_iter().rev().fold(call, |body, (var, val)| {
            CExpr::Let(var, Box::new(val), Box::new(body))
        })
    }
}
