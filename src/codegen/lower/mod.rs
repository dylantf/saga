pub(crate) mod beam_interop;
mod builtins;
mod effects;
pub mod errors;
mod evidence;
mod exprs;
pub(crate) mod init;
mod pats;
pub mod util;

use crate::ast::{self, Decl, Expr, ExprKind, HandlerArm, Lit, NodeId, Pat, Stmt};
use crate::codegen::cerl::{CArm, CExpr, CFunDef, CLit, CModule, CPat};
use std::collections::HashMap;

use errors::{ErrorInfo, ErrorKind, SourceInfo};
use init::{PendingAnnotation, extract_external};
use pats::lower_params;
use util::{
    cerl_call, collect_ctor_call, collect_effect_call, collect_effect_call_expr, collect_fun_call,
    collect_qualified_call, core_var, lower_lit, lower_string_to_binary, process_string_escapes,
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

/// Bundled inputs to `Lowerer::lower_qualified_call`, gathered to keep its
/// signature manageable. All borrows tie back to the same lowering invocation.
pub(super) struct QualifiedCallSite<'a> {
    pub app_id: NodeId,
    pub module: &'a str,
    pub func_name: &'a str,
    pub head: &'a Expr,
    pub args: &'a [&'a Expr],
    pub return_k: Option<CExpr>,
    pub call_span: Option<&'a crate::token::Span>,
}

fn count_lambda_params(body: &Expr) -> usize {
    match &body.kind {
        ExprKind::Lambda { params, body, .. } => params.len() + count_lambda_params(body),
        _ => 0,
    }
}

fn is_unit_type_expr(ty: &ast::TypeExpr) -> bool {
    match ty {
        ast::TypeExpr::Named { name, .. } => {
            crate::typechecker::canonicalize_type_name(name)
                == crate::typechecker::canonicalize_type_name("Unit")
        }
        ast::TypeExpr::Labeled { inner, .. } => is_unit_type_expr(inner),
        _ => false,
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

/// Stored effect definition: maps op_name -> lowering metadata.
struct EffectInfo {
    ops: HashMap<String, EffectOpInfo>,
}

#[derive(Debug, Clone, Default)]
struct EffectOpInfo {
    /// Source-level parameter count before erasing `Unit` placeholders.
    source_param_count: usize,
    /// Runtime parameter count after erasing `Unit` placeholders.
    runtime_param_count: usize,
    /// Indices of source params that survive runtime erasure.
    runtime_param_positions: Vec<usize>,
    /// For callback parameters, the effects absorbed by that parameter.
    param_absorbed_effects: HashMap<usize, Vec<String>>,
}

/// CPS metadata for a top-level function. Used by the lowerer to determine
/// how to thread evidence and return continuations through effectful calls.
/// This is NOT name resolution -- name resolution is handled by the
/// ResolutionMap. FunInfo only tracks arity/effects needed for CPS
/// transformation.
#[derive(Debug, Clone, Default)]
struct FunInfo {
    /// Exported arity: `user_arity + 2` (`_Evidence` + `_ReturnK`) when
    /// effectful, `user_arity` when pure. 0 if not yet known.
    arity: usize,
    /// Effect names from `needs` clause (sorted). Used to derive the evidence
    /// layout the callee expects.
    effects: Vec<String>,
    /// True when the callee's declared effect row has an open tail
    /// (`needs {Foo, ..e}`). Call-site lowering uses this to choose
    /// `RowForwarded` (forward full evidence) vs `StaticOps` (project the
    /// caller's evidence). Mirrors `util::has_open_effect_row` on the
    /// declared/inferred type.
    is_open_row: bool,
    /// For EffArrow params: param_index -> absorbed effects. Used to inject
    /// evidence threading into lambdas passed to effectful higher-order
    /// functions.
    param_absorbed_effects: HashMap<usize, Vec<String>>,
    /// Source-level parameter types from the declared/inferred function type.
    /// Used to propagate expected callback shapes through containers at call sites
    /// without depending on fully specialized row-polymorphic instantiations.
    param_types: Vec<crate::typechecker::Type>,
}

/// Tracks the evidence vector currently in scope during lowering.
///
/// An `_Evidence` parameter is threaded into every effectful function
/// definition and at every effectful call site, paired with a trailing
/// `_ReturnK` for the success continuation. Op-call emission reads handler
/// closures out of this context via `evidence_op_lookup`.
#[derive(Debug, Clone)]
#[allow(dead_code, private_interfaces)]
pub(super) struct EvidenceCtx {
    /// Core Erlang variable name holding the evidence tuple in scope.
    pub(super) var: String,
    /// Statically-known canonical effect tags in the evidence vector. Sorted.
    pub(super) layout: evidence::EvidenceLayout,
    /// True when the evidence has an open tail (additional effects may be
    /// present at runtime beyond `layout`). Closed-row narrowing only
    /// projects when `is_open` is false.
    pub(super) is_open: bool,
}

/// Explicit lowering context for value-producing vs terminal positions.
#[derive(Clone)]
pub(super) enum LowerMode {
    /// Lower as a value-producing subexpression.
    Value,
    /// Lower as a terminal computation whose successful result should flow to K.
    Tail(CExpr),
}

pub struct Lowerer<'a> {
    counter: usize,
    /// Cross-module codegen context (compiled modules, effect bindings, prelude imports).
    ctx: &'a super::CodegenContext,
    /// Source location info for error terms. None for stdlib modules (no user source).
    source_info: Option<SourceInfo>,
    /// Current Erlang module name being emitted (e.g. "my_app_server").
    current_module: String,
    /// Current Saga source module name (e.g. "MyApp.Server").
    current_source_module: String,
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
    /// Evidence context for the currently-lowered effectful scope. `None` in
    /// pure code. Set by the function-entry plumbing for effectful functions
    /// (var = `_Evidence`) and refreshed at `with` boundaries (var = a fresh
    /// name bound to the inserted-canonical extension). Op-call emission
    /// reads handler closures out of this evidence vector via
    /// `evidence_op_lookup`.
    current_evidence: Option<EvidenceCtx>,
    /// Set of "effect.op" keys whose current handler arm never calls resume.
    /// Used to pass a cheap atom instead of a real continuation closure at the call site,
    /// avoiding the Erlang "a term is constructed but never used" warning.
    no_resume_ops: std::collections::HashSet<String>,
    /// Maps "effect.op" -> handler canonical name for ops that are guaranteed to
    /// resume exactly once with the result value. These ops can be inlined as direct
    /// `let` bindings instead of going through CPS continuation-passing, avoiding
    /// closure allocation. Currently all BEAM-native ops satisfy this property.
    direct_ops: HashMap<String, String>,
    /// Effects that the next lambda being lowered should accept as extra params.
    /// Set by the call site that passes the lambda to an effectful parameter.
    lambda_effect_context: Option<Vec<String>>,
    /// Variable name for the continuation parameter in the current handler function.
    /// Set by `build_handler_fun`, read by `Expr::Resume`.
    current_handler_k: Option<String>,
    /// When lowering a handler arm with `finally`, this holds the finally block AST.
    /// At each `resume` site, the cleanup code is lowered inline (wrapped in try/catch
    /// around the K call) so it can capture variables from the arm body's lexical scope.
    current_handler_finally: Option<crate::ast::Expr>,
    /// When inlining a named handler from another module, local function references
    /// inside that handler body should lower against the source module, not the
    /// current module being emitted.
    current_handler_source_module: Option<String>,
    /// Pre-resolved constructor name -> mangled Erlang atom.
    /// e.g. "NotFound" -> "std_file_NotFound", "Ok" -> "ok".
    /// Built by resolve::build_constructor_atoms before lowering.
    constructor_atoms: super::resolve::ConstructorAtoms,
    /// Pre-resolved name resolution map: NodeId -> ResolvedName.
    /// Built by resolve::resolve_names before lowering.
    resolved: super::resolve::ResolutionMap,
    /// Pre-resolved compiler intrinsics keyed by source node.
    intrinsics: super::resolve::IntrinsicMap,
    /// @inline val name -> lowered expression. Substituted at reference sites.
    inline_vals: HashMap<String, CExpr>,
    /// Bare handler name -> canonical handler name (e.g. "collect_handler" -> "Std.Test.collect_handler").
    /// Built during init_module for resolving handler references in `with` expressions.
    handler_canonical: HashMap<String, String>,
    /// Bare effect name -> canonical effect name (e.g. "Test" -> "Std.Test.Test").
    /// Built during init_module for canonicalizing effect names from the type system.
    effect_canonical: HashMap<String, String>,
    /// Typechecker result for the module currently being lowered.
    /// Provides resolved types, handler info, effect info, etc.
    check_result: crate::typechecker::CheckResult,
    /// Conditional handle bindings: name -> (cond_var, cond_expr, then_canonical, else_canonical).
    /// Used during lower_with to generate conditional handler dispatch.
    handle_cond_vars: HashMap<String, (String, CExpr, String, String)>,
    /// Dynamic handle bindings: name -> (lowered_var, canonical_effect_names, has_return_clause).
    /// For `handle name = some_function_call()` where the handler isn't statically
    /// resolvable, the RHS is lowered to a tuple-of-lambdas and bound to a variable.
    /// At `with` sites, the tuple is destructured to extract per-op handler functions.
    handle_dynamic_vars: HashMap<String, (String, Vec<String>, bool)>,
    /// Optional function name that should be exported even if it is not `pub`.
    /// Used by the build pipeline to mark the chosen entrypoint explicitly.
    entry_export: Option<String>,
    /// Per-call effect metadata for every `App` node in the module being
    /// lowered. Populated by the call-effects pre-pass after `init_module`,
    /// then consumed at every effectful call site to drive evidence threading.
    call_effects: super::call_effects::CallEffectMap,
    /// Trait impl dict name -> sorted canonical effect names from the impl's
    /// `needs` clause. Populated during `lower_module` from the active and
    /// imported modules' `TraitImplDict.impl_effects`. Read by (1) the
    /// call-effects pre-pass for `DictMethodAccess` classification, and (2)
    /// dict-constructor emission, where each method body is compiled as
    /// effectful (params `_Evidence`/`_ReturnK`, evidence context installed)
    /// when its impl declares `needs`.
    impl_effects_by_dict: HashMap<String, Vec<String>>,
}

impl<'a> Lowerer<'a> {
    pub fn new(
        ctx: &'a super::CodegenContext,
        constructor_atoms: super::resolve::ConstructorAtoms,
        resolved: super::resolve::ResolutionMap,
        intrinsics: super::resolve::IntrinsicMap,
        check_result: &crate::typechecker::CheckResult,
        source_info: Option<SourceInfo>,
        entry_export: Option<String>,
    ) -> Self {
        Lowerer {
            counter: 0,
            ctx,
            source_info,
            current_module: String::new(),
            current_source_module: String::new(),
            current_function: String::new(),
            module_aliases: HashMap::new(),
            pub_names: std::collections::HashSet::new(),
            record_fields: HashMap::new(),
            fun_info: HashMap::new(),
            effect_defs: HashMap::new(),
            handler_defs: HashMap::new(),
            current_evidence: None,
            no_resume_ops: std::collections::HashSet::new(),
            direct_ops: HashMap::new(),
            lambda_effect_context: None,
            constructor_atoms,
            resolved,
            intrinsics,
            current_handler_k: None,
            current_handler_finally: None,
            current_handler_source_module: None,
            inline_vals: HashMap::new(),
            handler_canonical: HashMap::new(),
            effect_canonical: HashMap::new(),
            check_result: check_result.clone(),
            handle_cond_vars: HashMap::new(),
            handle_dynamic_vars: HashMap::new(),
            entry_export,
            call_effects: super::call_effects::CallEffectMap::new(),
            impl_effects_by_dict: HashMap::new(),
        }
    }

    pub(super) fn fresh(&mut self) -> String {
        let n = self.counter;
        self.counter += 1;
        format!("_Cor{}", n)
    }

    fn module_name_to_erlang(module_name: &str) -> String {
        module_name
            .split('.')
            .map(|s| s.to_lowercase())
            .collect::<Vec<_>>()
            .join("_")
    }

    fn imported_handler_external_target(
        &self,
        source_module: &str,
        name: &str,
        arity: usize,
    ) -> Option<(String, String)> {
        self.ctx
            .module_semantics(source_module)
            .and_then(|module_semantics| {
                module_semantics
                    .codegen_info
                    .external_funs
                    .iter()
                    .find(|(fun_name, _, _, fun_arity)| fun_name == name && *fun_arity == arity)
                    .map(|(_, erl_mod, erl_fun, _)| (erl_mod.clone(), erl_fun.clone()))
            })
    }

    fn resolved_fun_info(&self, node_id: crate::ast::NodeId, fallback: &str) -> Option<&FunInfo> {
        use super::resolve::ResolvedName;
        match self.resolved.get(&node_id) {
            // Local calls should use the current module's fully populated entry.
            // A canonical entry can also exist from module metadata and may not
            // include CPS-expanded handler/return parameters.
            Some(ResolvedName::LocalFun { canonical_name, .. }) => self
                .fun_info
                .get(fallback)
                .or_else(|| self.fun_info.get(canonical_name)),
            Some(ResolvedName::ImportedFun { canonical_name, .. }) => self
                .fun_info
                .get(canonical_name)
                .or_else(|| self.fun_info.get(fallback)),
            None => None,
        }
    }

    fn substitute_type_vars(
        ty: &crate::typechecker::Type,
        subst: &HashMap<u32, crate::typechecker::Type>,
    ) -> crate::typechecker::Type {
        use crate::typechecker::{EffectEntry, EffectRow, Type};

        match ty {
            Type::Var(id) => subst.get(id).cloned().unwrap_or(Type::Var(*id)),
            Type::Fun(param, ret, row) => Type::Fun(
                Box::new(Self::substitute_type_vars(param, subst)),
                Box::new(Self::substitute_type_vars(ret, subst)),
                EffectRow {
                    effects: row
                        .effects
                        .iter()
                        .map(|entry| EffectEntry {
                            name: entry.name.clone(),
                            args: entry
                                .args
                                .iter()
                                .map(|arg| Self::substitute_type_vars(arg, subst))
                                .collect(),
                        })
                        .collect(),
                    tail: row
                        .tail
                        .as_ref()
                        .map(|tail| Box::new(Self::substitute_type_vars(tail, subst))),
                },
            ),
            Type::Con(name, args) => Type::Con(
                name.clone(),
                args.iter()
                    .map(|arg| Self::substitute_type_vars(arg, subst))
                    .collect(),
            ),
            Type::Record(fields) => Type::Record(
                fields
                    .iter()
                    .map(|(name, ty)| (name.clone(), Self::substitute_type_vars(ty, subst)))
                    .collect(),
            ),
            Type::Error => Type::Error,
        }
    }

    fn bind_type_vars_from_match(
        actual: &crate::typechecker::Type,
        pattern: &crate::typechecker::Type,
        subst: &mut HashMap<u32, crate::typechecker::Type>,
    ) {
        use crate::typechecker::Type;

        match (actual, pattern) {
            (_, Type::Var(id)) => {
                subst.entry(*id).or_insert_with(|| actual.clone());
            }
            (Type::Fun(a1, b1, _), Type::Fun(a2, b2, _)) => {
                Self::bind_type_vars_from_match(a1, a2, subst);
                Self::bind_type_vars_from_match(b1, b2, subst);
            }
            (Type::Con(n1, xs1), Type::Con(n2, xs2)) if n1 == n2 && xs1.len() == xs2.len() => {
                for (x1, x2) in xs1.iter().zip(xs2.iter()) {
                    Self::bind_type_vars_from_match(x1, x2, subst);
                }
            }
            (Type::Record(fs1), Type::Record(fs2)) if fs1.len() == fs2.len() => {
                for ((n1, t1), (n2, t2)) in fs1.iter().zip(fs2.iter()) {
                    if n1 == n2 {
                        Self::bind_type_vars_from_match(t1, t2, subst);
                    }
                }
            }
            _ => {}
        }
    }

    fn record_field_types_from_expected(
        &self,
        expected_ty: &crate::typechecker::Type,
    ) -> Option<HashMap<String, crate::typechecker::Type>> {
        use crate::typechecker::Type;

        match expected_ty {
            Type::Record(fields) => Some(fields.iter().cloned().collect()),
            Type::Con(name, args) => {
                let info = self.check_result.records.get(name).or_else(|| {
                    self.check_result
                        .records
                        .get(crate::typechecker::bare_type_name(name))
                })?;
                let mut subst = HashMap::new();
                for (param_id, arg_ty) in info.type_params.iter().zip(args.iter()) {
                    subst.insert(*param_id, arg_ty.clone());
                }
                Some(
                    info.fields
                        .iter()
                        .map(|(field, ty)| (field.clone(), Self::substitute_type_vars(ty, &subst)))
                        .collect(),
                )
            }
            _ => None,
        }
    }

    fn constructor_arg_types_from_expected(
        &self,
        ctor_name: &str,
        expected_ty: &crate::typechecker::Type,
    ) -> Option<Vec<crate::typechecker::Type>> {
        if matches!(
            expected_ty,
            crate::typechecker::Type::Var(_) | crate::typechecker::Type::Error
        ) {
            return None;
        }
        let scheme = self.check_result.constructors.get(ctor_name).or_else(|| {
            let bare = ctor_name.rsplit('.').next().unwrap_or(ctor_name);
            self.check_result.constructors.get(bare)
        })?;
        let mut param_tys = Vec::new();
        let mut current = &scheme.ty;
        while let crate::typechecker::Type::Fun(param, ret, _) = current {
            param_tys.push((**param).clone());
            current = ret;
        }
        let mut subst = HashMap::new();
        Self::bind_type_vars_from_match(expected_ty, current, &mut subst);
        Some(
            param_tys
                .into_iter()
                .map(|ty| Self::substitute_type_vars(&ty, &subst))
                .collect(),
        )
    }

    fn current_semantic_module_name(&self) -> &str {
        self.current_handler_source_module
            .as_deref()
            .unwrap_or(&self.current_source_module)
    }

    /// When lowering code from an imported handler, returns the handler's
    /// source module so constructor atoms and patterns resolve against the
    /// correct module. Returns `None` when lowering the current module's
    /// own code (the common case).
    pub(super) fn handler_origin_module(&self) -> Option<&str> {
        self.current_handler_source_module
            .as_deref()
            .filter(|m| *m != self.current_source_module)
    }

    /// Check whether a name refers to a known constructor, accounting for
    /// the current handler origin module if lowering imported handler code.
    fn is_known_constructor(&self, name: &str) -> bool {
        if self.constructor_atoms.contains_key(name) {
            return true;
        }
        if let Some(origin) = self.handler_origin_module() {
            let qualified = format!("{}.{}", origin, name);
            return self.constructor_atoms.contains_key(&qualified);
        }
        false
    }

    fn front_resolution_for_module(
        &self,
        module_name: &str,
    ) -> Option<&crate::typechecker::ResolutionResult> {
        self.check_result
            .module_check_results()
            .get(module_name)
            .map(|m| &m.resolution)
            .or_else(|| {
                (module_name == self.current_source_module).then_some(&self.check_result.resolution)
            })
            .or_else(|| {
                self.ctx
                    .module_semantics(module_name)
                    .map(|m| m.front_resolution)
            })
    }

    fn current_value_ref(
        &self,
        node_id: crate::ast::NodeId,
    ) -> Option<&crate::typechecker::ResolvedValue> {
        self.front_resolution_for_module(self.current_semantic_module_name())
            .and_then(|r| r.value(node_id))
    }

    fn current_record_type_name(&self, node_id: crate::ast::NodeId) -> Option<&str> {
        self.front_resolution_for_module(self.current_semantic_module_name())
            .and_then(|r| r.record_type(node_id))
    }

    fn current_effect_call_effect(&self, node_id: crate::ast::NodeId) -> Option<&str> {
        self.front_resolution_for_module(self.current_semantic_module_name())
            .and_then(|r| r.effect_call(node_id))
            .map(|resolved| resolved.effect.as_str())
    }

    fn handler_arm_effect_for_module(
        &self,
        module_name: &str,
        node_id: crate::ast::NodeId,
    ) -> Option<&str> {
        self.front_resolution_for_module(module_name)
            .and_then(|r| r.handler_arm(node_id))
            .map(|resolved| resolved.effect.as_str())
    }

    fn resolved_effect_ref_for_module(
        &self,
        module_name: &str,
        effect_ref: &crate::ast::EffectRef,
    ) -> String {
        self.front_resolution_for_module(module_name)
            .and_then(|r| r.effect_ref(effect_ref.id))
            .map(|resolved| {
                self.effect_canonical
                    .get(resolved)
                    .cloned()
                    .unwrap_or_else(|| resolved.to_string())
            })
            .unwrap_or_else(|| {
                self.effect_canonical
                    .get(&effect_ref.name)
                    .cloned()
                    .unwrap_or_else(|| effect_ref.name.clone())
            })
    }

    fn resolved_effect_refs_for_module(
        &self,
        module_name: &str,
        effect_refs: &[crate::ast::EffectRef],
    ) -> Vec<String> {
        effect_refs
            .iter()
            .map(|effect_ref| self.resolved_effect_ref_for_module(module_name, effect_ref))
            .collect()
    }

    fn canonical_effect_lookup(&self, effect_name: &str) -> String {
        self.effect_canonical
            .get(effect_name)
            .cloned()
            .unwrap_or_else(|| effect_name.to_string())
    }

    fn resolved_effect_call_name(
        &self,
        node_id: crate::ast::NodeId,
        _op_name: &str,
        _qualifier: Option<&str>,
    ) -> Option<String> {
        self.current_effect_call_effect(node_id)
            .map(|resolved| self.canonical_effect_lookup(resolved))
    }

    fn resolved_handler_binding_name(&self, node_id: crate::ast::NodeId) -> Option<String> {
        let normalize_lookup = |lookup_name: &str| {
            if self.handle_dynamic_vars.contains_key(lookup_name)
                || self.handle_cond_vars.contains_key(lookup_name)
                || self.handler_defs.contains_key(lookup_name)
            {
                lookup_name.to_string()
            } else {
                self.resolve_handler_name(lookup_name)
            }
        };
        self.front_resolution_for_module(self.current_semantic_module_name())
            .and_then(|r| r.handler_ref(node_id).or_else(|| r.value(node_id)))
            .map(|resolved| match resolved {
                crate::typechecker::ResolvedValue::Local { name, .. } => normalize_lookup(name),
                crate::typechecker::ResolvedValue::Global { lookup_name } => {
                    normalize_lookup(lookup_name)
                }
            })
    }

    fn known_handler_binding_name(
        &self,
        node_id: crate::ast::NodeId,
        _fallback: &str,
    ) -> Option<String> {
        let resolved = self.resolved_handler_binding_name(node_id)?;
        if self.handler_defs.contains_key(&resolved)
            || self.handle_dynamic_vars.contains_key(&resolved)
            || self.handle_cond_vars.contains_key(&resolved)
        {
            Some(resolved)
        } else {
            None
        }
    }

    fn resolved_env_lookup_name(&self, node_id: crate::ast::NodeId, fallback: &str) -> String {
        use super::resolve::ResolvedName;

        match self.resolved.get(&node_id) {
            Some(ResolvedName::LocalFun { name, .. }) => name.clone(),
            Some(ResolvedName::ImportedFun { canonical_name, .. }) => canonical_name.clone(),
            None => self
                .current_value_ref(node_id)
                .map(|resolved| match resolved {
                    crate::typechecker::ResolvedValue::Local { name, .. } => name.clone(),
                    crate::typechecker::ResolvedValue::Global { lookup_name } => {
                        lookup_name.clone()
                    }
                })
                .unwrap_or_else(|| fallback.to_string()),
        }
    }

    fn record_fields_for_name(&self, name: &str) -> Option<&Vec<String>> {
        self.record_fields.get(name)
    }

    pub(super) fn resolved_record_fields(
        &self,
        node_id: crate::ast::NodeId,
        source_name: &str,
    ) -> Option<&Vec<String>> {
        let module_name = self.current_semantic_module_name();
        self.current_record_type_name(node_id)
            .and_then(|name| self.record_fields_for_name(name))
            .or_else(|| self.record_fields_for_name(source_name))
            .or_else(|| {
                let local_name = format!("{}.{}", module_name, source_name);
                self.record_fields_for_name(&local_name)
            })
    }

    fn resolved_handler_arm_effect_for_module(
        &self,
        arm: &HandlerArm,
        module_name: &str,
    ) -> Option<String> {
        self.handler_arm_effect_for_module(module_name, arm.id)
            .map(|resolved| self.canonical_effect_lookup(resolved))
    }

    fn handler_arm_matches_effect_op_for_module(
        &self,
        arm: &HandlerArm,
        source_module: Option<&str>,
        eff: &str,
        op: &str,
    ) -> bool {
        let module_name = source_module.unwrap_or_else(|| self.current_semantic_module_name());
        self.resolved_handler_arm_effect_for_module(arm, module_name)
            .is_some_and(|resolved| resolved == eff && arm.op_name == op)
    }

    fn lower_local_fun_ref(
        &mut self,
        name: &str,
        arity: usize,
        effects: Option<Vec<String>>,
        source_module: Option<&str>,
    ) -> CExpr {
        if let Some(source_module) =
            source_module.filter(|source| *source != self.current_source_module)
        {
            let (erlang_mod, target_name) = self
                .imported_handler_external_target(source_module, name, arity)
                .unwrap_or_else(|| (Self::module_name_to_erlang(source_module), name.to_string()));
            if arity == 0 {
                return CExpr::Call(erlang_mod, target_name, vec![]);
            }
            if let Some(effects) = effects.as_ref()
                && !effects.is_empty()
            {
                // Effectful function value: raw-CPS calling convention.
                let expanded_arity = self.expanded_arity(arity, effects);
                return CExpr::Call(
                    "erlang".to_string(),
                    "make_fun".to_string(),
                    vec![
                        CExpr::Lit(CLit::Atom(erlang_mod)),
                        CExpr::Lit(CLit::Atom(target_name)),
                        CExpr::Lit(CLit::Int(expanded_arity as i64)),
                    ],
                );
            }
            return CExpr::Call(
                "erlang".to_string(),
                "make_fun".to_string(),
                vec![
                    CExpr::Lit(CLit::Atom(erlang_mod)),
                    CExpr::Lit(CLit::Atom(target_name)),
                    CExpr::Lit(CLit::Int(arity as i64)),
                ],
            );
        }

        if arity == 0 {
            if let Some(inlined) = self.inline_vals.get(name) {
                inlined.clone()
            } else {
                CExpr::Apply(Box::new(CExpr::FunRef(name.to_string(), 0)), vec![])
            }
        } else if effects.as_ref().is_some_and(|e| !e.is_empty()) {
            // Effectful function used as a value: emit a raw FunRef of the
            // CPS-expanded arity. The calling convention for effectful function
            // values is raw-CPS — call sites supply (user_args..., handlers...,
            // _ReturnK). An eta-wrapper that captures handlers and supplies an
            // identity continuation would be incompatible with HOFs whose body
            // calls the callback in raw-CPS shape (e.g. `decoder n` lowering to
            // `decoder(n, H, K)` in `Lib.at`).
            let lowered_arity = self.fun_arity(name).unwrap_or(arity);
            CExpr::FunRef(name.to_string(), lowered_arity)
        } else {
            let lowered_arity = self.fun_arity(name).unwrap_or(arity);
            CExpr::FunRef(name.to_string(), lowered_arity)
        }
    }

    fn lower_local_fun_call(
        &self,
        name: &str,
        arity: usize,
        call_args: Vec<CExpr>,
        source_module: Option<&str>,
    ) -> CExpr {
        if let Some(source_module) =
            source_module.filter(|source| *source != self.current_source_module)
        {
            let (erlang_mod, target_name) = self
                .imported_handler_external_target(source_module, name, arity)
                .unwrap_or_else(|| (Self::module_name_to_erlang(source_module), name.to_string()));
            CExpr::Call(erlang_mod, target_name, call_args)
        } else {
            CExpr::Apply(Box::new(CExpr::FunRef(name.to_string(), arity)), call_args)
        }
    }

    /// Build a structured error term and wrap it in `erlang:error(Term)`.
    /// Falls back to the old `{saga_panic, Msg}` tuple when no source info is available.
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
                module: self.current_source_module.clone(),
                function: self.current_function.clone(),
                file: si.file.clone(),
                line,
            }
            .to_cexpr()
        } else {
            // Stdlib modules don't have source info — use the old format
            CExpr::Tuple(vec![
                CExpr::Lit(CLit::Atom("saga_error".into())),
                CExpr::Lit(CLit::Atom(kind.as_atom().into())),
                message,
                lower_string_to_binary(&self.current_source_module),
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

    /// Generate a fresh scoped handler binding name for a specific effect op.
    /// Used for local `with` layers so nested handlers for the same op don't
    /// shadow each other and trigger backend "constructed but never used" warnings.
    pub(super) fn fresh_handler_binding_name(&mut self, effect: &str, op: &str) -> String {
        let suffix = self.counter;
        self.counter += 1;
        format!("{}__{}", Self::handler_param_name(effect, op), suffix)
    }

    /// Compute the expanded arity for a function with the given base arity
    /// and effect requirements. Effectful functions get `_Evidence` and
    /// `_ReturnK` appended (handler params no longer threaded under the
    /// evidence-passing convention).
    pub(super) fn expanded_arity(&self, base_arity: usize, effects: &[String]) -> usize {
        let op_count = self.effect_handler_ops(effects).len();
        base_arity + if op_count > 0 { 2 } else { 0 }
    }

    fn lower_eta_reduced_effect_op_ref(
        &mut self,
        node_id: crate::ast::NodeId,
        op_name: &str,
        qualifier: Option<&str>,
    ) -> Option<CExpr> {
        let effect_name = self.resolved_effect_call_name(node_id, op_name, qualifier)?;
        let _ = self.effect_defs.get(&effect_name)?.ops.get(op_name)?;
        let op_info = self
            .effect_defs
            .get(&effect_name)?
            .ops
            .get(op_name)?
            .clone();

        let mut params = Vec::new();
        let mut runtime_args = Vec::new();
        for idx in 0..op_info.source_param_count {
            let param = self.fresh();
            if op_info.runtime_param_positions.contains(&idx) {
                runtime_args.push(CExpr::Var(param.clone()));
            }
            params.push(param);
        }

        if self.lambda_effect_context.is_some() {
            // Raw CPS shape: the resulting closure is passed to a slot that
            // expects an effectful function value, so it takes `_Evidence`
            // and `_ReturnK` and reads the per-op handler out of the
            // evidence vector at call time.
            let evidence = "_Evidence".to_string();
            let return_k = "_ReturnK".to_string();
            runtime_args.push(CExpr::Var(return_k.clone()));
            params.push(evidence.clone());
            params.push(return_k);
            // Build the op lookup against the lambda's evidence parameter.
            let saved_evidence = self.current_evidence.clone();
            self.current_evidence = Some(EvidenceCtx {
                var: evidence,
                layout: evidence::EvidenceLayout::new([effect_name.clone()]),
                is_open: true,
            });
            let handler_expr = self.evidence_op_lookup(&effect_name, op_name);
            self.current_evidence = saved_evidence;
            Some(CExpr::Fun(
                params,
                Box::new(CExpr::Apply(Box::new(handler_expr), runtime_args)),
            ))
        } else {
            // Value-closure shape: the resulting lambda is bound locally or
            // passed to a pure-shaped callback slot. Capture the in-scope
            // op closure (read out of current evidence) and provide an
            // identity return continuation.
            let handler_expr = self.evidence_op_lookup(&effect_name, op_name);
            let return_value = self.fresh();
            runtime_args.push(CExpr::Fun(
                vec![return_value.clone()],
                Box::new(CExpr::Var(return_value)),
            ));
            Some(CExpr::Fun(
                params,
                Box::new(CExpr::Apply(Box::new(handler_expr), runtime_args)),
            ))
        }
    }

    fn lower_eta_reduced_effect_expr(&mut self, expr: &Expr) -> Option<CExpr> {
        let mut args = Vec::new();
        let mut current = expr;
        let (effect_call_id, op_name, qualifier) = loop {
            match &current.kind {
                ExprKind::App { func, arg, .. } => {
                    args.push(arg.as_ref());
                    current = func.as_ref();
                }
                ExprKind::EffectCall {
                    name, qualifier, ..
                } => {
                    args.reverse();
                    break (current.id, name.as_str(), qualifier.as_deref());
                }
                _ => return None,
            }
        };

        if !args.is_empty() {
            return None;
        }
        self.lower_eta_reduced_effect_op_ref(effect_call_id, op_name, qualifier)
    }

    /// Check if an expression contains effectful calls nested inside if/case/block
    /// branches. Like `has_nested_effect_call` but also detects effectful function
    /// calls (e.g. `assert_eq 1 1`) that the static utility misses because it has
    /// no access to the resolution/fun_info tables.
    fn has_nested_effectful_expr(&self, expr: &Expr) -> bool {
        match &expr.kind {
            ExprKind::If {
                then_branch,
                else_branch,
                ..
            } => self.branch_is_effectful(then_branch) || self.branch_is_effectful(else_branch),
            ExprKind::Case { arms, .. } => arms
                .iter()
                .any(|arm| self.branch_is_effectful(&arm.node.body)),
            ExprKind::Block { stmts, .. } => stmts.iter().any(|s| match &s.node {
                Stmt::Expr(e) => self.branch_is_effectful(e),
                Stmt::Let { value, .. } => self.branch_is_effectful(value),
                Stmt::LetFun { body, .. } => self.branch_is_effectful(body),
            }),
            ExprKind::RecordCreate { fields, .. } | ExprKind::AnonRecordCreate { fields } => {
                fields.iter().any(|(_, _, e)| self.branch_is_effectful(e))
            }
            _ => false,
        }
    }

    /// Check if an expression is or contains an effectful call — either a direct
    /// effect op (`!` call), an effectful function call, or nested branches
    /// containing either.
    fn branch_is_effectful(&self, expr: &Expr) -> bool {
        collect_effect_call(expr).is_some()
            || self.expr_is_effectful_call(expr)
            || self.has_nested_effectful_expr(expr)
    }

    /// Canonical predicate for "is this a saturated effectful function call?"
    ///
    /// Reads from the pre-populated `CallEffectMap`. Returns true when the
    /// outer expression is an `App` whose entry classifies as effectful
    /// (`StaticOps` or `RowForwarded`). Bare references and partial
    /// applications are tagged `Pure` by the populator.
    pub(super) fn expr_is_effectful_call(&self, expr: &Expr) -> bool {
        if !matches!(expr.kind, ExprKind::App { .. }) {
            return false;
        }
        matches!(
            self.call_effects.get(&expr.id).map(|i| &i.kind),
            Some(super::call_effects::CallEffectKind::StaticOps { .. })
                | Some(super::call_effects::CallEffectKind::RowForwarded { .. })
        )
    }

    /// Build the per-call effect map for the module currently being lowered.
    /// Snapshots the relevant `FunInfo` and `EffectDefs` and hands them to the
    /// stand-alone `call_effects::Populator` walker.
    fn populate_call_effects(&self, program: &ast::Program) -> super::call_effects::CallEffectMap {
        use super::call_effects::{FunSig, Populator};

        let fun_sigs: HashMap<String, FunSig> = self
            .fun_info
            .iter()
            .map(|(name, info)| {
                (
                    name.clone(),
                    FunSig {
                        arity: info.arity,
                        effects: info.effects.clone(),
                        param_absorbed_effects: info.param_absorbed_effects.clone(),
                        is_open_row: info.is_open_row,
                    },
                )
            })
            .collect();

        let effect_ops: HashMap<String, Vec<String>> = self
            .effect_defs
            .iter()
            .map(|(eff, info)| {
                let mut ops: Vec<String> = info.ops.keys().cloned().collect();
                ops.sort();
                (eff.clone(), ops)
            })
            .collect();

        Populator::new(super::call_effects::PopulatorInputs {
            resolved: &self.resolved,
            check_result: &self.check_result,
            ctx: self.ctx,
            fun_sigs: &fun_sigs,
            effect_ops: &effect_ops,
            effect_canonical: &self.effect_canonical,
            let_effect_bindings: &self.ctx.let_effect_bindings,
            impl_effects_by_dict: &self.impl_effects_by_dict,
        })
        .populate(program)
    }

    fn inline_val_deps_for_module(
        expr: &Expr,
        module_name: &str,
        inline_exprs: &HashMap<String, Expr>,
        out: &mut Vec<String>,
    ) {
        match &expr.kind {
            ExprKind::Var { name, .. } => {
                if inline_exprs.contains_key(name) && !out.contains(name) {
                    out.push(name.clone());
                }
            }
            ExprKind::QualifiedName { module, name, .. } if module == module_name => {
                if inline_exprs.contains_key(name) && !out.contains(name) {
                    out.push(name.clone());
                }
            }
            ExprKind::App { func, arg, .. } => {
                Self::inline_val_deps_for_module(func, module_name, inline_exprs, out);
                Self::inline_val_deps_for_module(arg, module_name, inline_exprs, out);
            }
            ExprKind::Tuple { elements, .. } | ExprKind::ListLit { elements } => {
                for e in elements {
                    Self::inline_val_deps_for_module(e, module_name, inline_exprs, out);
                }
            }
            ExprKind::Cons { head, tail }
            | ExprKind::BinOp {
                left: head,
                right: tail,
                ..
            } => {
                Self::inline_val_deps_for_module(head, module_name, inline_exprs, out);
                Self::inline_val_deps_for_module(tail, module_name, inline_exprs, out);
            }
            ExprKind::UnaryMinus { expr, .. } | ExprKind::Ascription { expr, .. } => {
                Self::inline_val_deps_for_module(expr, module_name, inline_exprs, out);
            }
            _ => {}
        }
    }

    fn lower_inline_vals_for_module(
        &mut self,
        module_name: &str,
        inline_exprs: &HashMap<String, Expr>,
        expose_bare: bool,
    ) {
        let mut lowered = HashMap::new();
        let mut visiting = std::collections::HashSet::new();
        let names: Vec<String> = inline_exprs.keys().cloned().collect();
        for name in names {
            self.lower_inline_val_for_module(
                module_name,
                &name,
                inline_exprs,
                &mut lowered,
                &mut visiting,
                expose_bare,
            );
        }
    }

    fn lower_inline_val_for_module(
        &mut self,
        module_name: &str,
        name: &str,
        inline_exprs: &HashMap<String, Expr>,
        lowered: &mut HashMap<String, CExpr>,
        visiting: &mut std::collections::HashSet<String>,
        expose_bare: bool,
    ) -> Option<CExpr> {
        let canonical = format!("{}.{}", module_name, name);
        if let Some(existing) = self.inline_vals.get(&canonical).cloned() {
            return Some(existing);
        }
        if let Some(existing) = lowered.get(name).cloned() {
            return Some(existing);
        }
        let expr = inline_exprs.get(name)?;
        if !visiting.insert(name.to_string()) {
            return None;
        }

        let mut deps = Vec::new();
        Self::inline_val_deps_for_module(expr, module_name, inline_exprs, &mut deps);
        for dep in deps {
            if dep != name {
                self.lower_inline_val_for_module(
                    module_name,
                    &dep,
                    inline_exprs,
                    lowered,
                    visiting,
                    expose_bare,
                );
            }
        }

        let saved_source_module =
            std::mem::replace(&mut self.current_source_module, module_name.to_string());
        let lowered_expr = self.lower_expr(expr);
        self.current_source_module = saved_source_module;

        visiting.remove(name);
        lowered.insert(name.to_string(), lowered_expr.clone());
        self.inline_vals
            .entry(canonical)
            .or_insert_with(|| lowered_expr.clone());
        if expose_bare {
            self.inline_vals
                .entry(name.to_string())
                .or_insert_with(|| lowered_expr.clone());
        }
        Some(lowered_expr)
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
            Some(ResolvedName::ImportedFun {
                erlang_mod,
                name: erl_name,
                ..
            }) => CExpr::Call(erlang_mod.clone(), erl_name.clone(), call_args),
            Some(ResolvedName::LocalFun {
                name,
                source_module,
                ..
            }) => self.lower_local_fun_call(name, arity, call_args, source_module.as_deref()),
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

    pub fn lower_module(&mut self, module_name: &str, program: &ast::Program) -> CModule {
        self.current_module = module_name.to_string();
        self.current_source_module = program
            .iter()
            .find_map(|decl| {
                if let Decl::ModuleDecl { path, .. } = decl {
                    Some(path.join("."))
                } else {
                    None
                }
            })
            .unwrap_or_else(|| module_name.to_string());
        let mut pending_annotations = self.init_module(module_name, program);

        // Group FunBindings by name, preserving declaration order, and simultaneously
        // populate top_level_funs. Handler params are added to the arity for effectful funs.
        let mut clause_groups: Vec<(String, usize, Vec<Clause>, crate::token::Span)> = Vec::new();
        type DictCtor<'b> = (&'b str, &'b [String], &'b [Expr], &'b [String]);
        let mut dict_constructors: Vec<DictCtor<'_>> = Vec::new();
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
                    let mut param_types = Vec::new();
                    if effects.is_empty()
                        && let Some(scheme) = self.check_result.env.get(name)
                    {
                        let resolved_ty = self.check_result.sub.apply(&scheme.ty);
                        effects = self.canonicalize_effects(
                            util::arity_and_effects_from_type(&resolved_ty).1,
                        );
                        param_absorbed_effects =
                            util::param_absorbed_effects_from_type(&resolved_ty)
                                .into_iter()
                                .map(|(idx, effs)| (idx, self.canonicalize_effects(effs)))
                                .collect();
                        param_types = util::param_types_from_type(&resolved_ty);
                    } else if let Some(scheme) = self.check_result.env.get(name) {
                        param_types =
                            util::param_types_from_type(&self.check_result.sub.apply(&scheme.ty));
                    }
                    let mut base_arity = lower_params(params).len() + count_lambda_params(body);
                    // For eta-reduced functions (e.g. `pg_text = coerce_value`),
                    // the binding has 0 params but the type annotation declares a
                    // higher arity. Use the annotation's arity so cross-module
                    // callers (who derive arity from the type) find the right /N.
                    if let Some(scheme) = self.check_result.env.get(name) {
                        let declared_arity = util::arity_and_effects_from_type(
                            &self.check_result.sub.apply(&scheme.ty),
                        )
                        .0;
                        if declared_arity > base_arity {
                            base_arity = declared_arity;
                        }
                    }
                    let arity = self.expanded_arity(base_arity, &effects);
                    let is_open_row = self
                        .check_result
                        .env
                        .get(name)
                        .map(|scheme| {
                            util::has_open_effect_row(&self.check_result.sub.apply(&scheme.ty))
                        })
                        .unwrap_or(false);
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
                                is_open_row,
                                param_absorbed_effects,
                                param_types,
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
                    impl_effects,
                    ..
                } => {
                    self.fun_info.insert(
                        name.clone(),
                        FunInfo {
                            arity: dict_params.len(),
                            ..Default::default()
                        },
                    );
                    dict_constructors.push((name, dict_params, methods, impl_effects));
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

        // Build dict_name -> impl_effects from the active module's
        // `DictConstructor` nodes (which carry the field directly post-
        // elaboration, since the active module may not appear in
        // `check_result.codegen_info()`) and imported modules' TraitImplDicts.
        // Used by both the call-effects pre-pass (to classify
        // `DictMethodAccess` call sites) and dict-constructor emission below.
        self.impl_effects_by_dict.clear();
        for (name, _, _, impl_effects) in &dict_constructors {
            self.impl_effects_by_dict
                .insert((*name).to_string(), impl_effects.to_vec());
        }
        for m in self.ctx.modules.values() {
            for d in &m.codegen_info.trait_impl_dicts {
                self.impl_effects_by_dict
                    .entry(d.dict_name.clone())
                    .or_insert_with(|| d.impl_effects.clone());
            }
        }

        // Call-effects pre-pass: tag every `App` node in the elaborated
        // program with `CallEffectInfo` so the lowerer can consume it via
        // lookup. Runs after `init_module` + per-decl `fun_info` registration
        // so all callees have arity/effect entries by the time we classify
        // their call sites.
        self.call_effects = self.populate_call_effects(program);
        // Cross-module inlined handler bodies live in the elaborated programs
        // of compiled modules and are lowered through the active Lowerer.
        // Tag their `App` nodes too so the parallel-check can see them.
        for (_name, compiled) in self.ctx.modules.iter() {
            let cross_map = self.populate_call_effects(&compiled.elaborated);
            for (id, info) in cross_map {
                self.call_effects.entry(id).or_insert(info);
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
                let call_args: Vec<CExpr> = arg_vars
                    .iter()
                    .zip(params.iter())
                    .filter(|(_, (_, ty))| !is_unit_type_expr(ty))
                    .map(|(v, _)| CExpr::Var(v.clone()))
                    .collect();
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
        // when lowering function bodies. Lower each module's inline vals under
        // that module's semantic identity, so sibling refs like `b = a` resolve
        // against the defining module rather than the importing module.
        let local_inline_exprs: HashMap<String, Expr> = val_bindings
            .iter()
            .filter(|&(_name, is_inline, _value)| *is_inline)
            .map(|(name, _is_inline, value)| ((*name).to_string(), (*value).clone()))
            .collect();
        self.lower_inline_vals_for_module(
            &self.current_source_module.clone(),
            &local_inline_exprs,
            true,
        );

        let imported_inline_exprs: Vec<(String, HashMap<String, Expr>)> = self
            .ctx
            .modules
            .iter()
            .filter(|(mod_name, _)| *mod_name != &self.current_source_module)
            .map(|(mod_name, m)| {
                (
                    mod_name.clone(),
                    m.codegen_info.inline_vals.iter().cloned().collect(),
                )
            })
            .collect();
        for (mod_name, inline_exprs) in imported_inline_exprs {
            self.lower_inline_vals_for_module(&mod_name, &inline_exprs, false);
        }
        for (mod_name, m) in &self.ctx.modules {
            if mod_name == &self.current_source_module {
                continue;
            }
            for (val_name, _) in &m.codegen_info.inline_vals {
                let canonical = format!("{}.{}", mod_name, val_name);
                debug_assert!(
                    self.inline_vals.contains_key(&canonical),
                    "imported inline val was not lowered canonically: {canonical}"
                );
            }
        }

        for (name, arity, clauses, fun_span) in clause_groups {
            self.current_function = name.clone();
            let is_entry_export = self.entry_export.as_deref() == Some(name.as_str());
            if !is_module || self.pub_names.contains(&name) || is_entry_export {
                exports.push((name.clone(), arity));
            }

            // Effects in scope for this function (drives _Evidence threading).
            let effects = self.fun_effects(&name).cloned().unwrap_or_default();
            let saved_direct_ops = std::mem::take(&mut self.direct_ops);

            let has_effects = !effects.is_empty() && !self.effect_handler_ops(&effects).is_empty();
            // Effectful arity = user + Evidence + ReturnK.
            let base_arity = arity - if has_effects { 2 } else { 0 };
            let effect_return_k = has_effects.then(|| CExpr::Var("_ReturnK".to_string()));

            // Install the evidence context for the function body. Op-call
            // emission inside the body reads handler closures out of
            // `current_evidence`.
            let saved_evidence = self.current_evidence.clone();
            if has_effects {
                let layout = evidence::EvidenceLayout::new(effects.iter().cloned());
                let is_open_row = self
                    .fun_info
                    .get(&name)
                    .map(|f| f.is_open_row)
                    .unwrap_or(false);
                self.current_evidence = Some(EvidenceCtx {
                    var: "_Evidence".to_string(),
                    layout,
                    is_open: is_open_row,
                });
            }

            // For effectful functions, _ReturnK is threaded explicitly into
            // terminal body lowering so handler aborts bypass normal return.
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
                // Eta-expand if the binding has fewer params than the type
                // declares (e.g. `pg_text = coerce_value` with type String -> Value).
                // Without this, the function is emitted as /0 but cross-module
                // callers derive arity from the type and call /1.
                let eta_count = base_arity.saturating_sub(params_ce.len());
                let eta_params: Vec<String> =
                    (0..eta_count).map(|i| format!("_Eta{}", i)).collect();
                params_ce.extend(eta_params.clone());
                if has_effects {
                    params_ce.push("_Evidence".to_string());
                    params_ce.push("_ReturnK".to_string());
                }
                // For non-block bodies, lower_block didn't run, so apply return_k.
                // Special case: if the body is a terminal effect call, pass _ReturnK
                // directly as K so abort-style handlers skip the rest (proper CPS).
                let mut body_ce = if has_effects && !matches!(body.kind, ExprKind::Block { .. }) {
                    self.lower_terminal_effectful_expr_with_return_k(body, effect_return_k.clone())
                } else {
                    self.lower_expr_with_installed_return_k(body, effect_return_k.clone())
                };
                // Apply eta params to the body: `pg_text(_Eta0) = coerce_value(_Eta0)`
                if !eta_params.is_empty() {
                    let eta_args: Vec<CExpr> =
                        eta_params.iter().map(|p| CExpr::Var(p.clone())).collect();
                    body_ce = CExpr::Apply(Box::new(body_ce), eta_args);
                }
                CExpr::Fun(params_ce, Box::new(body_ce))
            } else {
                // Multi-clause or single clause with a guard: generate fresh arg vars
                // and case-match on them using proper Core Erlang values syntax.
                let mut arg_vars: Vec<String> =
                    (0..base_arity).map(|i| format!("_Arg{}", i)).collect();
                if has_effects {
                    arg_vars.push("_Evidence".to_string());
                    arg_vars.push("_ReturnK".to_string());
                }

                let arms: Vec<CArm> = clauses
                    .iter()
                    .map(|(params, guard, body)| {
                        // Pattern only matches user params, not handler params
                        let pat = if base_arity == 1 {
                            self.lower_pat(
                                &params[0],
                                &self.constructor_atoms,
                                self.handler_origin_module(),
                            )
                        } else if base_arity == 0 {
                            // No user params to match on -- use wildcard
                            CPat::Wildcard
                        } else {
                            CPat::Values(
                                params
                                    .iter()
                                    .map(|p| {
                                        self.lower_pat(
                                            p,
                                            &self.constructor_atoms,
                                            self.handler_origin_module(),
                                        )
                                    })
                                    .collect(),
                            )
                        };
                        let guard_ce = guard.as_deref().map(|g| self.lower_expr(g));
                        let body_ce = if has_effects && !matches!(body.kind, ExprKind::Block { .. })
                        {
                            self.lower_terminal_effectful_expr_with_return_k(
                                body,
                                effect_return_k.clone(),
                            )
                        } else {
                            self.lower_expr_with_installed_return_k(body, effect_return_k.clone())
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

            self.direct_ops = saved_direct_ops;
            self.current_evidence = saved_evidence;

            // fun_span is available for future use (e.g. function-level metadata)
            let _ = fun_span;
            fun_defs.push(CFunDef {
                name,
                arity,
                body: fun_body,
            });
        }

        // Emit dictionary constructor functions
        for (name, dict_params, methods, impl_effects) in dict_constructors {
            let arity = dict_params.len();
            let params: Vec<String> = dict_params.iter().map(|p| core_var(p)).collect();
            // Methods inherit the impl's `needs` clause as their effect row.
            // When non-empty, set `lambda_effect_context` so each method's
            // Lambda lowers with `_Evidence`/`_ReturnK` params and the body
            // runs with evidence installed (mirrors the FunBinding effectful-
            // function path for top-level effectful funs).
            let impl_effects: Vec<String> = impl_effects.to_vec();
            let method_exprs: Vec<CExpr> = methods
                .iter()
                .map(|m| {
                    if !impl_effects.is_empty() {
                        self.lambda_effect_context = Some(impl_effects.clone());
                    }
                    let ce = self.lower_expr(m);
                    self.lambda_effect_context = None;
                    ce
                })
                .collect();
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

        // If the program uses ets_ref, prepend ETS table creation to the entry function.
        if self.check_result.needs_ets_ref_table
            && let Some(entry_def) = fun_defs
                .iter_mut()
                .find(|f| f.name == "main" || f.name == "tests")
        {
            entry_def.body = Self::wrap_with_ets_init(entry_def.body.clone());
        }

        // If the program uses beam_vec, prepend ETS table creation for saga_vec_store.
        if self.check_result.needs_vec_table
            && let Some(entry_def) = fun_defs
                .iter_mut()
                .find(|f| f.name == "main" || f.name == "tests")
        {
            entry_def.body = Self::wrap_with_vec_init(entry_def.body.clone());
        }

        CModule {
            name: module_name.to_string(),
            exports,
            funs: fun_defs,
        }
    }

    /// Wraps a function body with ETS table creation for `saga_ref_store`.
    /// Emits: `fun(Args...) -> let _ = ets:new(saga_ref_store, [set, public, named_table]) in <original body>`
    fn wrap_with_ets_init(body: CExpr) -> CExpr {
        // Unwrap the outer Fun to inject the let-binding inside
        match body {
            CExpr::Fun(params, inner_body) => {
                let ets_init = CExpr::Call(
                    "ets".to_string(),
                    "new".to_string(),
                    vec![
                        CExpr::Lit(CLit::Atom("saga_ref_store".into())),
                        CExpr::Cons(
                            Box::new(CExpr::Lit(CLit::Atom("set".into()))),
                            Box::new(CExpr::Cons(
                                Box::new(CExpr::Lit(CLit::Atom("public".into()))),
                                Box::new(CExpr::Cons(
                                    Box::new(CExpr::Lit(CLit::Atom("named_table".into()))),
                                    Box::new(CExpr::Nil),
                                )),
                            )),
                        ),
                    ],
                );
                CExpr::Fun(
                    params,
                    Box::new(CExpr::Let(
                        "_EtsRefInit".to_string(),
                        Box::new(ets_init),
                        inner_body,
                    )),
                )
            }
            other => other,
        }
    }

    /// Wraps a function body with ETS table creation for `saga_vec_store`.
    fn wrap_with_vec_init(body: CExpr) -> CExpr {
        match body {
            CExpr::Fun(params, inner_body) => {
                let ets_init = CExpr::Call(
                    "ets".to_string(),
                    "new".to_string(),
                    vec![
                        CExpr::Lit(CLit::Atom("saga_vec_store".into())),
                        CExpr::Cons(
                            Box::new(CExpr::Lit(CLit::Atom("set".into()))),
                            Box::new(CExpr::Cons(
                                Box::new(CExpr::Lit(CLit::Atom("public".into()))),
                                Box::new(CExpr::Cons(
                                    Box::new(CExpr::Lit(CLit::Atom("named_table".into()))),
                                    Box::new(CExpr::Nil),
                                )),
                            )),
                        ),
                    ],
                );
                CExpr::Fun(
                    params,
                    Box::new(CExpr::Let(
                        "_EtsVecInit".to_string(),
                        Box::new(ets_init),
                        inner_body,
                    )),
                )
            }
            other => other,
        }
    }

    fn effectful_call_return_k_binding(&mut self, return_k: Option<CExpr>) -> (String, CExpr) {
        let rk_var = self.fresh();
        let return_k = return_k.unwrap_or_else(|| {
            let p = self.fresh();
            CExpr::Fun(vec![p.clone()], Box::new(CExpr::Var(p)))
        });
        (rk_var, return_k)
    }

    pub(super) fn wrap_let_bindings(&self, bindings: Vec<(String, CExpr)>, body: CExpr) -> CExpr {
        bindings.into_iter().rev().fold(body, |body, (var, val)| {
            CExpr::Let(var, Box::new(val), Box::new(body))
        })
    }

    fn lower_expr_value_with_expected_type(
        &mut self,
        expr: &Expr,
        expected_ty: Option<&crate::typechecker::Type>,
    ) -> CExpr {
        if let Some(expected_ty) = expected_ty {
            if let Some((ctor_name, args)) = collect_ctor_call(expr) {
                let bare = crate::typechecker::bare_type_name(match expected_ty {
                    crate::typechecker::Type::Con(name, _) => name,
                    _ => "",
                });
                if bare == "List"
                    && let crate::typechecker::Type::Con(_, type_args) = expected_ty
                    && let Some(elem_ty) = type_args.first()
                {
                    match (
                        ctor_name.rsplit('.').next().unwrap_or(ctor_name),
                        args.as_slice(),
                    ) {
                        ("Nil", []) => return CExpr::Nil,
                        ("Cons", [head, tail]) => {
                            let head_var = self.fresh();
                            let tail_var = self.fresh();
                            let head_ce =
                                self.lower_expr_value_with_expected_type(head, Some(elem_ty));
                            let tail_ce =
                                self.lower_expr_value_with_expected_type(tail, Some(expected_ty));
                            return CExpr::Let(
                                head_var.clone(),
                                Box::new(head_ce),
                                Box::new(CExpr::Let(
                                    tail_var.clone(),
                                    Box::new(tail_ce),
                                    Box::new(CExpr::Cons(
                                        Box::new(CExpr::Var(head_var)),
                                        Box::new(CExpr::Var(tail_var)),
                                    )),
                                )),
                            );
                        }
                        _ => {}
                    }
                }

                if bare != "List"
                    && let Some(arg_tys) =
                        self.constructor_arg_types_from_expected(ctor_name, expected_ty)
                {
                    let mut vars = Vec::new();
                    let mut bindings = Vec::new();
                    for (idx, arg) in args.iter().enumerate() {
                        let var = self.fresh();
                        let child_expected = arg_tys.get(idx);
                        let val = self.lower_expr_value_with_expected_type(arg, child_expected);
                        vars.push(var.clone());
                        bindings.push((var, val));
                    }
                    let atom = util::mangle_ctor_atom(
                        ctor_name,
                        &self.constructor_atoms,
                        self.handler_origin_module(),
                    );
                    let mut elems = vec![CExpr::Lit(CLit::Atom(atom))];
                    elems.extend(vars.iter().map(|v| CExpr::Var(v.clone())));
                    let tuple = CExpr::Tuple(elems);
                    return self.wrap_let_bindings(bindings, tuple);
                }
            }

            if let ExprKind::Tuple { elements, .. } = &expr.kind
                && let crate::typechecker::Type::Con(name, elem_tys) = expected_ty
                && crate::typechecker::bare_type_name(name) == "Tuple"
                && elem_tys.len() == elements.len()
            {
                let mut vars = Vec::new();
                let mut bindings = Vec::new();
                for (elem, elem_ty) in elements.iter().zip(elem_tys.iter()) {
                    let var = self.fresh();
                    let val = self.lower_expr_value_with_expected_type(elem, Some(elem_ty));
                    vars.push(var.clone());
                    bindings.push((var, val));
                }
                let tuple = CExpr::Tuple(vars.iter().map(|v| CExpr::Var(v.clone())).collect());
                return self.wrap_let_bindings(bindings, tuple);
            }

            if matches!(expr.kind, ExprKind::Lambda { .. })
                || self.lower_eta_reduced_effect_expr(expr).is_some()
            {
                let saved_ctx = self.lambda_effect_context.take();
                let effects = crate::typechecker::effects_from_type(expected_ty);
                if !effects.is_empty() {
                    let mut effects: Vec<String> = effects.into_iter().collect();
                    effects.sort();
                    self.lambda_effect_context = Some(self.canonicalize_effects(effects));
                }
                let ce = self
                    .lower_eta_reduced_effect_expr(expr)
                    .unwrap_or_else(|| self.lower_expr_value(expr));
                self.lambda_effect_context = saved_ctx;
                return ce;
            }

            match &expr.kind {
                ExprKind::RecordCreate { name, fields, .. } => {
                    let Some(field_tys) = self.record_field_types_from_expected(expected_ty) else {
                        return self.lower_expr_value(expr);
                    };
                    let order = self
                        .resolved_record_fields(expr.id, name)
                        .cloned()
                        .unwrap_or_default();
                    let field_map: HashMap<&str, &Expr> =
                        fields.iter().map(|(n, _, e)| (n.as_str(), e)).collect();
                    let mut vars = Vec::new();
                    let mut bindings = Vec::new();
                    for field_name in &order {
                        let var = self.fresh();
                        let field_expr = field_map
                            .get(field_name.as_str())
                            .expect("field missing in RecordCreate");
                        let child_expected = field_tys.get(field_name.as_str());
                        let val =
                            self.lower_expr_value_with_expected_type(field_expr, child_expected);
                        vars.push(var.clone());
                        bindings.push((var, val));
                    }
                    let atom = util::mangle_ctor_atom(
                        name,
                        &self.constructor_atoms,
                        self.handler_origin_module(),
                    );
                    let mut elems = vec![CExpr::Lit(CLit::Atom(atom))];
                    elems.extend(vars.iter().map(|v| CExpr::Var(v.clone())));
                    return self.wrap_let_bindings(bindings, CExpr::Tuple(elems));
                }
                ExprKind::AnonRecordCreate { fields, .. } => {
                    let Some(field_tys) = self.record_field_types_from_expected(expected_ty) else {
                        return self.lower_expr_value(expr);
                    };
                    let names: Vec<&str> = fields.iter().map(|(n, _, _)| n.as_str()).collect();
                    let tag = crate::ast::anon_record_tag(&names);
                    let mut sorted_names: Vec<String> =
                        names.iter().map(|n| n.to_string()).collect();
                    sorted_names.sort();
                    let field_map: HashMap<&str, &Expr> =
                        fields.iter().map(|(n, _, e)| (n.as_str(), e)).collect();
                    let mut vars = Vec::new();
                    let mut bindings = Vec::new();
                    for field_name in &sorted_names {
                        let var = self.fresh();
                        let field_expr = field_map
                            .get(field_name.as_str())
                            .expect("field missing in AnonRecordCreate");
                        let child_expected = field_tys.get(field_name.as_str());
                        let val =
                            self.lower_expr_value_with_expected_type(field_expr, child_expected);
                        vars.push(var.clone());
                        bindings.push((var, val));
                    }
                    let mut elems = vec![CExpr::Lit(CLit::Atom(tag))];
                    elems.extend(vars.iter().map(|v| CExpr::Var(v.clone())));
                    return self.wrap_let_bindings(bindings, CExpr::Tuple(elems));
                }
                _ => {}
            }
        }

        self.lower_expr_value(expr)
    }

    fn lower_call_args_with_expected_types(
        &mut self,
        args: &[&Expr],
        param_types: Option<&[crate::typechecker::Type]>,
    ) -> (Vec<String>, Vec<(String, CExpr)>) {
        let mut arg_vars: Vec<String> = Vec::new();
        let mut bindings: Vec<(String, CExpr)> = Vec::new();
        for (i, arg) in args.iter().enumerate() {
            let v = self.fresh();
            let ce = self
                .lower_expr_value_with_expected_type(arg, param_types.and_then(|tys| tys.get(i)));
            arg_vars.push(v.clone());
            bindings.push((v, ce));
        }
        (arg_vars, bindings)
    }

    fn lower_call_args(
        &mut self,
        args: &[&Expr],
        param_effects: Option<&HashMap<usize, Vec<String>>>,
    ) -> (Vec<String>, Vec<(String, CExpr)>) {
        let mut arg_vars: Vec<String> = Vec::new();
        let mut bindings: Vec<(String, CExpr)> = Vec::new();
        for (i, arg) in args.iter().enumerate() {
            let v = self.fresh();
            let saved_ctx = self.lambda_effect_context.take();
            if let Some(pe) = param_effects
                && let Some(effs) = pe.get(&i)
            {
                self.lambda_effect_context = Some(effs.clone());
            }
            let ce = self
                .lower_eta_reduced_effect_expr(arg)
                .unwrap_or_else(|| self.lower_expr_value(arg));
            self.lambda_effect_context = saved_ctx;
            arg_vars.push(v.clone());
            bindings.push((v, ce));
        }
        (arg_vars, bindings)
    }

    /// Build the evidence value to pass to a callee that declares the given
    /// effects. Returns a fresh let-binding that produces the evidence
    /// (`(var_name, value_expr)`).
    ///
    /// - Closed-row caller (`current_evidence` is `Some` with `is_open == false`)
    ///   and callee effects are a strict subset: emit a runtime
    ///   `project_evidence` narrowing call.
    /// - Otherwise: forward the caller's evidence directly. When the caller
    ///   has no evidence in scope (pure caller installing first effect via a
    ///   `with` further out, or handler-bound value paths), emit an empty
    ///   tuple as a placeholder so arity matches.
    pub(super) fn build_call_evidence(&mut self, callee_effects: &[String]) -> (String, CExpr) {
        let var = self.fresh();
        let value = match &self.current_evidence {
            Some(ctx) if !ctx.is_open => {
                // Project when the callee asks for fewer effects than the
                // caller's static layout carries. The runtime helper handles
                // the case where no narrowing is required (returns the input
                // tuple unchanged when tags match), but we skip the call when
                // we can prove statically that no narrowing is needed.
                let caller_tags: std::collections::HashSet<&str> =
                    ctx.layout.tags().iter().map(|s| s.as_str()).collect();
                let callee_subset = callee_effects
                    .iter()
                    .all(|t| caller_tags.contains(t.as_str()));
                let narrowing = callee_subset && callee_effects.len() < ctx.layout.tags().len();
                if narrowing {
                    let tags: Vec<&str> = callee_effects.iter().map(|s| s.as_str()).collect();
                    evidence::project_evidence(CExpr::Var(ctx.var.clone()), &tags)
                } else {
                    CExpr::Var(ctx.var.clone())
                }
            }
            Some(ctx) => CExpr::Var(ctx.var.clone()),
            None => CExpr::Tuple(Vec::new()),
        };
        (var, value)
    }

    /// Lower a saturated or partially-applied call to a *resolved* function
    /// (`emit_call` semantics: BIF / external / local / imported with known
    /// arity and param types). For runtime closure values bound to local
    /// variables, see [`Self::lower_effectful_var_call`].
    ///
    /// The two helpers are *not* collapsible: resolved funs have a static
    /// arity (so partial application emits a wrapper closure here, and arg
    /// lowering can use callee-side expected types) and call via
    /// `emit_call`; effectful vars have no static arity at the call site
    /// and lower as `CExpr::Apply(Var, args)`. Merging them would replace
    /// two focused branches with one branchier function.
    fn lower_resolved_fun_call(
        &mut self,
        app_id: NodeId,
        func_name: &str,
        head_expr: &Expr,
        args: &[&Expr],
        return_k: Option<CExpr>,
        call_span: Option<&crate::token::Span>,
    ) -> Option<CExpr> {
        // Source of truth: the per-call effect map populated pre-lowering.
        // `info` tells us whether this call is effectful (needs evidence + _ReturnK)
        // and which effects the callee declares; both used to be recomputed here
        // from `resolved_effects` + `effect_handler_ops`.
        let info = self.call_effects.get(&app_id);
        let (is_effectful, callee_effects_vec): (bool, Vec<String>) = match info.map(|i| &i.kind) {
            Some(super::call_effects::CallEffectKind::StaticOps { ops })
            | Some(super::call_effects::CallEffectKind::RowForwarded { static_ops: ops }) => {
                let mut effs: Vec<String> = ops.iter().map(|k| k.effect.clone()).collect();
                effs.sort();
                effs.dedup();
                (!ops.is_empty(), effs)
            }
            _ => (false, Vec::new()),
        };
        let total_arity = self
            .resolved_fun_info(head_expr.id, func_name)
            .map(|f| f.arity);
        // Effectful callees take `_Evidence` and `_ReturnK`.
        let extras = if is_effectful { 2 } else { 0 };

        if let Some(arity) = total_arity
            && args.len() + extras == arity
        {
            let param_types = self.resolved_fun_info(head_expr.id, func_name).map(|f| {
                f.param_types
                    .iter()
                    .take(args.len())
                    .cloned()
                    .collect::<Vec<_>>()
            });

            let is_effectful_outer = is_effectful;
            let effectful_arg_idxs: Vec<usize> = if is_effectful_outer {
                args.iter()
                    .enumerate()
                    .filter(|(_, a)| self.expr_is_effectful_call(a))
                    .map(|(i, _)| i)
                    .collect()
            } else {
                Vec::new()
            };

            if !effectful_arg_idxs.is_empty() {
                // CPS-chain effectful argument calls so that aborting handlers
                // skip the outer call entirely. For each effectful arg, the rest
                // of the outer call (and the remaining args) becomes the inner
                // call's return continuation.
                let mut arg_vars: Vec<String> = Vec::with_capacity(args.len());
                let mut pure_bindings: Vec<(String, CExpr)> = Vec::new();
                for (i, arg) in args.iter().enumerate() {
                    let v = self.fresh();
                    arg_vars.push(v.clone());
                    if !effectful_arg_idxs.contains(&i) {
                        let pty = param_types.as_ref().and_then(|t| t.get(i));
                        let ce = self.lower_expr_value_with_expected_type(arg, pty);
                        pure_bindings.push((v, ce));
                    }
                }

                let mut call_args: Vec<CExpr> =
                    arg_vars.iter().map(|v| CExpr::Var(v.clone())).collect();
                // Effectful callee: thread evidence + _ReturnK.
                let (ev_var, ev_ce) = self.build_call_evidence(&callee_effects_vec);
                call_args.push(CExpr::Var(ev_var.clone()));
                let (rk_var, rk_ce) = self.effectful_call_return_k_binding(return_k);
                call_args.push(CExpr::Var(rk_var.clone()));

                let outer_call =
                    self.emit_call(func_name, head_expr.id, arity, call_args, call_span);
                let mut body = CExpr::Let(rk_var, Box::new(rk_ce), Box::new(outer_call));
                body = CExpr::Let(ev_var, Box::new(ev_ce), Box::new(body));

                // Wrap body with each effectful arg's CPS continuation,
                // innermost (rightmost) first so left-to-right order is preserved.
                for &i in effectful_arg_idxs.iter().rev() {
                    let v = arg_vars[i].clone();
                    let inner_k = CExpr::Fun(vec![v], Box::new(body));
                    body = self.lower_expr_with_call_return_k(args[i], Some(inner_k));
                }

                return Some(self.wrap_let_bindings(pure_bindings, body));
            }

            let (mut arg_vars, mut bindings) =
                self.lower_call_args_with_expected_types(args, param_types.as_deref());
            if is_effectful {
                // Effectful callee: thread evidence + _ReturnK.
                let (ev_var, ev_ce) = self.build_call_evidence(&callee_effects_vec);
                bindings.push((ev_var.clone(), ev_ce));
                arg_vars.push(ev_var);
                let (rk_var, rk_ce) = self.effectful_call_return_k_binding(return_k);
                bindings.push((rk_var.clone(), rk_ce));
                arg_vars.push(rk_var);
            }
            let call_args: Vec<CExpr> = arg_vars.iter().map(|v| CExpr::Var(v.clone())).collect();
            let call = self.emit_call(func_name, head_expr.id, arity, call_args, call_span);
            return Some(self.wrap_let_bindings(bindings, call));
        }

        if let Some(arity) = total_arity {
            let user_slots = arity.saturating_sub(extras);
            if args.len() < user_slots {
                let remaining_user = user_slots - args.len();
                let param_types = self.resolved_fun_info(head_expr.id, func_name).map(|f| {
                    f.param_types
                        .iter()
                        .take(args.len())
                        .cloned()
                        .collect::<Vec<_>>()
                });
                let (arg_vars, bindings) =
                    self.lower_call_args_with_expected_types(args, param_types.as_deref());
                let mut params: Vec<String> = Vec::new();
                for _ in 0..remaining_user {
                    params.push(self.fresh());
                }
                let mut call_args: Vec<CExpr> =
                    arg_vars.iter().map(|v| CExpr::Var(v.clone())).collect();
                call_args.extend(params.iter().map(|p| CExpr::Var(p.clone())));
                if is_effectful {
                    // Closure takes `_Evidence` and `_ReturnK` for the
                    // residual user args; the call forwards them straight
                    // through.
                    let ev = "_Evidence".to_string();
                    params.push(ev.clone());
                    call_args.push(CExpr::Var(ev));
                    let rk = "_ReturnK".to_string();
                    params.push(rk.clone());
                    call_args.push(CExpr::Var(rk));
                }
                let call = self.emit_call(func_name, head_expr.id, arity, call_args, call_span);
                let lambda = CExpr::Fun(params, Box::new(call));
                return Some(self.wrap_let_bindings(bindings, lambda));
            }
        }

        None
    }

    /// Lower a call to a runtime closure value bound to a local variable
    /// whose type carries effects (e.g. `let g = factory(); g x`). See
    /// [`Self::lower_resolved_fun_call`] for the resolved-fun counterpart
    /// and the rationale for keeping the two paths separate.
    fn lower_effectful_var_call(
        &mut self,
        app_id: NodeId,
        var_name: &str,
        args: &[&Expr],
        return_k: Option<CExpr>,
    ) -> Option<CExpr> {
        // Source of truth: the per-call effect map, keyed by this App's NodeId.
        // Pre-pass already walked the lexical scope and recorded the absorbed
        // effects for the bound variable on its call-site App entry.
        let absorbed: Vec<String> = match self.call_effects.get(&app_id).map(|i| &i.kind) {
            Some(super::call_effects::CallEffectKind::StaticOps { ops })
            | Some(super::call_effects::CallEffectKind::RowForwarded { static_ops: ops })
                if !ops.is_empty() =>
            {
                let mut effs: Vec<String> = ops.iter().map(|k| k.effect.clone()).collect();
                effs.sort();
                effs.dedup();
                effs
            }
            _ => return None,
        };

        let effectful_arg_idxs: Vec<usize> = args
            .iter()
            .enumerate()
            .filter(|(_, a)| self.expr_is_effectful_call(a))
            .map(|(i, _)| i)
            .collect();

        if !effectful_arg_idxs.is_empty() {
            let mut arg_vars: Vec<String> = Vec::with_capacity(args.len());
            let mut pure_bindings: Vec<(String, CExpr)> = Vec::new();
            for (i, arg) in args.iter().enumerate() {
                let v = self.fresh();
                arg_vars.push(v.clone());
                if !effectful_arg_idxs.contains(&i) {
                    let saved_ctx = self.lambda_effect_context.take();
                    let ce = self
                        .lower_eta_reduced_effect_expr(arg)
                        .unwrap_or_else(|| self.lower_expr_value(arg));
                    self.lambda_effect_context = saved_ctx;
                    pure_bindings.push((v, ce));
                }
            }

            let mut call_args: Vec<CExpr> =
                arg_vars.iter().map(|v| CExpr::Var(v.clone())).collect();
            // Effectful var call: thread evidence + _ReturnK.
            let (ev_var, ev_ce) = self.build_call_evidence(&absorbed);
            call_args.push(CExpr::Var(ev_var.clone()));
            let (rk_var, rk_ce) = self.effectful_call_return_k_binding(return_k);
            call_args.push(CExpr::Var(rk_var.clone()));

            let outer_call = CExpr::Apply(Box::new(CExpr::Var(core_var(var_name))), call_args);
            let mut body = CExpr::Let(rk_var, Box::new(rk_ce), Box::new(outer_call));
            body = CExpr::Let(ev_var, Box::new(ev_ce), Box::new(body));

            for &i in effectful_arg_idxs.iter().rev() {
                let v = arg_vars[i].clone();
                let inner_k = CExpr::Fun(vec![v], Box::new(body));
                body = self.lower_expr_with_call_return_k(args[i], Some(inner_k));
            }

            return Some(self.wrap_let_bindings(pure_bindings, body));
        }

        let (mut arg_vars, mut bindings) = self.lower_call_args(args, None);
        // Effectful var call: thread evidence + _ReturnK.
        let (ev_var, ev_ce) = self.build_call_evidence(&absorbed);
        bindings.push((ev_var.clone(), ev_ce));
        arg_vars.push(ev_var);
        let (rk_var, rk_ce) = self.effectful_call_return_k_binding(return_k);
        bindings.push((rk_var.clone(), rk_ce));
        arg_vars.push(rk_var);
        let call = CExpr::Apply(
            Box::new(CExpr::Var(core_var(var_name))),
            arg_vars.iter().map(|v| CExpr::Var(v.clone())).collect(),
        );
        Some(self.wrap_let_bindings(bindings, call))
    }

    /// Lower a saturated effectful call whose head is a `DictMethodAccess`
    /// (post-elaboration shape of a trait method call). Returns `None` when
    /// the per-call effect map says the call is pure — caller falls through
    /// to the regular non-effectful path which extracts the method via
    /// `erlang:element` and applies it without evidence threading.
    fn lower_dict_method_call(
        &mut self,
        app_id: NodeId,
        dict: &Expr,
        method_index: usize,
        args: &[&Expr],
        return_k: Option<CExpr>,
    ) -> Option<CExpr> {
        let absorbed: Vec<String> = match self.call_effects.get(&app_id).map(|i| &i.kind) {
            Some(super::call_effects::CallEffectKind::StaticOps { ops })
            | Some(super::call_effects::CallEffectKind::RowForwarded { static_ops: ops })
                if !ops.is_empty() =>
            {
                let mut effs: Vec<String> = ops.iter().map(|k| k.effect.clone()).collect();
                effs.sort();
                effs.dedup();
                effs
            }
            _ => return None,
        };

        let dict_var = self.fresh();
        let dict_ce = self.lower_expr_value(dict);
        let method_var = self.fresh();
        let extract = cerl_call(
            "erlang",
            "element",
            vec![
                CExpr::Lit(CLit::Int(method_index as i64 + 1)),
                CExpr::Var(dict_var.clone()),
            ],
        );

        let effectful_arg_idxs: Vec<usize> = args
            .iter()
            .enumerate()
            .filter(|(_, a)| self.expr_is_effectful_call(a))
            .map(|(i, _)| i)
            .collect();

        if !effectful_arg_idxs.is_empty() {
            let mut arg_vars: Vec<String> = Vec::with_capacity(args.len());
            let mut pure_bindings: Vec<(String, CExpr)> = Vec::new();
            for (i, arg) in args.iter().enumerate() {
                let v = self.fresh();
                arg_vars.push(v.clone());
                if !effectful_arg_idxs.contains(&i) {
                    let ce = self.lower_expr_value(arg);
                    pure_bindings.push((v, ce));
                }
            }

            let mut call_args: Vec<CExpr> =
                arg_vars.iter().map(|v| CExpr::Var(v.clone())).collect();
            let (ev_var, ev_ce) = self.build_call_evidence(&absorbed);
            call_args.push(CExpr::Var(ev_var.clone()));
            let (rk_var, rk_ce) = self.effectful_call_return_k_binding(return_k);
            call_args.push(CExpr::Var(rk_var.clone()));

            let outer_call = CExpr::Apply(Box::new(CExpr::Var(method_var.clone())), call_args);
            let mut body = CExpr::Let(rk_var, Box::new(rk_ce), Box::new(outer_call));
            body = CExpr::Let(ev_var, Box::new(ev_ce), Box::new(body));

            for &i in effectful_arg_idxs.iter().rev() {
                let v = arg_vars[i].clone();
                let inner_k = CExpr::Fun(vec![v], Box::new(body));
                body = self.lower_expr_with_call_return_k(args[i], Some(inner_k));
            }

            let body = self.wrap_let_bindings(pure_bindings, body);
            let body = CExpr::Let(method_var, Box::new(extract), Box::new(body));
            return Some(CExpr::Let(dict_var, Box::new(dict_ce), Box::new(body)));
        }

        let (mut arg_vars, mut bindings) = self.lower_call_args(args, None);
        let (ev_var, ev_ce) = self.build_call_evidence(&absorbed);
        bindings.push((ev_var.clone(), ev_ce));
        arg_vars.push(ev_var);
        let (rk_var, rk_ce) = self.effectful_call_return_k_binding(return_k);
        bindings.push((rk_var.clone(), rk_ce));
        arg_vars.push(rk_var);
        let call = CExpr::Apply(
            Box::new(CExpr::Var(method_var.clone())),
            arg_vars.iter().map(|v| CExpr::Var(v.clone())).collect(),
        );
        let body = self.wrap_let_bindings(bindings, call);
        let body = CExpr::Let(method_var, Box::new(extract), Box::new(body));
        Some(CExpr::Let(dict_var, Box::new(dict_ce), Box::new(body)))
    }

    /// Lower a saturated effectful call whose head is a `Lambda` literal —
    /// `(fun x -> body) y`. Returns `None` when `call_effects[app_id]`
    /// classifies the call as pure; the caller then falls through to the
    /// regular path where the lambda lowers as a pure closure.
    ///
    /// When effectful, the lambda is recompiled as effectful (taking
    /// `_Evidence`/`_ReturnK` params, body lowered with evidence installed)
    /// by setting `lambda_effect_context` for the duration of `lower_expr`
    /// on the head. The call site threads evidence + return_k like any
    /// other effectful call. This preserves §8: the body sees the *call-time*
    /// evidence (passed as a param), not creation-time evidence.
    fn lower_lambda_head_call(
        &mut self,
        app_id: NodeId,
        lambda: &Expr,
        args: &[&Expr],
        return_k: Option<CExpr>,
    ) -> Option<CExpr> {
        let absorbed: Vec<String> = match self.call_effects.get(&app_id).map(|i| &i.kind) {
            Some(super::call_effects::CallEffectKind::StaticOps { ops })
            | Some(super::call_effects::CallEffectKind::RowForwarded { static_ops: ops })
                if !ops.is_empty() =>
            {
                let mut effs: Vec<String> = ops.iter().map(|k| k.effect.clone()).collect();
                effs.sort();
                effs.dedup();
                effs
            }
            _ => return None,
        };

        let saved_ctx = self.lambda_effect_context.take();
        self.lambda_effect_context = Some(absorbed.clone());
        let func_ce = self.lower_expr(lambda);
        self.lambda_effect_context = saved_ctx;

        let func_var = self.fresh();
        let effectful_arg_idxs: Vec<usize> = args
            .iter()
            .enumerate()
            .filter(|(_, a)| self.expr_is_effectful_call(a))
            .map(|(i, _)| i)
            .collect();

        if !effectful_arg_idxs.is_empty() {
            let mut arg_vars: Vec<String> = Vec::with_capacity(args.len());
            let mut pure_bindings: Vec<(String, CExpr)> = Vec::new();
            for (i, arg) in args.iter().enumerate() {
                let v = self.fresh();
                arg_vars.push(v.clone());
                if !effectful_arg_idxs.contains(&i) {
                    let ce = self.lower_expr_value(arg);
                    pure_bindings.push((v, ce));
                }
            }

            let mut call_args: Vec<CExpr> =
                arg_vars.iter().map(|v| CExpr::Var(v.clone())).collect();
            let (ev_var, ev_ce) = self.build_call_evidence(&absorbed);
            call_args.push(CExpr::Var(ev_var.clone()));
            let (rk_var, rk_ce) = self.effectful_call_return_k_binding(return_k);
            call_args.push(CExpr::Var(rk_var.clone()));

            let outer_call = CExpr::Apply(Box::new(CExpr::Var(func_var.clone())), call_args);
            let mut body = CExpr::Let(rk_var, Box::new(rk_ce), Box::new(outer_call));
            body = CExpr::Let(ev_var, Box::new(ev_ce), Box::new(body));

            for &i in effectful_arg_idxs.iter().rev() {
                let v = arg_vars[i].clone();
                let inner_k = CExpr::Fun(vec![v], Box::new(body));
                body = self.lower_expr_with_call_return_k(args[i], Some(inner_k));
            }

            let body = self.wrap_let_bindings(pure_bindings, body);
            return Some(CExpr::Let(func_var, Box::new(func_ce), Box::new(body)));
        }

        let (mut arg_vars, mut bindings) = self.lower_call_args(args, None);
        let (ev_var, ev_ce) = self.build_call_evidence(&absorbed);
        bindings.push((ev_var.clone(), ev_ce));
        arg_vars.push(ev_var);
        let (rk_var, rk_ce) = self.effectful_call_return_k_binding(return_k);
        bindings.push((rk_var.clone(), rk_ce));
        arg_vars.push(rk_var);
        let call = CExpr::Apply(
            Box::new(CExpr::Var(func_var.clone())),
            arg_vars.iter().map(|v| CExpr::Var(v.clone())).collect(),
        );
        let body = self.wrap_let_bindings(bindings, call);
        Some(CExpr::Let(func_var, Box::new(func_ce), Box::new(body)))
    }

    fn lower_generic_apply(&mut self, callee: &Expr, args: &[&Expr]) -> CExpr {
        let callee_arity = match &callee.kind {
            ExprKind::Var { name, .. } if self.resolved.contains_key(&callee.id) => {
                self.resolved_fun_info(callee.id, name).map(|f| f.arity)
            }
            _ => None,
        };

        if let Some(arity) = callee_arity
            && arity < args.len()
        {
            let (arg_vars, mut bindings) = self.lower_call_args(args, None);
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

            let extra_args: Vec<CExpr> = arg_vars[arity..]
                .iter()
                .map(|v| CExpr::Var(v.clone()))
                .collect();
            let call = CExpr::Apply(Box::new(CExpr::Var(result_var)), extra_args);
            self.wrap_let_bindings(bindings, call)
        } else {
            let func_var = self.fresh();
            let func_ce = self.lower_expr(callee);
            let (arg_vars, mut bindings) = self.lower_call_args(args, None);
            bindings.insert(0, (func_var.clone(), func_ce));
            let call = CExpr::Apply(
                Box::new(CExpr::Var(func_var)),
                arg_vars.into_iter().map(CExpr::Var).collect(),
            );
            self.wrap_let_bindings(bindings, call)
        }
    }

    fn lower_app_expr(&mut self, expr: &Expr) -> CExpr {
        if let Some((ctor_name, args)) = collect_ctor_call(expr) {
            return self.lower_ctor(ctor_name, args);
        }

        if let Some((head_expr, op_name, qualifier, args)) = collect_effect_call_expr(expr) {
            return self.lower_effect_call(
                head_expr.id,
                op_name,
                qualifier,
                &args.into_iter().cloned().collect::<Vec<_>>(),
                None,
            );
        }

        let qualified_call = collect_qualified_call(expr);
        if let Some((module, func_name, head, args)) = qualified_call {
            let qualified = format!("{}.{}", module, func_name);
            if self.is_known_constructor(&qualified) || self.is_known_constructor(func_name) {
                return self.lower_ctor(func_name, args);
            }
            if let Some(intrinsic) = self.intrinsics.get(&head.id).copied()
                && let Some(ce) = self.lower_intrinsic(intrinsic, &args)
            {
                return ce;
            }
            if let Some(call) = self.lower_resolved_fun_call(
                expr.id,
                func_name,
                head,
                &args,
                None,
                Some(&expr.span),
            ) {
                return call;
            }
            if self.resolved.contains_key(&head.id) {
                return self.lower_generic_apply(head, &args);
            }
            return self.lower_qualified_call(QualifiedCallSite {
                app_id: expr.id,
                module,
                func_name,
                head,
                args: &args,
                return_k: None,
                call_span: Some(&expr.span),
            });
        }

        let fun_call = collect_fun_call(expr);
        if let Some((_func_name, head, args)) = fun_call.as_ref()
            && let Some(intrinsic) = self.intrinsics.get(&head.id).copied()
            && let Some(ce) = self.lower_intrinsic(intrinsic, args)
        {
            return ce;
        }

        if let Some((func_name, _head, args)) = fun_call.as_ref()
            && (*func_name == "panic" || *func_name == "todo")
            && args.len() == 1
        {
            let v = self.fresh();
            let (kind, arg) = if *func_name == "todo" {
                (ErrorKind::Todo, lower_string_to_binary("not implemented"))
            } else {
                (ErrorKind::Panic, self.lower_expr_value(args[0]))
            };
            let error = self.make_error(kind, CExpr::Var(v.clone()), Some(&expr.span));
            return CExpr::Let(v, Box::new(arg), Box::new(error));
        }

        if let Some((func_name, head_expr, args)) = fun_call.as_ref()
            && self.resolved.contains_key(&head_expr.id)
            && let Some(call) = self.lower_resolved_fun_call(
                expr.id,
                func_name,
                head_expr,
                args,
                None,
                Some(&expr.span),
            )
        {
            return call;
        }

        if self.expr_is_effectful_call(expr)
            && let Some((var_name, _, args)) = fun_call.as_ref()
        {
            return self
                .lower_effectful_var_call(expr.id, var_name, args, None)
                .expect("effectful variable call should lower");
        }

        let mut callee = expr;
        let mut args_rev = Vec::new();
        while let ExprKind::App { func, arg, .. } = &callee.kind {
            args_rev.push(arg.as_ref());
            callee = func.as_ref();
        }
        args_rev.reverse();

        // Lambda-headed effectful call: `(fun x -> ...) y`. Populator tagged
        // `expr.id` with `CallEffectInfo` based on the lambda's typechecker-
        // resolved effect row. Route through `lower_lambda_head_call` so the
        // lambda is compiled as effectful (params include `_Evidence`/
        // `_ReturnK`) and the call threads evidence + return_k. Returns
        // `None` for pure-classified calls — fall through to the plain path.
        if matches!(callee.kind, ExprKind::Lambda { .. })
            && let Some(call) = self.lower_lambda_head_call(expr.id, callee, &args_rev, None)
        {
            return call;
        }

        self.lower_generic_apply(callee, &args_rev)
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
                match self.resolved.get(&expr.id).cloned() {
                    Some(ResolvedName::ImportedFun {
                        erlang_mod,
                        name: erl_name,
                        arity,
                        ..
                    }) => {
                        if arity == 0 {
                            CExpr::Call(erlang_mod.clone(), erl_name.clone(), vec![])
                        } else {
                            // Function value: emit a `make_fun` reference at
                            // the resolver-recorded arity, which already
                            // includes CPS expansion (handlers + _ReturnK)
                            // for effectful imports. The call site supplies
                            // the extra args. An eta-wrapper that captured
                            // handlers in scope would be incompatible with
                            // HOFs whose body calls the callback in raw-CPS
                            // shape (e.g. `Lib.at`'s `decoder n` lowering to
                            // `decoder(n, H, K)`).
                            CExpr::Call(
                                "erlang".to_string(),
                                "make_fun".to_string(),
                                vec![
                                    CExpr::Lit(CLit::Atom(erlang_mod.clone())),
                                    CExpr::Lit(CLit::Atom(erl_name.clone())),
                                    CExpr::Lit(CLit::Int(arity as i64)),
                                ],
                            )
                        }
                    }
                    Some(ResolvedName::LocalFun {
                        name,
                        source_module,
                        canonical_name,
                        arity,
                        effects,
                    }) => {
                        if arity == 0
                            && let Some(inlined) = self.inline_vals.get(&canonical_name).cloned()
                        {
                            inlined
                        } else {
                            let eff = if !effects.is_empty() {
                                Some(effects.clone())
                            } else {
                                self.resolved_fun_info(expr.id, &name)
                                    .map(|f| &f.effects)
                                    .cloned()
                                    .filter(|e| !e.is_empty())
                            };
                            self.lower_local_fun_ref(&name, arity, eff, source_module.as_deref())
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

            ExprKind::App { .. } => self.lower_app_expr(expr),

            ExprKind::Constructor { name, .. } => self.lower_ctor(name, vec![]),

            ExprKind::BinOp {
                op, left, right, ..
            } => self.lower_binop(op, left, right, Some(&expr.span)),

            ExprKind::UnaryMinus { expr, .. } => {
                let v = self.fresh();
                let ce = self.lower_expr_value(expr);
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
                let cond_ce = self.lower_expr_value(cond);
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
                self.lower_block_with_return_k(&stmts, None)
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
                let mut is_effectful_lambda = false;
                let effects = self
                    .lambda_effect_context
                    .take()
                    .filter(|effs| !effs.is_empty());
                let saved_evidence = self.current_evidence.clone();
                if let Some(effects) = effects {
                    // Effectful lambdas take `_Evidence` and `_ReturnK`; the
                    // body reads per-op handlers out of the evidence vector.
                    param_vars.push("_Evidence".to_string());
                    param_vars.push("_ReturnK".to_string());
                    self.current_evidence = Some(EvidenceCtx {
                        var: "_Evidence".to_string(),
                        layout: evidence::EvidenceLayout::new(effects.iter().cloned()),
                        is_open: false,
                    });
                    is_effectful_lambda = true;
                }
                let effect_return_k =
                    is_effectful_lambda.then(|| CExpr::Var("_ReturnK".to_string()));
                let body_ce = if is_effectful_lambda && !matches!(body.kind, ExprKind::Block { .. })
                {
                    self.lower_terminal_effectful_expr_with_return_k(body, effect_return_k.clone())
                } else {
                    self.lower_expr_with_installed_return_k(body, effect_return_k.clone())
                };
                self.current_evidence = saved_evidence;
                // If lambda has complex params (tuples, constructors), wrap
                // the body in a case expression for destructuring. The
                // scrutinee covers user params only — `_Evidence`/`_ReturnK`
                // (when present for effectful lambdas) stay outside the
                // destructure pattern.
                let body_ce = if !all_simple {
                    let user_param_vars: &[String] = &param_vars[..params.len()];
                    let scrutinee = if user_param_vars.len() == 1 {
                        CExpr::Var(user_param_vars[0].clone())
                    } else {
                        CExpr::Tuple(
                            user_param_vars
                                .iter()
                                .map(|v| CExpr::Var(v.clone()))
                                .collect(),
                        )
                    };
                    let pat = if params.len() == 1 {
                        self.lower_pat(
                            &params[0],
                            &self.constructor_atoms,
                            self.handler_origin_module(),
                        )
                    } else {
                        CPat::Tuple(
                            params
                                .iter()
                                .map(|p| {
                                    self.lower_pat(
                                        p,
                                        &self.constructor_atoms,
                                        self.handler_origin_module(),
                                    )
                                })
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
                let scrut_ce = self.lower_expr_value(scrutinee);
                let arms: Vec<_> = arms.iter().map(|a| a.node.clone()).collect();
                CExpr::Let(
                    scrut_var.clone(),
                    Box::new(scrut_ce),
                    Box::new(self.lower_case_expr(&scrut_var, &arms)),
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
                        // System message patterns (Down/Exit): match raw Erlang
                        // tuple shapes and convert the reason field.
                        let (pat, reason_wrapper) = if let Pat::Constructor { name, args, .. } =
                            &arm.pattern
                        {
                            if beam_interop::is_system_msg(name) && args.len() == 2 {
                                let (reason_pat, wrapper) =
                                    if let Pat::Var { name: var_name, .. } = &args[1] {
                                        let raw = self.fresh();
                                        (CPat::Var(raw.clone()), Some((core_var(var_name), raw)))
                                    } else {
                                        (
                                            self.lower_pat(
                                                &args[1],
                                                &self.constructor_atoms,
                                                self.handler_origin_module(),
                                            ),
                                            None,
                                        )
                                    };
                                let pid_pat = self.lower_pat(
                                    &args[0],
                                    &self.constructor_atoms,
                                    self.handler_origin_module(),
                                );
                                let tuple_pat = beam_interop::build_system_msg_pattern(
                                    name, pid_pat, reason_pat,
                                );
                                (tuple_pat, wrapper)
                            } else {
                                (
                                    self.lower_pat(
                                        &arm.pattern,
                                        &self.constructor_atoms,
                                        self.handler_origin_module(),
                                    ),
                                    None,
                                )
                            }
                        } else {
                            (
                                self.lower_pat(
                                    &arm.pattern,
                                    &self.constructor_atoms,
                                    self.handler_origin_module(),
                                ),
                                None,
                            )
                        };

                        let guard = arm.guard.as_ref().map(|g| self.lower_expr(g));
                        let raw_body = self.lower_expr(&arm.body);
                        let body = if let Some((user_var, raw_var)) = reason_wrapper {
                            let ctor_atoms = self.constructor_atoms.clone();
                            let conversion = beam_interop::build_exit_reason_from_erlang(
                                &raw_var,
                                &ctor_atoms,
                                &mut || self.fresh(),
                            );
                            CExpr::Let(user_var, Box::new(conversion), Box::new(raw_body))
                        } else {
                            raw_body
                        };
                        CArm { pat, guard, body }
                    })
                    .collect();

                let (timeout, timeout_body) = if let Some((t, b)) = after_clause {
                    (self.lower_expr_value(t), self.lower_expr(b))
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
                if self.is_known_constructor(&qualified) || self.is_known_constructor(name) {
                    return self.lower_ctor(name, vec![]);
                }
                // @inline val cross-module reference: substitute the lowered
                // RHS expression. Mirrors the bare-name path in `lower_var`.
                if let Some(inlined) = self.inline_vals.get(&qualified) {
                    return inlined.clone();
                }
                use super::resolve::ResolvedName;
                if let Some(resolved) = self.resolved.get(&expr.id).cloned() {
                    match resolved {
                        ResolvedName::ImportedFun {
                            erlang_mod,
                            name: erl_name,
                            arity,
                            ..
                        } => {
                            if arity == 0 {
                                CExpr::Call(erlang_mod.clone(), erl_name.clone(), vec![])
                            } else {
                                CExpr::Call(
                                    "erlang".to_string(),
                                    "make_fun".to_string(),
                                    vec![
                                        CExpr::Lit(CLit::Atom(erlang_mod.clone())),
                                        CExpr::Lit(CLit::Atom(erl_name.clone())),
                                        CExpr::Lit(CLit::Int(arity as i64)),
                                    ],
                                )
                            }
                        }
                        ResolvedName::LocalFun {
                            name,
                            source_module,
                            canonical_name,
                            arity,
                            effects,
                        } => {
                            if arity == 0
                                && let Some(inlined) =
                                    self.inline_vals.get(&canonical_name).cloned()
                            {
                                inlined
                            } else {
                                let eff = if !effects.is_empty() {
                                    Some(effects)
                                } else {
                                    self.resolved_fun_info(expr.id, &name)
                                        .map(|f| &f.effects)
                                        .cloned()
                                        .filter(|e| !e.is_empty())
                                };
                                self.lower_local_fun_ref(
                                    &name,
                                    arity,
                                    eff,
                                    source_module.as_deref(),
                                )
                            }
                        }
                    }
                } else {
                    CExpr::Var(core_var(name))
                }
            }

            ExprKind::RecordCreate { name, fields, .. } => {
                let order = self
                    .resolved_record_fields(expr.id, name)
                    .cloned()
                    .unwrap_or_default();
                let field_map: HashMap<&str, &Expr> =
                    fields.iter().map(|(n, _, e)| (n.as_str(), e)).collect();
                let mut vars: Vec<String> = Vec::new();
                let mut bindings: Vec<(String, CExpr)> = Vec::new();
                for field_name in &order {
                    let v = self.fresh();
                    let e = field_map
                        .get(field_name.as_str())
                        .expect("field missing in RecordCreate");
                    let ce = self.lower_expr_value(e);
                    vars.push(v.clone());
                    bindings.push((v, ce));
                }
                let atom = util::mangle_ctor_atom(
                    name,
                    &self.constructor_atoms,
                    self.handler_origin_module(),
                );
                let mut elems = vec![CExpr::Lit(CLit::Atom(atom))];
                elems.extend(vars.iter().map(|v| CExpr::Var(v.clone())));
                let tuple = CExpr::Tuple(elems);
                bindings.into_iter().rev().fold(tuple, |body, (var, val)| {
                    CExpr::Let(var, Box::new(val), Box::new(body))
                })
            }

            ExprKind::AnonRecordCreate { fields, .. } => {
                let names: Vec<&str> = fields.iter().map(|(n, _, _)| n.as_str()).collect();
                let tag = crate::ast::anon_record_tag(&names);
                let mut sorted_names: Vec<String> = names.iter().map(|n| n.to_string()).collect();
                sorted_names.sort();
                let field_map: HashMap<&str, &Expr> =
                    fields.iter().map(|(n, _, e)| (n.as_str(), e)).collect();
                let mut vars: Vec<String> = Vec::new();
                let mut bindings: Vec<(String, CExpr)> = Vec::new();
                for field_name in &sorted_names {
                    let v = self.fresh();
                    let e = field_map
                        .get(field_name.as_str())
                        .expect("field missing in AnonRecordCreate");
                    let ce = self.lower_expr_value(e);
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

            ExprKind::FieldAccess {
                expr,
                field,
                record_name: resolved_name,
            } => {
                let idx = resolved_name
                    .as_deref()
                    .and_then(|rname| self.record_fields.get(rname))
                    .and_then(|fields| fields.iter().position(|f| f == field))
                    .map(|pos| pos + 2) // +1 for tag, +1 for 1-based
                    .unwrap_or_else(|| {
                        panic!(
                            "codegen: could not resolve record type for field access '.{}' at node {:?} (record_name={:?})",
                            field, expr.id, resolved_name
                        )
                    }) as i64;
                let v = self.fresh();
                let ce = self.lower_expr_value(expr);
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

            ExprKind::RecordUpdate {
                record,
                fields,
                record_name: resolved_name,
            } => {
                let rec_var = self.fresh();
                let rec_ce = self.lower_expr_value(record);
                let order = resolved_name
                    .as_deref()
                    .and_then(|rname| self.record_fields.get(rname))
                    .cloned()
                    .unwrap_or_else(|| {
                        panic!(
                            "codegen: could not resolve record type for record update at node {:?} (record_name={:?})",
                            expr.id, resolved_name
                        )
                    });
                let field_map: HashMap<&str, &Expr> =
                    fields.iter().map(|(n, _, e)| (n.as_str(), e)).collect();

                let mut vars: Vec<String> = Vec::new();
                let mut bindings: Vec<(String, CExpr)> = Vec::new();
                for (pos, field_name) in order.iter().enumerate() {
                    let v = self.fresh();
                    let ce = if let Some(new_expr) = field_map.get(field_name.as_str()) {
                        self.lower_expr_value(new_expr)
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
                let dict_ce = self.lower_expr_value(dict);
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
                    let ce = self.lower_expr_value(arg);
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
            } => self
                .lower_eta_reduced_effect_op_ref(expr.id, name, qualifier.as_deref())
                .unwrap_or_else(|| {
                    self.lower_effect_call(expr.id, name, qualifier.as_deref(), args, None)
                }),

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
                let ce = self.lower_expr_value(value);
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
    fn lower_qualified_call(&mut self, site: QualifiedCallSite<'_>) -> CExpr {
        let QualifiedCallSite {
            app_id,
            module,
            func_name,
            head,
            args,
            return_k,
            call_span,
        } = site;
        let erlang_module = self
            .module_aliases
            .get(module)
            .cloned()
            .unwrap_or_else(|| module.to_lowercase());

        // Source of truth: the per-call effect map populated pre-lowering.
        let info = self.call_effects.get(&app_id);
        let (is_effectful, callee_effects_vec): (bool, Vec<String>) = match info.map(|i| &i.kind) {
            Some(super::call_effects::CallEffectKind::StaticOps { ops })
            | Some(super::call_effects::CallEffectKind::RowForwarded { static_ops: ops }) => {
                let mut effs: Vec<String> = ops.iter().map(|k| k.effect.clone()).collect();
                effs.sort();
                effs.dedup();
                (!ops.is_empty(), effs)
            }
            _ => (false, Vec::new()),
        };

        use super::resolve::ResolvedName;

        let qualified = format!("{}.{}", module, func_name);
        // Detect partial application: if the call site supplies fewer user args
        // than the declared arity, emit a closure that captures the supplied
        // args and takes the remaining ones as fresh parameters. Without this,
        // an under-applied qualified call like `String.replace "m" ""` would
        // lower to `call std_string:replace/2`, which doesn't exist.
        let total_arity = self.resolved_fun_info(head.id, &qualified).map(|f| f.arity);
        let extras = if is_effectful { 2 } else { 0 };
        if let Some(arity) = total_arity {
            let user_slots = arity.saturating_sub(extras);
            if args.len() < user_slots {
                let remaining_user = user_slots - args.len();
                let param_types = self.resolved_fun_info(head.id, &qualified).map(|f| {
                    f.param_types
                        .iter()
                        .take(args.len())
                        .cloned()
                        .collect::<Vec<_>>()
                });
                let (supplied_arg_vars, supplied_bindings) =
                    self.lower_call_args_with_expected_types(args, param_types.as_deref());
                let mut closure_params: Vec<String> = Vec::new();
                for _ in 0..remaining_user {
                    closure_params.push(self.fresh());
                }
                let mut all_args: Vec<CExpr> = supplied_arg_vars
                    .iter()
                    .map(|v| CExpr::Var(v.clone()))
                    .collect();
                all_args.extend(closure_params.iter().map(|p| CExpr::Var(p.clone())));
                if is_effectful {
                    let ev = "_Evidence".to_string();
                    closure_params.push(ev.clone());
                    all_args.push(CExpr::Var(ev));
                    let rk = "_ReturnK".to_string();
                    closure_params.push(rk.clone());
                    all_args.push(CExpr::Var(rk));
                }
                let call = match self.resolved.get(&head.id) {
                    Some(ResolvedName::ImportedFun {
                        erlang_mod, name, ..
                    }) => CExpr::Call(erlang_mod.clone(), name.clone(), all_args),
                    _ => CExpr::Call(erlang_module.clone(), func_name.to_string(), all_args),
                };
                let call = self.annotate(call, call_span);
                let lambda = CExpr::Fun(closure_params, Box::new(call));
                return self.wrap_let_bindings(supplied_bindings, lambda);
            }
        }

        let param_types = self.resolved_fun_info(head.id, &qualified).map(|f| {
            f.param_types
                .iter()
                .take(args.len())
                .cloned()
                .collect::<Vec<_>>()
        });
        let (mut arg_vars, mut bindings) =
            self.lower_call_args_with_expected_types(args, param_types.as_deref());

        // Effectful callees take `_Evidence` and `_ReturnK`.
        if is_effectful {
            let (ev_var, ev_ce) = self.build_call_evidence(&callee_effects_vec);
            bindings.push((ev_var.clone(), ev_ce));
            arg_vars.push(ev_var);
            let (rk_var, rk_ce) = self.effectful_call_return_k_binding(return_k);
            bindings.push((rk_var.clone(), rk_ce));
            arg_vars.push(rk_var);
        }

        let call_args: Vec<CExpr> = arg_vars.iter().map(|v| CExpr::Var(v.clone())).collect();
        let call = match self.resolved.get(&head.id) {
            Some(ResolvedName::ImportedFun {
                erlang_mod, name, ..
            }) => CExpr::Call(erlang_mod.clone(), name.clone(), call_args),
            _ => CExpr::Call(erlang_module, func_name.to_string(), call_args),
        };
        let call = self.annotate(call, call_span);

        self.wrap_let_bindings(bindings, call)
    }
}
