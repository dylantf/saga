use std::collections::{HashMap, HashSet};

use super::{
    CheckResult, Diagnostic, EffectRow, ModuleCodegenInfo, ModuleExports, ResolutionResult, Scheme,
    Substitution, Type, TypeAliasInfo, TypeEnv, check_module, result,
};
use crate::ast::{Kind, NodeId};
use crate::token::Span;

// --- Internal types used by inference ---

#[derive(Debug, Clone)]
pub struct EffectOpSig {
    pub name: std::string::String,
    /// Canonical name of the effect this op belongs to.
    pub effect_name: std::string::String,
    pub params: Vec<(String, Type)>,
    pub return_type: Type,
    /// Effect requirements declared on this op (e.g. `spawn` needs `{Actor msg, ..e}`).
    pub needs: EffectRow,
    /// Trait constraints declared on this op, e.g. `where {a: Show}`.
    pub constraints: Vec<(String, u32, Vec<Type>)>,
}

/// Record definition info: type parameter var IDs + field types (with those vars).
/// Instantiate the type_params to fresh vars before using the field types.
#[derive(Debug, Clone)]
pub struct RecordInfo {
    /// Fresh var IDs for the record's type parameters (empty for monomorphic records)
    pub type_params: Vec<u32>,
    /// Field name -> field type (may reference vars from type_params)
    pub fields: Vec<(String, Type)>,
}

#[derive(Debug, Clone)]
pub struct EffectDefInfo {
    /// Fresh var IDs for the effect's type parameters (empty for non-parameterized effects)
    pub type_params: Vec<u32>,
    pub ops: Vec<EffectOpSig>,
    /// op_name -> span of the op declaration in the effect block (for LSP go-to-def)
    pub op_spans: HashMap<String, Span>,
    /// Which module this effect is defined in (None = main file).
    pub source_module: Option<String>,
}

/// Handler where constraint key: (effect_name, param_index).
/// Value: list of (trait_name, extra_type_arg_var_ids).
pub type HandlerWhereConstraints = HashMap<(String, usize), Vec<(String, Vec<u32>)>>;

#[derive(Debug, Clone)]
pub struct HandlerInfo {
    /// Which effects this handler handles
    pub effects: Vec<std::string::String>,
    /// Frozen return clause: (param_type, body_type). Sub-applied at register time so
    /// internal handler vars are resolved but forall vars remain free.
    pub return_type: Option<(Type, Type)>,
    /// Effects the handler's arm bodies perform (from `needs` clause).
    /// Frozen at registration; free vars are in `forall` and instantiated fresh at each usage.
    pub needs_effects: EffectRow,
    /// Type vars to instantiate fresh at each usage site (polymorphic handler params).
    pub forall: Vec<u32>,
    /// op_name -> span of the handler arm (for LSP go-to-def and with-stack)
    pub arm_spans: HashMap<String, Span>,
    /// Trait constraints from `where` clause, keyed by (effect_name, param_index).
    /// Each constraint is (trait_name, extra_type_arg_var_ids).
    /// E.g. `handler h for Store a where {a: Show}` -> {("Store", 0) -> [("Show", [])]}
    /// E.g. `handler h for State a where {a: ConvertTo b}` -> {("State", 0) -> [("ConvertTo", [b_var_id])]}
    pub where_constraints: HandlerWhereConstraints,
    /// Which module this handler is defined in (None = main file).
    pub source_module: Option<String>,
}

#[derive(Debug, Clone)]
pub struct TraitMethodEffectSig {
    pub effects: Vec<String>,
    pub is_open_row: bool,
    pub user_arity: usize,
}

#[derive(Debug, Clone)]
pub struct TraitMethodInfo {
    pub name: String,
    pub param_types: Vec<Type>,
    pub return_type: Type,
    /// Var id assigned to the trait's self type parameter inside this method's
    /// signature, if the method's user-written types reference it.
    pub trait_param_id: Option<u32>,
    /// Polymorphic scheme for the method, with constraints encoding the trait
    /// bound (and any trait-level extra type-param bounds). This is the
    /// authoritative scheme: trait methods live in their owning `TraitInfo`,
    /// not in a flat per-name table.
    pub scheme: Scheme,
    pub effect_sig: TraitMethodEffectSig,
}

#[derive(Debug, Clone)]
pub struct TraitInfo {
    /// Type parameters: first is self, rest are extras.
    /// e.g. `trait ConvertTo a b` -> [("a", Star), ("b", Star)].
    /// Symbol-kinded params are declared as `(n : Symbol)` in source.
    pub type_params: Vec<(String, Kind)>,
    pub supertraits: Vec<String>,
    pub methods: Vec<TraitMethodInfo>,
    /// `true` if the trait's self/first parameter functionally determines
    /// the remaining trait parameters. Set at registration time from a
    /// hardcoded canonical-name list (see `check_traits::FUNCTIONAL_TRAITS`).
    pub is_functional: bool,
}

#[derive(Debug, Clone, Default)]
pub struct ImplInfo {
    /// Constraints on type parameters: (trait_name, param_index)
    /// e.g. Show for List requires Show on param 0 (the element type)
    pub param_constraints: Vec<(String, usize)>,
    /// Constraints on impl pattern variables: (trait_name, pattern_var_id).
    /// This supports structured targets where a constrained variable may be
    /// nested inside the target, e.g. `Column sa na a` in a tuple element.
    pub param_constraints_by_var: Vec<(String, u32)>,
    /// Constraints on impl pattern variables with extra trait arguments:
    /// (trait_name, self_pattern_var_id, extra_type_args).
    /// Used for multi-parameter traits in structured impls, e.g.
    /// `Selectable field out` in an impl whose target contains `field`.
    pub param_constraints_by_var_with_args: Vec<(String, u32, Vec<Type>)>,
    /// Full target pattern for user-written structured impls. `None` means
    /// legacy/builtin impl matching by coarse target key only.
    pub target_pattern: Option<Type>,
    /// Extra type arguments applied to the trait, as full Types.
    /// For parameterized impls (e.g. `impl Generic (Box a) (Rep__Box a)`),
    /// these reference the impl's target type-parameter Type::Vars listed
    /// in `target_type_param_ids`, so the call-site can substitute the
    /// concrete args of the target to materialize the extras.
    /// Empty for single-param traits.
    pub trait_type_args: Vec<Type>,
    /// Fresh type variable ids assigned to the impl's `type_params` at
    /// registration time, in declaration order. Empty for monomorphic impls.
    /// Used to substitute call-site target args back into `trait_type_args`.
    pub target_type_param_ids: Vec<u32>,
    pub span: Option<Span>,
    /// Per-method effect rows this impl performs: method name -> sorted effect
    /// names. Populated in `register_impl` from each method body's inferred
    /// effects (per-method, not the impl-level `needs` union). Read at concrete
    /// trait-method call sites to propagate the selected impl's effects to the
    /// caller (the trait-effect-propagation bugfix). Travels cross-module via
    /// `ModuleExports.trait_impls`. See docs/planning/effect-polymorphic-traits.md.
    pub method_effects: HashMap<String, Vec<String>>,
}

/// Evidence that a trait constraint was resolved during typechecking.
/// Used by the elaboration pass to insert dictionary arguments.
#[derive(Debug, Clone)]
pub struct TraitEvidence {
    pub node_id: crate::ast::NodeId,
    pub trait_name: String,
    /// The concrete type that satisfied the constraint.
    /// None if resolved via a where-bound type variable (polymorphic passthrough).
    pub resolved_type: Option<(String, Vec<Type>)>,
    /// The concrete anonymous record type that satisfied the constraint.
    /// Kept separate from `resolved_type` because anonymous records have no
    /// named impl key.
    pub resolved_record_type: Option<Type>,
    /// For polymorphic evidence, the name of the type variable that was bounded.
    /// Used to select the correct dict param when multiple where-clause bounds
    /// exist for the same trait (e.g. `where {e: Show, a: Show}`).
    pub type_var_name: Option<String>,
    /// Resolved extra type arguments for multi-param traits.
    /// e.g. for `ConvertTo NOK`, this holds [Type::Con("NOK", [])].
    /// Empty for single-param traits.
    pub trait_type_args: Vec<Type>,
    /// For `KnownSymbol 'foo` constraints resolved against a concrete symbol
    /// literal: the symbol's source name (e.g. `"foo"`). The elaborator uses
    /// this to emit a symbol-flavored intrinsic instead of a normal dict
    /// lookup. `None` for all other trait evidence.
    pub resolved_symbol: Option<String>,
}

/// Warnings deferred until after inference, when substitutions are complete.
#[derive(Clone)]
pub enum PendingWarning {
    /// A non-unit value was discarded in a block (not the last statement).
    DiscardedValue { span: Span, ty: Type },
    /// A local variable binding was never referenced.
    UnusedVariable { span: Span, name: String },
    /// A module-level function was never referenced.
    UnusedFunction { span: Span, name: String },
    /// A function declares effects in its `needs` clause that it never uses.
    UnusedEffects {
        span: Span,
        fun_name: String,
        effects: Vec<String>,
    },
}

// --- Inference engine ---

#[derive(Clone)]
pub struct Checker {
    pub(crate) next_var: u32,
    pub(crate) sub: Substitution,
    pub(crate) env: TypeEnv,
    /// Constructor types from type definitions: name -> (arity, type scheme)
    pub(crate) constructors: HashMap<std::string::String, Scheme>,
    /// Record definitions: record name -> info (type params + field types)
    pub(crate) records: HashMap<std::string::String, RecordInfo>,
    /// Effect definitions: effect name -> definition info (type params + operations)
    pub(crate) effects: HashMap<std::string::String, EffectDefInfo>,
    /// Named handler definitions: handler name -> info
    pub(crate) handlers: HashMap<std::string::String, HandlerInfo>,
    /// Functions whose bodies produce handlers, so applications like
    /// `make_state 0` can preserve handler metadata such as return clauses.
    pub(crate) handler_funs: HashMap<std::string::String, HandlerInfo>,
    /// Handler info for `let h = <expr>` bindings whose RHS produces a handler.
    /// Keyed by the let pattern's NodeId so the lowerer can look up handler
    /// metadata (return clauses, effects) even after the per-function-clause
    /// `self.handlers` save/restore wipes the in-scope entry.
    pub(crate) let_binding_handlers: HashMap<crate::ast::NodeId, HandlerInfo>,
    /// Context for resume typing: when inside a handler arm, the return type of the op being handled
    pub(crate) resume_type: Option<Type>,
    /// Context for resume return typing: when inside a handler arm, the answer type of the with-expression
    pub(crate) resume_return_type: Option<Type>,
    /// Metadata for effect inference (instantiation caches, declared rows, name registries).
    pub(crate) effect_meta: EffectMeta,
    /// Effect accumulator: effects from the current scope are pushed here automatically
    /// during inference. Isolation scopes (handlers, lambdas) save/restore this field.
    pub(crate) effect_row: EffectRow,
    /// Effects absorbed during call-site HOF absorption (infer.rs App). Tracks effect
    /// names that were subtracted from the accumulator when passing callbacks to HOFs.
    /// Used by the unused-effects warning to avoid false positives: an absorbed effect
    /// was genuinely needed in scope even though it no longer appears in the accumulator.
    /// Cleared at the start of each function body in check_fun_clauses.
    pub(crate) call_site_absorbed: std::collections::HashSet<String>,
    /// Open-row trait constraints surfaced as forwarded effect row variables in
    /// the current function body: maps the constrained type variable's id to the
    /// trait that made it open-row. Populated by
    /// `emit_concrete_trait_impl_effects` when an open-row trait method is called
    /// on an abstract (where-bound) `self`, so the surfaced `..a` tail can be
    /// checked for required forwarding in `check_fun_clauses`. Cleared at the
    /// start of each function body. See docs/planning/effect-polymorphic-traits.md.
    pub(crate) trait_forward_row_vars: std::collections::HashMap<u32, String>,
    /// Trait system state (definitions, impls, constraints, where bounds).
    pub(crate) trait_state: TraitState,
    /// Per-variable record candidate narrowing for field access: var_id -> (candidate record names, span).
    /// Tracks which records are still candidates for an unresolved type variable based on
    /// the intersection of all fields accessed on it. Checked at end of each function body.
    pub(crate) field_candidates: FieldCandidates,
    /// Module system state: caches, project root, import tracking.
    pub(crate) modules: ModuleContext,
    /// Reverse map: type name -> list of (constructor_name, arity) pairs (for exhaustiveness checking)
    pub(crate) adt_variants: HashMap<std::string::String, Vec<(std::string::String, usize)>>,
    /// Type name -> number of declared type parameters (for arity checking).
    /// Absent entries (e.g. Tuple) are unchecked.
    pub(crate) type_arity: HashMap<String, usize>,
    /// Type name -> kinds of declared type parameters (positional). Used by
    /// `convert_type_expr` to know the expected kind of each argument slot
    /// in a type application. Absent entries default to all-Star.
    pub(crate) type_param_kinds: HashMap<String, Vec<Kind>>,
    /// Type aliases (canonical name -> info). Unfolded structurally during
    /// `convert_type_expr` so the rest of the typechecker never sees aliases.
    pub(crate) type_aliases: HashMap<String, TypeAliasInfo>,
    /// Per type-variable id -> declared kind. Absent entries default to
    /// `Kind::Star`. Populated when a fresh variable is minted for an
    /// `Symbol`-kinded type parameter (type, trait, impl, effect).
    pub(crate) var_kinds: HashMap<u32, Kind>,
    /// Names of type parameters in scope for the binder currently being
    /// checked (e.g. an impl whose body is mid-check). Populated by
    /// `register_impl` before walking each method body and cleared after.
    /// `convert_type_expr` consults this on a `TypeExpr::Var` miss so that
    /// inline type ascriptions like `(Proxy : Proxy n)` inside a method body
    /// resolve `n` to the impl's `n` rather than creating a fresh,
    /// unconstrained var. Without this, polymorphic `KnownSymbol n` impl
    /// bodies can't reflect the symbol — the Generic migration's library
    /// impls (`impl ToJson for Variant n a`) depend on it.
    pub(crate) outer_named_type_vars: HashMap<String, u32>,
    /// Per top-level `fun`: the (name, var_id) mapping for the type params
    /// introduced by its signature annotation. Recorded by
    /// `collect_annotations` so `check_fun_clauses` can seed
    /// `outer_named_type_vars` before checking the body — same fix as for
    /// impls, applied to functions. Without this, an ascription like
    /// `(Proxy : Proxy n)` inside a body whose signature also has `n`
    /// would mint a fresh, unrelated var.
    pub(crate) fun_type_param_vars: HashMap<String, Vec<(String, u32)>>,
    /// Name resolution map: user-visible names -> canonical names.
    pub(crate) scope_map: ScopeMap,
    /// Authoritative source-level resolution result for the current program.
    pub(crate) resolution: ResolutionResult,
    /// Evidence collected during constraint solving for the elaboration pass.
    pub(crate) evidence: Vec<TraitEvidence>,
    /// Dict params for let bindings with trait constraints.
    /// Keyed by (name, pat_node_id) to avoid collisions between same-named
    /// bindings in different scopes (e.g. multiple test bodies).
    pub(crate) let_dict_params: HashMap<(String, NodeId), result::LetDictInfo>,
    /// Diagnostics collected during block inference (for multi-error reporting).
    pub(crate) collected_diagnostics: Vec<Diagnostic>,
    /// Warnings deferred until after inference, when substitutions are complete.
    pub(crate) pending_warnings: Vec<PendingWarning>,
    /// Dedupes internal warnings when a non-canonical handler effect name is normalized.
    pub(crate) internal_handler_normalization_warnings: HashSet<String>,
    /// LSP/IDE state: type info, references, definitions, go-to-def targets.
    pub(crate) lsp: LspState,
    /// When true, function annotations without matching bodies are allowed
    /// (used for builtin stdlib modules where implementations are in Rust).
    pub(crate) allow_bodyless_annotations: bool,
    /// Set to the module name when checking a module file; None for the main file.
    pub(crate) current_module: Option<String>,
    /// Import declarations from the prelude (passed through to lowerer).
    pub prelude_imports: Vec<crate::ast::Decl>,
    /// Set to true when a `with ets_ref` handler is encountered, signalling
    /// that the `saga_ref_store` ETS table must be created at startup.
    pub(crate) needs_ets_ref_table: bool,
    /// Set to true when a `with beam_vec` handler is encountered, signalling
    /// that the `saga_vec_store` ETS table must be created at startup.
    pub(crate) needs_vec_table: bool,
}

/// Maps user-visible name forms to canonical (module-qualified) names.
///
/// When `import Std.List as List exposing (map)` is processed, the ScopeMap gets:
///   values["Std.List.map"] = "Std.List.map"   (canonical)
///   values["List.map"]     = "Std.List.map"   (aliased)
///   values["map"]          = "Std.List.map"   (bare, because exposed)
///
/// This allows each binding to be stored once in the env under its canonical name,
/// with the ScopeMap handling all user-facing name form resolution.
///
/// Canonical names are dot-joined: `Module.Item` for module-level items,
/// `Module.Trait.method` for trait methods, `Module.Effect.op` for effect ops.
/// Use [`canonical_join`] to build them from parts so the convention stays
/// in one place.
#[derive(Debug, Clone, Default)]
pub struct ScopeMap {
    /// User-visible name -> canonical name for value bindings (functions, let bindings).
    pub values: HashMap<String, String>,
    /// User-visible name -> canonical name for handlers.
    pub handlers: HashMap<String, String>,
    /// User-visible name -> canonical (bare) name for type names.
    pub types: HashMap<String, String>,
    /// User-visible name -> canonical name for constructors.
    pub constructors: HashMap<String, String>,
    /// User-visible name -> canonical name for effects.
    pub effects: HashMap<String, String>,
    /// Bare effect operation name -> canonical effects that make that op visible.
    pub effect_ops: HashMap<String, HashSet<String>>,
    /// User-visible name -> canonical name for traits.
    pub traits: HashMap<String, String>,
    /// Bare trait method name -> canonical traits that make that method visible.
    pub trait_methods: HashMap<String, HashSet<String>>,
    /// Canonical name -> source module name (e.g. "Std.List.map" -> "Std.List").
    /// Used by LSP to determine import origins without a separate parallel map.
    pub origins: HashMap<String, String>,
}

impl ScopeMap {
    pub fn resolve_value(&self, name: &str) -> Option<&str> {
        self.values.get(name).map(|s| s.as_str())
    }

    pub fn resolve_handler(&self, name: &str) -> Option<&str> {
        self.handlers.get(name).map(|s| s.as_str())
    }

    pub fn resolve_type(&self, name: &str) -> Option<&str> {
        self.types.get(name).map(|s| s.as_str())
    }

    pub fn resolve_constructor(&self, name: &str) -> Option<&str> {
        self.constructors.get(name).map(|s| s.as_str())
    }

    /// Find the shortest user-visible alias that maps to `canonical` in the given namespace.
    pub fn shortest_alias<'a>(
        &'a self,
        canonical: &str,
        namespace: &'a HashMap<String, String>,
    ) -> Option<&'a str> {
        namespace
            .iter()
            .filter(|(_, c)| c.as_str() == canonical)
            .map(|(alias, _)| alias.as_str())
            .min_by_key(|a| a.len())
    }

    pub fn resolve_effect(&self, name: &str) -> Option<&str> {
        self.effects.get(name).map(|s| s.as_str())
    }

    pub fn register_effect_op(&mut self, op_name: &str, canonical_effect: &str) {
        self.effect_ops
            .entry(op_name.to_string())
            .or_default()
            .insert(canonical_effect.to_string());
    }

    pub fn register_effect_ops<'a>(
        &mut self,
        canonical_effect: &str,
        op_names: impl IntoIterator<Item = &'a str>,
    ) {
        for op_name in op_names {
            self.register_effect_op(op_name, canonical_effect);
        }
    }

    pub fn resolve_trait(&self, name: &str) -> Option<&str> {
        self.traits.get(name).map(|s| s.as_str())
    }

    pub fn register_trait_method(&mut self, method_name: &str, canonical_trait: &str) {
        self.trait_methods
            .entry(method_name.to_string())
            .or_default()
            .insert(canonical_trait.to_string());
    }

    pub fn register_trait_methods<'a>(
        &mut self,
        canonical_trait: &str,
        method_names: impl IntoIterator<Item = &'a str>,
    ) {
        for method_name in method_names {
            self.register_trait_method(method_name, canonical_trait);
        }
    }

    /// Get the source module for a user-visible name, checking all name kinds.
    pub fn origin_of(&self, name: &str) -> Option<&str> {
        // Resolve the user-visible name to canonical, then look up origin
        let canonical = self
            .values
            .get(name)
            .or_else(|| self.handlers.get(name))
            .or_else(|| self.constructors.get(name))
            .or_else(|| self.effects.get(name))
            .or_else(|| self.traits.get(name))
            .or_else(|| self.types.get(name));
        if let Some(canon) = canonical {
            self.origins.get(canon).map(|s| s.as_str())
        } else {
            // Name might already be canonical
            self.origins.get(name).map(|s| s.as_str())
        }
    }

    /// Check if a user-visible name is an import (has an origin in scope_map).
    pub fn is_import(&self, name: &str) -> bool {
        self.origin_of(name).is_some()
    }

    /// Register a name under its canonical and (optionally) aliased qualified forms.
    ///
    /// Inserts `"Module.Name" -> "Module.Name"` (canonical) and, when the alias
    /// prefix differs from the module name, `"Alias.Name" -> "Module.Name"`.
    pub fn register_qualified(
        map: &mut HashMap<String, String>,
        module_name: &str,
        prefix: &str,
        bare_name: &str,
    ) {
        let canonical = format!("{}.{}", module_name, bare_name);
        map.entry(canonical.clone())
            .or_insert_with(|| canonical.clone());
        if prefix != module_name {
            let aliased = format!("{}.{}", prefix, bare_name);
            map.entry(aliased).or_insert_with(|| canonical);
        }
    }

    /// Merge another scope_map into this one.
    ///
    /// Most namespaces are first-insert-wins. Effect op and trait method
    /// visibility unions candidates so overlapping exposed names remain
    /// ambiguous.
    pub fn merge(&mut self, other: &ScopeMap) {
        for (k, v) in &other.values {
            self.values.entry(k.clone()).or_insert_with(|| v.clone());
        }
        for (k, v) in &other.handlers {
            self.handlers.entry(k.clone()).or_insert_with(|| v.clone());
        }
        for (k, v) in &other.types {
            self.types.entry(k.clone()).or_insert_with(|| v.clone());
        }
        for (k, v) in &other.constructors {
            self.constructors
                .entry(k.clone())
                .or_insert_with(|| v.clone());
        }
        for (k, v) in &other.effects {
            self.effects.entry(k.clone()).or_insert_with(|| v.clone());
        }
        for (op_name, effects) in &other.effect_ops {
            self.effect_ops
                .entry(op_name.clone())
                .or_default()
                .extend(effects.iter().cloned());
        }
        for (k, v) in &other.traits {
            self.traits.entry(k.clone()).or_insert_with(|| v.clone());
        }
        for (method_name, traits) in &other.trait_methods {
            self.trait_methods
                .entry(method_name.clone())
                .or_default()
                .extend(traits.iter().cloned());
        }
        for (k, v) in &other.origins {
            self.origins.entry(k.clone()).or_insert_with(|| v.clone());
        }
    }
}

/// Trait system state: definitions, impl registry, deferred constraints, where bounds.
#[derive(Clone, Default)]
pub(crate) struct TraitState {
    /// Trait definitions: trait name -> info.
    pub traits: HashMap<String, TraitInfo>,
    /// Impl registry: (trait_name, trait_type_args, target_type) -> impl info.
    pub impls: HashMap<(String, Vec<String>, String), ImplInfo>,
    /// Pending trait constraints to check: (trait_name, trait_type_arg_types, self_type, span, node_id).
    /// trait_type_arg_types is empty for single-param traits.
    pub pending_constraints: Vec<(String, Vec<Type>, Type, Span, crate::ast::NodeId)>,
    /// Constraint NodeIds that originated inside a synthesized routed-derive impl.
    /// Populated in `register_impl` by snapshotting constraints added during the
    /// impl's body check. Used by `check_pending_constraints` to rewrite failure
    /// diagnostics so they point at the user's deriving clause and name the
    /// user-facing trait + type, instead of mentioning building-block types from
    /// the synthesized body. See the [crate::ast::RoutedDeriveInfo] marker on
    /// `Decl::ImplDef` set by `derive_routed`.
    pub routed_constraint_origins: HashMap<crate::ast::NodeId, crate::ast::RoutedDeriveInfo>,
    /// Where clause bounds: var_id -> set of trait names assumed satisfied.
    pub where_bounds: HashMap<u32, HashSet<String>>,
    /// Extra type arguments for multi-parameter where bounds, keyed by
    /// (var_id, trait_name). For `where {a: ConvertTo b}` this stores `b`.
    pub where_bound_trait_args: HashMap<(u32, String), Vec<Type>>,
    /// Reverse map from type var ID to original type parameter name (for polymorphic evidence).
    pub where_bound_var_names: HashMap<u32, String>,
}

/// Metadata for effect inference: instantiation caches and name registries.
/// Effect accumulation lives on Checker.effect_row.
#[derive(Clone, Default)]
pub(crate) struct EffectMeta {
    /// Per-scope cache of instantiated effect type params: effect name -> mapping
    /// from original var IDs to fresh vars. Ensures all ops from the same effect
    /// share type params within a function scope.
    pub type_param_cache: HashMap<String, HashMap<u32, Type>>,
    /// Registry of locally defined function names. Not used for effect tracking
    /// (the accumulator + absorption handle that). Only read at the CheckResult
    /// boundary to build fun_effects for codegen. See docs/remove-known-funs-registry.md.
    pub known_funs: HashSet<String>,
    /// Annotation-provided effect type constraints: fn name -> [(effect_name, [concrete types])].
    pub fun_type_constraints: HashMap<String, Vec<(String, Vec<Type>)>>,
    /// Registry of let bindings with deferred effects, keyed by binding name and
    /// recording the effects observed at registration time.
    ///
    /// Captured at the binding's definition site (not looked up post-hoc in the
    /// global env) so a local `let foo = pure_lambda` that shadows a top-level
    /// effectful `foo` records the local lambda's effects (often empty), not
    /// the top-level fn's. Only read at the CheckResult boundary for codegen.
    pub known_let_bindings: HashMap<String, Vec<String>>,
}

/// State accumulated during typechecking for IDE/LSP features: hover types,
/// go-to-definition, find-all-references, unused variable detection.
#[derive(Clone, Default)]
pub(crate) struct LspState {
    /// Per-node type information for Expr nodes (LSP hover, go-to-def, etc.).
    /// Types are stored unresolved (may contain type variables); apply `sub`
    /// at lookup time to get the final resolved type.
    pub type_at_node: HashMap<crate::ast::NodeId, Type>,
    /// Per-span type information for Pat bindings.
    pub type_at_span: HashMap<Span, Type>,
    /// Resolution map: usage NodeId -> definition NodeId (for find-all-references).
    pub references: HashMap<crate::ast::NodeId, crate::ast::NodeId>,
    /// NodeId -> Span map for all recorded expression nodes (for resolving NodeIds to locations).
    pub node_spans: HashMap<crate::ast::NodeId, Span>,
    /// Constructor definition NodeIds: constructor name -> NodeId of the TypeConstructor/RecordDef.
    pub constructor_def_ids: HashMap<String, crate::ast::NodeId>,
    /// All variable/param definitions: (NodeId, name, span) for unused variable detection.
    pub definitions: Vec<(crate::ast::NodeId, String, Span)>,
    /// Top-level function definitions: (NodeId, name, span, is_public) for unused function detection.
    pub fun_definitions: Vec<(crate::ast::NodeId, String, Span, bool)>,
    /// Stack of (op_name -> (arm_span, source_module)) maps for nested `with` expressions.
    /// Innermost handler is last. Used to record which arm handles each effect call.
    pub with_arm_stacks: Vec<HashMap<String, (Span, Option<String>)>>,
    /// Maps effect call span -> (handler arm span, source module) (for LSP go-to-def, level 1).
    pub effect_call_targets: HashMap<Span, (Span, Option<String>)>,
    /// Maps handler arm span -> (effect op definition span, source module) (for LSP go-to-def, level 2).
    pub handler_arm_targets: HashMap<Span, (Span, Option<String>)>,
    /// Type/effect name references: (span, name) pairs for all type names in annotations,
    /// type expressions, effect refs, etc. Used for find-references on type/effect names.
    pub type_references: Vec<(Span, String)>,
    /// Doc comments from imported declarations: name -> doc lines.
    pub imported_docs: HashMap<String, Vec<String>>,
}

/// Module system state: caches, project root, and import tracking.
#[derive(Clone, Default)]
pub struct ModuleContext {
    /// Project root for resolving imports. None = script mode.
    pub(crate) project_root: Option<std::path::PathBuf>,
    /// Map from declared module name to file path. Built by scanning the project at startup.
    pub map: Option<check_module::ModuleMap>,
    /// Cached import graph for `map`. Invalidated whenever the module map is replaced or mutated.
    pub(crate) module_graph: Option<check_module::ModuleGraph>,
    /// Per-module visibility metadata for dependency modules. Used to identify
    /// which package a module belongs to so internal cross-imports within a
    /// dependency can resolve. Local project modules have no entry.
    pub visibility: Option<check_module::ModuleVisibilityMap>,
    /// Private (non-`expose`d) modules of each dependency, keyed by the
    /// package's `lib.module` name. Looked up as a fallback when an importer
    /// from the same package references a module not in the global `map`.
    /// Kept out of the global map so private module names don't collide with
    /// other packages or the consumer's own modules.
    pub private_modules: Option<HashMap<String, check_module::ModuleMap>>,
    /// Cache of already-typechecked modules: module name -> all public exports.
    pub(crate) exports: HashMap<String, ModuleExports>,
    /// Cache of codegen-relevant info for each typechecked module.
    pub codegen_info: HashMap<String, ModuleCodegenInfo>,
    /// Cache of parsed programs for each typechecked module.
    pub programs: HashMap<String, crate::ast::Program>,
    /// Cache of per-module CheckResults for elaboration (avoids re-typechecking).
    pub check_results: HashMap<String, CheckResult>,
    /// Cached checker state after prelude has been loaded.
    pub(crate) prelude_snapshot: Option<Box<Checker>>,
    /// Trait impls from Std.saga (base layer). Shared with builtin module checkers
    /// so they can resolve constraints on primitives (e.g. Ord for Int).
    pub(crate) base_trait_impls: HashMap<(String, Vec<String>, String), ImplInfo>,
    /// Modules currently being typechecked (cycle detection).
    pub(crate) loading: HashSet<String>,
    /// Pre-inference headers for the SCC currently being checked. While this
    /// is set, imports of modules in the map are resolved from headers instead
    /// of recursively loading the module.
    pub(crate) active_scc_headers: Option<HashMap<String, check_module::ModuleHeader>>,
    /// Modules whose canonical exports have been registered into this
    /// checker's `env`/`constructors`/`effects`/etc. Tracks both explicit
    /// imports (via `inject_exports`) and auto-loaded canonical references
    /// (via `register_module_canonical_exports` directly). Used to skip
    /// redundant re-registration.
    pub(crate) registered_canonical: HashSet<String>,
}

/// Per-variable record candidate narrowing: var_id -> (candidate record names, span).
pub(crate) type FieldCandidates = HashMap<u32, (Vec<String>, Span)>;

/// Snapshot of inference state saved when entering an isolated scope (function
/// body, lambda, with-expression, handler arm) and restored on exit.
pub(crate) struct InferScope {
    pub(crate) effect_cache: HashMap<String, HashMap<u32, Type>>,
    pub(crate) field_candidates: FieldCandidates,
    pub(crate) resume_type: Option<Type>,
    pub(crate) resume_return_type: Option<Type>,
}

/// What accumulated inside an InferScope while it was active.
pub(crate) struct InferScopeResult {
    pub effect_cache: HashMap<String, HashMap<u32, Type>>,
    pub field_candidates: FieldCandidates,
}
