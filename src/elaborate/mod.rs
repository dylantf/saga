//! Elaboration pass: transforms the AST to make trait dictionary passing explicit.
//!
//! Runs after typechecking, before lowering to Core Erlang. Uses the typechecker's
//! evidence (resolved trait constraints) to:
//! - Emit dictionary constructor functions for each trait impl
//! - Replace trait method calls with dictionary lookups
//! - Add dictionary parameters to functions with where clauses
//! - Insert dictionary arguments at call sites
//!
//! The `impl Elaborator` is split across submodules by concern:
//! - `setup`        — name resolution helpers and `Elaborator::new` registration
//! - `dict_params`  — computing/threading dictionary parameters (where clauses, ops)
//! - `program`      — top-level program elaboration
//! - `expr`         — expression and handler elaboration, method desugaring
//! - `dict_resolve` — resolving a concrete dictionary for a trait at a use site
//! - `anon_record`  — building `Generic` dictionaries for anonymous records/tuples
//!
//! Shared free helpers, constants, and the `Elaborator` struct live here and are
//! re-exported to the submodules via `use super::*`.

pub(crate) use std::collections::{HashMap, HashSet};

pub(crate) use crate::ast::*;
pub(crate) use crate::token::{Span, StringKind};
pub(crate) use crate::typechecker::{
    CheckResult, ImplInfo, KNOWN_SYMBOL_TRAIT, ResolvedValue, TraitEvidence, TraitInfo, Type,
    WhereAppDictParam,
};

mod anon_record;
mod dict_params;
mod dict_resolve;
mod expr;
mod program;
mod setup;

pub(crate) fn bare_segment(name: &str) -> String {
    name.rsplit('.').next().unwrap_or(name).to_string()
}

/// Disambiguating suffix for a dictionary parameter's variable component.
///
/// A trait with a multi-variable-determinant fundep (e.g.
/// `TableScope table mode cols | table mode -> cols`) can be required twice on
/// the *same* self variable, differing only in a determinant extra
/// (`table Required -> ...` vs `table Optional -> ...`). The two dicts would
/// otherwise collapse to the same `__dict_<Trait>_<var>` name and collide in
/// codegen. We append the concrete determinant-extra heads (`_Required`) so the
/// names stay distinct. Returns "" for traits without such a fundep, or when a
/// determinant extra isn't a concrete head — keeping existing names unchanged
/// and definition/use sites consistent.
pub(crate) fn dict_var_suffix_from_types(
    traits: &HashMap<String, TraitInfo>,
    trait_name: &str,
    extras: &[Type],
) -> String {
    let Some(fundep) = traits.get(trait_name).and_then(|i| i.fundep.as_ref()) else {
        return String::new();
    };
    let positions = fundep.determinant_extra_positions();
    if positions.is_empty() {
        return String::new();
    }
    let mut parts = Vec::new();
    for p in positions {
        match extras.get(p) {
            Some(Type::Con(name, _)) => parts.push(bare_segment(name)),
            Some(Type::Symbol(s)) => parts.push(bare_segment(s)),
            _ => return String::new(),
        }
    }
    format!("_{}", parts.join("_"))
}

/// `dict_var_suffix_from_types` for the where-clause source form, where the
/// determinant extras are `TypeExpr`s rather than resolved `Type`s. Renders the
/// same bare heads so it agrees with the use-site (`Type`-based) computation.
pub(crate) fn dict_var_suffix_from_type_exprs(
    traits: &HashMap<String, TraitInfo>,
    trait_name: &str,
    extras: &[TypeExpr],
) -> String {
    let Some(fundep) = traits.get(trait_name).and_then(|i| i.fundep.as_ref()) else {
        return String::new();
    };
    let positions = fundep.determinant_extra_positions();
    if positions.is_empty() {
        return String::new();
    }
    let mut parts = Vec::new();
    for p in positions {
        match extras.get(p) {
            Some(TypeExpr::Named { name, .. }) => parts.push(bare_segment(name)),
            Some(te @ TypeExpr::App { .. }) => match te.head_name() {
                Some(h) => parts.push(bare_segment(h)),
                None => return String::new(),
            },
            Some(TypeExpr::Symbol { name, .. }) => parts.push(bare_segment(name)),
            _ => return String::new(),
        }
    }
    format!("_{}", parts.join("_"))
}

/// Only invoke the symbol-intrinsic lambda fast-path for the `KnownSymbol`
/// trait's own `symbol_name` method. Without this guard, a `to_json` call
/// whose node also carries KnownSymbol evidence (from a parameterized
/// `impl ToJson for Labeled n a where {n : KnownSymbol}` impl) would be
/// rewritten to a symbol-name lookup, silently dropping the real dispatch.
pub(crate) fn is_known_symbol_trait(trait_name: &str) -> bool {
    trait_name == KNOWN_SYMBOL_TRAIT
}

pub(crate) fn is_generic_trait(trait_name: &str) -> bool {
    matches!(trait_name, "Generic" | "Std.Generic.Generic")
}

pub(crate) fn generic_ctor(name: &str) -> String {
    format!("Std.Generic.{name}")
}

pub(crate) fn match_type_pattern(
    pattern: &Type,
    actual: &Type,
    subst: &mut HashMap<u32, Type>,
) -> bool {
    match (pattern, actual) {
        (Type::Var(id), actual) => match subst.get(id).cloned() {
            Some(existing) => existing == *actual,
            None => {
                subst.insert(*id, actual.clone());
                true
            }
        },
        (Type::Con(pn, pa), Type::Con(an, aa)) => {
            pn == an
                && pa.len() == aa.len()
                && pa
                    .iter()
                    .zip(aa.iter())
                    .all(|(p, a)| match_type_pattern(p, a, subst))
        }
        (Type::Symbol(a), Type::Symbol(b)) => a == b,
        _ => false,
    }
}

pub(crate) fn substitute_pattern_vars(ty: &Type, subst: &HashMap<u32, Type>) -> Type {
    match ty {
        Type::Var(id) => subst.get(id).cloned().unwrap_or(Type::Var(*id)),
        Type::Con(name, args) => Type::Con(
            name.clone(),
            args.iter()
                .map(|arg| substitute_pattern_vars(arg, subst))
                .collect(),
        ),
        Type::Fun(a, b, row) => Type::Fun(
            Box::new(substitute_pattern_vars(a, subst)),
            Box::new(substitute_pattern_vars(b, subst)),
            row.clone(),
        ),
        Type::Record(fields) => Type::Record(
            fields
                .iter()
                .map(|(name, ty)| (name.clone(), substitute_pattern_vars(ty, subst)))
                .collect(),
        ),
        other => other.clone(),
    }
}

pub(crate) fn trait_type_arg_names(args: &[Type]) -> Vec<String> {
    args.iter()
        .filter_map(|ty| match ty {
            Type::Con(name, _) => Some(name.clone()),
            _ => None,
        })
        .collect()
}

pub(crate) const SHOW: &str = "Std.Base.Show";
pub(crate) const DEBUG: &str = "Std.Base.Debug";
pub(crate) const ORD: &str = "Std.Base.Ord";
pub(crate) const SEMIGROUP: &str = "Std.Base.Semigroup";

/// Impl key: (trait_name, trait_type_args, target_type).
/// e.g. ("ConvertTo", ["NOK"], "USD") or ("Show", [], "Int").
pub(crate) type ImplKey = (String, Vec<String>, String);

/// The where-app dict param the elaborator threads into conditional dict
/// constructors. Defined on the typechecker side ([`WhereAppDictParam`]) so the
/// resolved form can ride along on `ImplInfo` for imported impls; aliased here
/// for the elaborator's local computation and call-site consumption.
pub(crate) type ImplWhereAppDictParam = WhereAppDictParam;

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

pub(crate) struct Elaborator {
    /// method_name -> (trait_name, method_index_in_trait)
    pub(crate) trait_methods: HashMap<String, (String, usize)>,
    /// fun_name -> [(trait_name, type_var_name)] from where clauses
    pub(crate) fun_dict_params: HashMap<String, Vec<(String, String)>>,
    /// handler_name -> [(trait_name, type_var_name)] from handler where clauses
    pub(crate) handler_dict_params: HashMap<String, Vec<(String, String)>>,
    /// (canonical_effect_name, op_name) -> [(trait_name, type_var_name)] from the
    /// operation's own `where` clause (e.g. `set : a -> Unit where {a: PgType}`).
    /// Used to (a) set up dict params when elaborating the handler arm body and
    /// (b) append dict arguments at `op!` call sites, so the dict for the op's
    /// trait constraint is threaded per call from caller to handler.
    pub(crate) op_dict_params: HashMap<(String, String), Vec<(String, String)>>,
    /// impl key -> dict constructor name
    pub(crate) dict_names: HashMap<ImplKey, String>,
    /// impl key -> ordered list of (constraint_trait, param_index) for dict params.
    /// Used to pass the correct sub-dicts when building parameterized dicts.
    pub(crate) impl_dict_params: HashMap<ImplKey, Vec<(String, usize)>>,
    /// impl key -> ordered list of fresh/existential where-app constraints that
    /// become dict params but are not tied directly to an impl type parameter.
    pub(crate) impl_where_app_dict_params: HashMap<ImplKey, Vec<ImplWhereAppDictParam>>,
    /// impl key -> registered impl info, including structured target pattern metadata.
    pub(crate) impl_infos: HashMap<ImplKey, ImplInfo>,
    /// trait_name -> TraitInfo
    pub(crate) traits: HashMap<String, TraitInfo>,
    /// Evidence from typechecking: node_id -> Vec<TraitEvidence>
    pub(crate) evidence_by_node: HashMap<crate::ast::NodeId, Vec<TraitEvidence>>,
    /// The name of the function currently being elaborated (for dict param lookup)
    pub(crate) current_fun: Option<String>,
    /// The canonical trait whose impl method body is currently being elaborated.
    /// Synthetic routed derives may call their own trait method even when that
    /// method is not imported as a bare value in the user's module.
    pub(crate) current_impl_trait: Option<String>,
    /// Current function's dict param names: trait_name -> param_name
    pub(crate) current_dict_params: HashMap<String, String>,
    /// Current function's dict params keyed by (trait_name, type_var_suffix):
    /// e.g. ("Show", "v42") -> "__dict_Show_v42"
    pub(crate) current_dict_params_by_var: HashMap<(String, String), String>,
    /// Erlang module name for this module (e.g. "animals"), used for dict name qualification
    pub(crate) erlang_module: String,
    /// Arity of let-bound values with trait constraints (for eta-expansion)
    pub(crate) let_binding_arities: HashMap<String, usize>,
    /// Pat node IDs of let bindings that actually need dict wrapping.
    /// Used to avoid wrapping same-named bindings in different scopes.
    pub(crate) let_dict_pat_ids: HashMap<String, HashSet<crate::ast::NodeId>>,
    /// Scope map values for canonical name bridging (user name -> canonical)
    pub(crate) scope_map_values: HashMap<String, String>,
    /// Scope map effects for canonical name bridging (user name -> canonical
    /// effect name, e.g. `"Fail"` -> `"Std.Fail.Fail"`).
    pub(crate) scope_map_effects: HashMap<String, String>,
    /// Record name -> declared field order.
    pub(crate) record_fields: HashMap<String, Vec<String>>,
    /// Front-end resolution result for looking up canonical names by span/node id.
    pub(crate) resolution: crate::typechecker::ResolutionResult,
    /// Finalized per-node type information for resolving record names in
    /// FieldAccess/RecordUpdate.
    pub(crate) type_at_node: HashMap<crate::ast::NodeId, Type>,
    /// var_id -> source name for where-clause-bound type vars. Used by
    /// `dict_for_type`'s `Type::Var` branch to translate a polymorphic
    /// var-id back to the source name so it can find the matching where-
    /// clause dict in `current_dict_params_by_var` (which is keyed by name).
    pub(crate) where_bound_var_names: HashMap<u32, String>,
}
