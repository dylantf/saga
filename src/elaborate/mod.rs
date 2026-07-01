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
//!
//! Shared free helpers, constants, and the `Elaborator` struct live here and are
//! re-exported to the submodules via `use super::*`.

pub(crate) use std::collections::{HashMap, HashSet};

pub(crate) use crate::ast::*;
pub(crate) use crate::token::{Span, StringKind};
pub(crate) use crate::typechecker::{
    CheckResult, ImplInfo, RecordInfo, ResolvedValue, TraitEvidence, TraitInfo, Type,
};

mod dict_params;
mod dict_resolve;
mod expr;
mod program;
mod setup;
mod tuple_show;

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
    /// Front-end resolution result for looking up canonical names by span/node id.
    pub(crate) resolution: crate::typechecker::ResolutionResult,
    /// Finalized per-node type information for resolving record names in
    /// FieldAccess/RecordUpdate.
    pub(crate) type_at_node: HashMap<crate::ast::NodeId, Type>,
    /// Record definitions, used to lower record builders in declaration order.
    pub(crate) records: HashMap<String, RecordInfo>,
    /// var_id -> source name for where-clause-bound type vars. Used by
    /// `dict_for_type`'s `Type::Var` branch to translate a polymorphic
    /// var-id back to the source name so it can find the matching where-
    /// clause dict in `current_dict_params_by_var` (which is keyed by name).
    pub(crate) where_bound_var_names: HashMap<u32, String>,
}
