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
use crate::typechecker::{
    CheckResult, ImplInfo, KNOWN_SYMBOL_TRAIT, ResolvedValue, TraitEvidence, TraitInfo, Type,
};

fn bare_segment(name: &str) -> String {
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
fn dict_var_suffix_from_types(
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
fn dict_var_suffix_from_type_exprs(
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
fn is_known_symbol_trait(trait_name: &str) -> bool {
    trait_name == KNOWN_SYMBOL_TRAIT
}

fn is_generic_trait(trait_name: &str) -> bool {
    matches!(trait_name, "Generic" | "Std.Generic.Generic")
}

fn generic_ctor(name: &str) -> String {
    format!("Std.Generic.{name}")
}

fn match_type_pattern(pattern: &Type, actual: &Type, subst: &mut HashMap<u32, Type>) -> bool {
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

fn substitute_pattern_vars(ty: &Type, subst: &HashMap<u32, Type>) -> Type {
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

fn trait_type_arg_names(args: &[Type]) -> Vec<String> {
    args.iter()
        .filter_map(|ty| match ty {
            Type::Con(name, _) => Some(name.clone()),
            _ => None,
        })
        .collect()
}

const SHOW: &str = "Std.Base.Show";
const DEBUG: &str = "Std.Base.Debug";
const ORD: &str = "Std.Base.Ord";
const SEMIGROUP: &str = "Std.Base.Semigroup";

/// Impl key: (trait_name, trait_type_args, target_type).
/// e.g. ("ConvertTo", ["NOK"], "USD") or ("Show", [], "Int").
type ImplKey = (String, Vec<String>, String);

#[derive(Clone, Debug)]
struct ImplWhereAppDictParam {
    trait_name: String,
    trait_type_args: Vec<Type>,
    self_type: Type,
}

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
    /// (canonical_effect_name, op_name) -> [(trait_name, type_var_name)] from the
    /// operation's own `where` clause (e.g. `set : a -> Unit where {a: PgType}`).
    /// Used to (a) set up dict params when elaborating the handler arm body and
    /// (b) append dict arguments at `op!` call sites, so the dict for the op's
    /// trait constraint is threaded per call from caller to handler.
    op_dict_params: HashMap<(String, String), Vec<(String, String)>>,
    /// impl key -> dict constructor name
    dict_names: HashMap<ImplKey, String>,
    /// impl key -> ordered list of (constraint_trait, param_index) for dict params.
    /// Used to pass the correct sub-dicts when building parameterized dicts.
    impl_dict_params: HashMap<ImplKey, Vec<(String, usize)>>,
    /// impl key -> ordered list of fresh/existential where-app constraints that
    /// become dict params but are not tied directly to an impl type parameter.
    impl_where_app_dict_params: HashMap<ImplKey, Vec<ImplWhereAppDictParam>>,
    /// impl key -> registered impl info, including structured target pattern metadata.
    impl_infos: HashMap<ImplKey, ImplInfo>,
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
    /// Scope map effects for canonical name bridging (user name -> canonical
    /// effect name, e.g. `"Fail"` -> `"Std.Fail.Fail"`).
    scope_map_effects: HashMap<String, String>,
    /// Front-end resolution result for looking up canonical names by span/node id.
    resolution: crate::typechecker::ResolutionResult,
    /// Finalized per-node type information for resolving record names in
    /// FieldAccess/RecordUpdate.
    type_at_node: HashMap<crate::ast::NodeId, Type>,
    /// var_id -> source name for where-clause-bound type vars. Used by
    /// `dict_for_type`'s `Type::Var` branch to translate a polymorphic
    /// var-id back to the source name so it can find the matching where-
    /// clause dict in `current_dict_params_by_var` (which is keyed by name).
    where_bound_var_names: HashMap<u32, String>,
}

impl Elaborator {
    fn resolved_trait_name(&self, id: crate::ast::NodeId, source: &str) -> String {
        self.resolution.trait_ref(id).unwrap_or(source).to_string()
    }

    fn resolved_impl_trait_name(&self, id: crate::ast::NodeId, source: &str) -> String {
        self.resolution
            .impl_trait_ref(id)
            .or_else(|| self.resolution.trait_ref(id))
            .unwrap_or(source)
            .to_string()
    }

    fn resolved_impl_target_type(&self, id: crate::ast::NodeId, source: &str) -> String {
        self.resolution
            .impl_target_type_ref(id)
            .unwrap_or(source)
            .to_string()
    }

    fn resolved_type_name(&self, id: crate::ast::NodeId, source: &str) -> String {
        self.resolution.type_ref(id).unwrap_or(source).to_string()
    }

    fn resolved_global_value_name(&self, id: crate::ast::NodeId) -> Option<&str> {
        match self.resolution.value(id) {
            Some(ResolvedValue::Global { lookup_name }) => Some(lookup_name.as_str()),
            _ => None,
        }
    }

    fn fun_dict_params_for_callee(
        &self,
        source_name: &str,
        node_id: crate::ast::NodeId,
    ) -> Option<Vec<(String, String)>> {
        // A reference that resolves to a local binding is NOT a top-level
        // dict-parameterized function, even when it shares a name with one
        // (e.g. a parameter `value` shadowing a global
        // `value : a -> _ where {a: Pg}`). Matching it by bare name would wrap
        // the local with dict arguments and apply it like a function at runtime
        // (`apply 18(dict)` → `{badfun,18}`). The only locals that legitimately
        // carry call-site dicts are eta-expanded dict-parameterized
        // let-bindings, which register their name in `let_dict_pat_ids`.
        if matches!(
            self.resolution.value(node_id),
            Some(ResolvedValue::Local { .. })
        ) && !self.let_dict_pat_ids.contains_key(source_name)
        {
            return None;
        }
        if let Some(params) = self.fun_dict_params.get(source_name).cloned() {
            return Some(params);
        }
        if let Some(resolved_name) = self.resolved_global_value_name(node_id)
            && let Some(params) = self.fun_dict_params.get(resolved_name).cloned()
        {
            return Some(params);
        }
        if let Some(canonical) = self.scope_map_values.get(source_name)
            && let Some(params) = self.fun_dict_params.get(canonical).cloned()
        {
            return Some(params);
        }
        None
    }

    /// Resolve trait type args via the resolution map. For App heads (e.g.
    /// `Rep__Box a`), uses the head name — only the head identifies the impl
    /// for dict-name purposes.
    fn resolved_trait_type_args(&self, args: &[crate::ast::TypeExpr]) -> Vec<String> {
        args.iter()
            .map(|te| {
                let head = te.head_name().unwrap_or("");
                self.resolved_type_name(te.head_id().unwrap_or(te.id()), head)
            })
            .collect()
    }

    fn impl_target_key(
        &self,
        canonical_target: &str,
        target_type_expr: Option<&crate::ast::TypeExpr>,
        type_params: &[crate::ast::TypeParam],
    ) -> String {
        let arity = target_type_expr
            .filter(|expr| expr.head_name() == Some("Tuple"))
            .map(|expr| expr.app_arg_count())
            .unwrap_or(type_params.len());
        crate::typechecker::arity_keyed_target_name(canonical_target, arity)
    }

    fn new(result: &CheckResult, module_name: &str) -> Self {
        // Build inferred dict params from checker's env (for functions without
        // explicit where clauses that still have inferred trait constraints).
        // Traits that use operator dispatch, not dictionary dispatch.
        // These should not generate dict params.
        let operator_traits: std::collections::HashSet<&str> = ["Num", "Eq"].into_iter().collect();

        let scheme_dict_params = |scheme: &crate::typechecker::Scheme| -> Vec<(String, String)> {
            scheme
                .constraints
                .iter()
                .filter(|(trait_name, _, _)| !operator_traits.contains(trait_name.as_str()))
                .map(|(trait_name, var_id, extras)| {
                    // Same determinant-extra disambiguation as the where-clause
                    // path, so inferred multi-determinant constraints on one var
                    // get distinct dict-param names.
                    let suffix = dict_var_suffix_from_types(&result.traits, trait_name, extras);
                    (trait_name.clone(), format!("v{}{}", var_id, suffix))
                })
                .collect()
        };

        let mut inferred_dict_params: HashMap<String, Vec<(String, String)>> = HashMap::new();
        for (name, scheme) in result.env.iter() {
            let dict_params = scheme_dict_params(scheme);
            if !dict_params.is_empty() {
                inferred_dict_params.insert(name.to_string(), dict_params);
            }
        }
        for info in result.codegen_info().values() {
            let origins: HashMap<&str, &str> = info
                .export_origins
                .iter()
                .map(|(surface, origin)| (surface.as_str(), origin.as_str()))
                .collect();
            for (name, scheme) in &info.exports {
                let dict_params = scheme_dict_params(scheme);
                if dict_params.is_empty() {
                    continue;
                }
                if let Some(origin) = origins.get(name.as_str()) {
                    inferred_dict_params
                        .entry((*origin).to_string())
                        .or_insert_with(|| dict_params.clone());
                }
                if name.contains('.') {
                    inferred_dict_params
                        .entry(name.clone())
                        .or_insert_with(|| dict_params.clone());
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

        // Per-operation `where` constraints, keyed by (effect, op). The op
        // signature stores constraints as (trait, var_id, _); translate the var
        // id back to its source name via `where_bound_var_names` so the dict
        // param name matches what the handler arm body and call site resolve to.
        let mut op_dict_params: HashMap<(String, String), Vec<(String, String)>> = HashMap::new();
        for (effect_name, info) in &result.effects {
            for op in &info.ops {
                let mut pairs = Vec::new();
                for (trait_name, var_id, _) in &op.constraints {
                    if trait_name == "Num" || trait_name == "Eq" {
                        continue;
                    }
                    if let Some(var_name) = result.where_bound_var_names.get(var_id) {
                        pairs.push((trait_name.clone(), var_name.clone()));
                    }
                }
                if !pairs.is_empty() {
                    op_dict_params.insert((effect_name.clone(), op.name.clone()), pairs);
                }
            }
        }

        Elaborator {
            trait_methods: HashMap::new(),
            fun_dict_params: inferred_dict_params,
            handler_dict_params: HashMap::new(),
            op_dict_params,
            dict_names,
            impl_dict_params: impl_dict_params_from_imports,
            impl_where_app_dict_params: HashMap::new(),
            impl_infos: result.trait_impls.clone(),
            traits: result.traits.clone(),
            evidence_by_node,
            current_fun: None,
            current_dict_params: HashMap::new(),
            current_dict_params_by_var: HashMap::new(),
            erlang_module,
            let_binding_arities,
            let_dict_pat_ids,
            scope_map_values: result.scope_map.values.clone(),
            scope_map_effects: result.scope_map.effects.clone(),
            resolution: result.resolution.clone(),
            type_at_node: result.type_at_node.clone(),
            where_bound_var_names: result.where_bound_var_names.clone(),
        }
    }

    /// Per-operation dict params for a handler arm, looked up by the arm's
    /// resolved (or qualified) effect and op name. Empty when the op has no
    /// `where` constraints of its own.
    fn op_dict_params_for_arm(&self, arm: &HandlerArm) -> Vec<(String, String)> {
        let effect = self
            .resolution
            .handler_arm(arm.id)
            .map(|r| r.effect.clone())
            .or_else(|| arm.qualifier.clone());
        self.op_dict_params_lookup(effect.as_deref(), &arm.op_name)
    }

    /// Per-operation dict params for an `op!` call site, looked up by the call's
    /// resolved (or qualified) effect and op name.
    fn op_dict_params_for_call(
        &self,
        node_id: crate::ast::NodeId,
        op_name: &str,
        qualifier: Option<&str>,
    ) -> Vec<(String, String)> {
        let effect = self
            .resolution
            .effect_call(node_id)
            .map(|r| r.effect.clone())
            .or_else(|| qualifier.map(str::to_string));
        self.op_dict_params_lookup(effect.as_deref(), op_name)
    }

    /// If `expr` is an App spine whose head is an `EffectCall` for an operation
    /// with its own `where` constraints, elaborate it and append the per-call
    /// dictionary arguments (outermost, so they follow the user args). Returns
    /// `None` for any other expression, leaving normal App elaboration to run.
    fn elaborate_effect_call_spine(&mut self, expr: &Expr) -> Option<Expr> {
        // Peel App nodes to find the EffectCall head and the user args (in order).
        let mut user_args: Vec<&Expr> = Vec::new();
        let mut current = expr;
        let (head, op_name, qualifier) = loop {
            match &current.kind {
                ExprKind::App { func, arg } => {
                    user_args.push(arg);
                    current = func;
                }
                ExprKind::EffectCall { name, qualifier, .. } => {
                    break (current, name.clone(), qualifier.clone());
                }
                _ => return None,
            }
        };
        user_args.reverse();

        let op_pairs = self.op_dict_params_for_call(head.id, &op_name, qualifier.as_deref());
        if op_pairs.is_empty() {
            return None;
        }

        // Rebuild the call spine with elaborated head and user args.
        let mut result = self.elaborate_expr(head);
        for arg in &user_args {
            let elab_arg = self.elaborate_expr(arg);
            result = Expr::synth(
                expr.span,
                ExprKind::App {
                    func: Box::new(result),
                    arg: Box::new(elab_arg),
                },
            );
        }

        // Append a dict arg per op constraint, resolved from the EffectCall
        // node's evidence (the concrete type is known at the call site).
        let mut trait_occurrences: HashMap<&str, usize> = HashMap::new();
        for (trait_name, _) in &op_pairs {
            let occ = trait_occurrences.entry(trait_name.as_str()).or_insert(0);
            if let Some(dict_expr) =
                self.resolve_dict_nth(trait_name, head.id, head.span, *occ)
            {
                result = Expr::synth(
                    expr.span,
                    ExprKind::App {
                        func: Box::new(result),
                        arg: Box::new(dict_expr),
                    },
                );
            }
            *occ += 1;
        }
        Some(result)
    }

    fn op_dict_params_lookup(&self, effect: Option<&str>, op_name: &str) -> Vec<(String, String)> {
        let Some(effect) = effect else {
            return Vec::new();
        };
        self.op_dict_params
            .get(&(effect.to_string(), op_name.to_string()))
            .cloned()
            .unwrap_or_default()
    }

    /// Extract dict param info from a where clause: [(trait_name, type_var_name)]
    /// for traits that use dictionary dispatch (excludes Num/Eq which use BIFs).
    ///
    /// Note: trait type args (the `_` in the destructure) are intentionally not used here.
    /// Dict params are keyed by (trait_name, self_type_var) - one dict per constraint.
    /// The extra type args (e.g. `b` in `a: ConvertTo b`) are resolved separately
    /// through TraitEvidence when looking up which concrete dict to pass at call sites.
    fn dict_params_from_where(&self, where_clause: &[TraitBound]) -> Vec<(String, String)> {
        let mut dict_params = Vec::new();
        for bound in where_clause {
            for tr in &bound.traits {
                if tr.name != "Num" && tr.name != "Eq" {
                    let resolved = self.resolved_trait_name(tr.id, &tr.name);
                    let suffix =
                        dict_var_suffix_from_type_exprs(&self.traits, &resolved, &tr.type_args);
                    dict_params.push((resolved, format!("{}{}", bound.type_var, suffix)));
                }
            }
        }
        dict_params
    }

    fn dict_params_from_where_apps(&self, where_apps: &[TraitApp]) -> Vec<(String, String)> {
        let mut dict_params = Vec::new();
        for app in where_apps {
            if matches!(app.trait_name.as_str(), "Num" | "Eq") {
                continue;
            }
            let Some(TypeExpr::Var { name, .. }) = app.type_args.first() else {
                continue;
            };
            let resolved = self.resolved_trait_name(app.id, &app.trait_name);
            // `type_args[0]` is the self var; the determinant extras are the rest.
            let suffix =
                dict_var_suffix_from_type_exprs(&self.traits, &resolved, &app.type_args[1..]);
            dict_params.push((resolved, format!("{}{}", name, suffix)));
        }
        dict_params
    }

    fn impl_type_param_id(type_params: &[TypeParam], name: &str) -> Option<u32> {
        type_params
            .iter()
            .position(|tp| tp.name == name)
            .map(|idx| u32::MAX - idx as u32)
    }

    fn impl_type_param_subst(args: &[Type]) -> HashMap<u32, Type> {
        args.iter()
            .enumerate()
            .map(|(idx, arg)| (u32::MAX - idx as u32, arg.clone()))
            .collect()
    }

    fn type_expr_to_constraint_type(
        &self,
        expr: &TypeExpr,
        type_params: &[TypeParam],
        local_subst: &HashMap<String, Type>,
    ) -> Option<Type> {
        match expr {
            TypeExpr::Named { id, name, .. } => {
                Some(Type::Con(self.resolved_type_name(*id, name), vec![]))
            }
            TypeExpr::Var { name, .. } => local_subst
                .get(name)
                .cloned()
                .or_else(|| Self::impl_type_param_id(type_params, name).map(Type::Var)),
            TypeExpr::App { .. } => {
                let head = expr.head_name()?;
                let head_id = expr.head_id().unwrap_or(expr.id());
                let mut args = Vec::new();
                let mut current = expr;
                while let TypeExpr::App { func, arg, .. } = current {
                    args.push(self.type_expr_to_constraint_type(arg, type_params, local_subst)?);
                    current = func;
                }
                args.reverse();
                Some(Type::Con(self.resolved_type_name(head_id, head), args))
            }
            TypeExpr::Symbol { name, .. } => Some(Type::Symbol(name.clone())),
            TypeExpr::Labeled { inner, .. } => {
                self.type_expr_to_constraint_type(inner, type_params, local_subst)
            }
            TypeExpr::Record { fields, .. } => fields
                .iter()
                .map(|(name, ty)| {
                    self.type_expr_to_constraint_type(ty, type_params, local_subst)
                        .map(|ty| (name.clone(), ty))
                })
                .collect::<Option<Vec<_>>>()
                .map(Type::Record),
            TypeExpr::Arrow { .. } => None,
        }
    }

    fn resolve_functional_where_app_fresh_vars(
        &self,
        app: &TraitApp,
        resolved_trait: &str,
        self_type: &Type,
        type_params: &[TypeParam],
        local_subst: &mut HashMap<String, Type>,
    ) {
        let Some(info) = self.traits.get(resolved_trait) else {
            return;
        };
        let Some(fundep) = &info.fundep else {
            return;
        };
        let Type::Con(self_name, self_args) = self_type else {
            return;
        };
        let Some((_, impl_info)) = self.impl_infos.iter().find(|((trait_name, _, target), _)| {
            trait_name == resolved_trait && target == self_name
        }) else {
            return;
        };
        let mut subst = HashMap::new();
        for (var_id, arg) in impl_info.target_type_param_ids.iter().zip(self_args.iter()) {
            subst.insert(*var_id, arg.clone());
        }
        // Only the *determined* parameters are pinned from the impl; the
        // determinant parameters are inputs, not outputs of the dependency.
        let determined = fundep.determined_extra_positions();
        for (idx, arg) in app.type_args.iter().enumerate().skip(1) {
            if !determined.contains(&(idx - 1)) {
                continue;
            }
            let TypeExpr::Var { name, .. } = arg else {
                continue;
            };
            if Self::impl_type_param_id(type_params, name).is_some()
                || local_subst.contains_key(name)
            {
                continue;
            }
            if let Some(extra) = impl_info.trait_type_args.get(idx - 1) {
                local_subst.insert(name.clone(), substitute_pattern_vars(extra, &subst));
            }
        }
    }

    fn where_app_dict_params_for_impl(
        &self,
        where_apps: &[TraitApp],
        type_params: &[TypeParam],
    ) -> Vec<ImplWhereAppDictParam> {
        let mut params = Vec::new();
        let mut local_subst = HashMap::new();
        for app in where_apps {
            if matches!(app.trait_name.as_str(), "Num" | "Eq") {
                continue;
            }
            let resolved_trait = self.resolved_trait_name(app.id, &app.trait_name);
            let Some(first_arg) = app.type_args.first() else {
                continue;
            };
            let Some(self_type) =
                self.type_expr_to_constraint_type(first_arg, type_params, &local_subst)
            else {
                continue;
            };

            self.resolve_functional_where_app_fresh_vars(
                app,
                &resolved_trait,
                &self_type,
                type_params,
                &mut local_subst,
            );

            let TypeExpr::Var { name, .. } = first_arg else {
                continue;
            };
            if Self::impl_type_param_id(type_params, name).is_some() {
                continue;
            }
            let Some(self_type) = local_subst.get(name).cloned() else {
                continue;
            };
            let Some(trait_type_args) = app.type_args[1..]
                .iter()
                .map(|arg| self.type_expr_to_constraint_type(arg, type_params, &local_subst))
                .collect::<Option<Vec<_>>>()
            else {
                continue;
            };
            params.push(ImplWhereAppDictParam {
                trait_name: resolved_trait,
                trait_type_args,
                self_type,
            });
        }
        params
    }

    /// Set up `current_dict_params` from a where clause, saving the previous state.
    /// Returns the saved state to be restored later via `restore_dict_params`.
    fn setup_dict_params_from_pairs(
        &mut self,
        dict_params: &[(String, String)],
    ) -> (HashMap<String, String>, HashMap<(String, String), String>) {
        let saved = (
            std::mem::take(&mut self.current_dict_params),
            std::mem::take(&mut self.current_dict_params_by_var),
        );
        for (resolved, type_var) in dict_params {
            let bare = resolved.rsplit('.').next().unwrap_or(resolved);
            let param_name = format!("__dict_{}_{}", bare, type_var);
            self.current_dict_params
                .insert(resolved.clone(), param_name.clone());
            self.current_dict_params_by_var
                .insert((resolved.clone(), type_var.clone()), param_name);
        }
        saved
    }

    fn setup_dict_params(
        &mut self,
        where_clause: &[TraitBound],
    ) -> (HashMap<String, String>, HashMap<(String, String), String>) {
        let dict_params = self.dict_params_from_where(where_clause);
        self.setup_dict_params_from_pairs(&dict_params)
    }

    /// Add dict params on top of the current ones (without clearing), returning
    /// the prior maps so the caller can restore them. Used for handler arms
    /// nested inside a function whose own dict params must stay in scope.
    fn push_dict_params_from_pairs(
        &mut self,
        dict_params: &[(String, String)],
    ) -> (HashMap<String, String>, HashMap<(String, String), String>) {
        let saved = (
            self.current_dict_params.clone(),
            self.current_dict_params_by_var.clone(),
        );
        for (resolved, type_var) in dict_params {
            let bare = resolved.rsplit('.').next().unwrap_or(resolved);
            let param_name = format!("__dict_{}_{}", bare, type_var);
            self.current_dict_params
                .insert(resolved.clone(), param_name.clone());
            self.current_dict_params_by_var
                .insert((resolved.clone(), type_var.clone()), param_name);
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
                Decl::TraitDef {
                    id, name, methods, ..
                } => {
                    let resolved_name = self.resolved_trait_name(*id, name);
                    for (idx, ann) in methods.iter().enumerate() {
                        let method = &ann.node;
                        if let Some((existing_trait, _)) = self.trait_methods.get(&method.name) {
                            panic!(
                                "trait method `{}` is defined in both `{}` and `{}`",
                                method.name, existing_trait, resolved_name
                            );
                        }
                        self.trait_methods
                            .insert(method.name.clone(), (resolved_name.clone(), idx));
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
                    id,
                    trait_name,
                    trait_type_args,
                    target_type,
                    target_type_expr,
                    type_params,
                    where_clause,
                    where_apps,
                    ..
                } => {
                    let canonical_trait = self.resolved_impl_trait_name(*id, trait_name);
                    let canonical_trait_type_args = self.resolved_trait_type_args(trait_type_args);
                    let canonical_target_type = self.resolved_impl_target_type(*id, target_type);
                    // Tuples are arity-distinguished: `(a, b)` and `(a, b, c)`
                    // both canonicalize to "Std.Base.Tuple", so suffix arity to
                    // keep their dict names and lookup keys distinct.
                    let canonical_target_type = self.impl_target_key(
                        &canonical_target_type,
                        target_type_expr.as_ref(),
                        type_params,
                    );
                    let dict_name = crate::typechecker::make_dict_name(
                        &canonical_trait,
                        &canonical_trait_type_args,
                        &self.erlang_module,
                        &canonical_target_type,
                    );
                    self.dict_names.insert(
                        (
                            canonical_trait.clone(),
                            canonical_trait_type_args.clone(),
                            canonical_target_type.clone(),
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
                        .map(|(i, tp)| (tp.name.as_str(), i))
                        .collect();
                    let mut params: Vec<(String, usize)> = Vec::new();
                    for bound in where_clause {
                        let idx = var_to_idx
                            .get(bound.type_var.as_str())
                            .copied()
                            .unwrap_or(0);
                        for tr in &bound.traits {
                            let resolved = self
                                .resolution
                                .trait_ref(tr.id)
                                .unwrap_or(&tr.name)
                                .to_string();
                            params.push((resolved, idx));
                        }
                    }
                    let key = (
                        canonical_trait,
                        canonical_trait_type_args,
                        canonical_target_type,
                    );
                    let where_app_params =
                        self.where_app_dict_params_for_impl(where_apps, type_params);
                    self.impl_dict_params.insert(key.clone(), params);
                    if !where_app_params.is_empty() {
                        self.impl_where_app_dict_params
                            .insert(key, where_app_params);
                    }
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
            for (idx, method) in info.methods.iter().enumerate() {
                self.trait_methods
                    .entry(method.name.clone())
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
                    id,
                    trait_name,
                    trait_type_args,
                    target_type,
                    target_type_expr,
                    type_params,
                    where_clause,
                    where_apps,
                    methods,
                    needs,
                    routed_derive_info,
                    span,
                    ..
                } => {
                    let canonical_trait = self.resolved_impl_trait_name(*id, trait_name);
                    let canonical_trait_type_args = self.resolved_trait_type_args(trait_type_args);
                    let canonical_target_base = self.resolved_impl_target_type(*id, target_type);
                    let canonical_target_type = self.impl_target_key(
                        &canonical_target_base,
                        target_type_expr.as_ref(),
                        type_params,
                    );
                    let dict_name = self
                        .dict_names
                        .get(&(
                            canonical_trait.clone(),
                            canonical_trait_type_args.clone(),
                            canonical_target_type.clone(),
                        ))
                        .cloned()
                        .unwrap();

                    let trait_info = self.traits.get(&canonical_trait).cloned();

                    // Build dict_params for conditional impls
                    let mut dict_param_pairs = self.dict_params_from_where_apps(where_apps);
                    dict_param_pairs.extend(self.dict_params_from_where(where_clause));
                    let dict_params: Vec<String> = dict_param_pairs
                        .iter()
                        .map(|(trait_name, type_var)| {
                            let bare = trait_name.rsplit('.').next().unwrap_or(trait_name);
                            format!("__dict_{}_{}", bare, type_var)
                        })
                        .collect();

                    // Set up current dict params for elaborating method bodies
                    let saved = self.setup_dict_params_from_pairs(&dict_param_pairs);

                    let mut super_dicts = Vec::new();
                    if let Some(ref info) = trait_info {
                        let mut saved_param_names = Vec::new();
                        let target_args: Vec<Type> = type_params
                            .iter()
                            .enumerate()
                            .map(|(idx, param)| {
                                let var_id = u32::MAX - idx as u32;
                                saved_param_names.push((
                                    var_id,
                                    self.where_bound_var_names
                                        .insert(var_id, param.name.clone()),
                                ));
                                Type::Var(var_id)
                            })
                            .collect();
                        let target_ty = Type::Con(canonical_target_base.clone(), target_args);
                        for supertrait in &info.supertraits {
                            if let Some(super_dict) =
                                self.dict_for_type(supertrait, &[], &target_ty, *span)
                            {
                                super_dicts.push(super_dict);
                            }
                        }
                        for (var_id, previous) in saved_param_names {
                            if let Some(previous) = previous {
                                self.where_bound_var_names.insert(var_id, previous);
                            } else {
                                self.where_bound_var_names.remove(&var_id);
                            }
                        }
                    }

                    // Order methods by trait declaration order
                    let mut ordered_methods = Vec::new();
                    let mut method_effects = Vec::new();
                    let mut method_open_rows = Vec::new();
                    if let Some(ref info) = trait_info {
                        for trait_method in &info.methods {
                            if let Some(ann) = methods
                                .iter()
                                .find(|ann| ann.node.name == trait_method.name)
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
                                method_effects.push(trait_method.effect_sig.effects.clone());
                                method_open_rows.push(trait_method.effect_sig.is_open_row);
                            }
                        }
                    }

                    self.restore_dict_params(saved);

                    // For parameterized types, if there are type_params but no where_clause,
                    // no dict params are needed. The dict is still nullary.
                    let _ = type_params; // acknowledge but don't use for now

                    let mut impl_effects: Vec<String> = needs
                        .iter()
                        .map(|e| {
                            self.scope_map_effects
                                .get(&e.name)
                                .cloned()
                                .unwrap_or_else(|| e.name.clone())
                        })
                        .collect();
                    // Routed-derive impls are synthesized with `needs: vec![]`.
                    // Source the impl's effect set from the trait method
                    // signatures' canonical effect_sigs instead — same
                    // rationale as in register_impl.
                    if routed_derive_info.is_some()
                        && let Some(ref info) = trait_info
                    {
                        for trait_method in &info.methods {
                            if methods.iter().any(|m| m.node.name == trait_method.name) {
                                impl_effects
                                    .extend(trait_method.effect_sig.effects.iter().cloned());
                            }
                        }
                    }
                    impl_effects.sort();
                    impl_effects.dedup();
                    output.push(Decl::DictConstructor {
                        id: NodeId::fresh(),
                        name: dict_name,
                        dict_params,
                        super_dicts,
                        methods: ordered_methods,
                        method_effects,
                        method_open_rows,
                        impl_effects,
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

                    if let Some(dict_param_info) = self.fun_dict_params.get(name).cloned() {
                        for (trait_name, type_var) in dict_param_info {
                            // Use bare trait name in param name to avoid dots in Erlang identifiers
                            let bare = trait_name.rsplit('.').next().unwrap_or(&trait_name);
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
                    // reference trait dicts (e.g. `show entity` -> `__dict_Show_a`).
                    // Each arm additionally gets the dict params from its own
                    // operation's `where` clause, threaded per call.
                    let handler_pairs = self.dict_params_from_where(&body.where_clause);
                    let saved = self.setup_dict_params(&body.where_clause);

                    let elab_arms: Vec<Annotated<HandlerArm>> = body
                        .arms
                        .iter()
                        .map(|ann| {
                            let arm = &ann.node;
                            let mut arm_pairs = handler_pairs.clone();
                            arm_pairs.extend(self.op_dict_params_for_arm(arm));
                            let arm_saved = self.setup_dict_params_from_pairs(&arm_pairs);
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
                            self.restore_dict_params(arm_saved);
                            elab
                        })
                        .collect();
                    let elab_return = body.return_clause.as_ref().map(|rc| {
                        Box::new(HandlerArm {
                            id: rc.id,
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

                // Pass through everything else
                _ => output.push(decl.clone()),
            }
        }

        output
    }

    /// Resolve the record type name from a node's inferred type.
    fn resolve_record_name(&self, node_id: crate::ast::NodeId) -> Option<String> {
        let ty = self.type_at_node.get(&node_id)?;
        match ty {
            Type::Con(name, _) => Some(name.clone()),
            Type::Record(fields) => {
                let names: Vec<&str> = fields.iter().map(|(n, _)| n.as_str()).collect();
                Some(crate::ast::anon_record_tag(&names))
            }
            _ => None,
        }
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
                                            ExprKind::Var { name: pname.clone() },
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

            ExprKind::RecordCreate { name, fields } => Expr::rebuild_like(
                expr,
                ExprKind::RecordCreate {
                    name: name.clone(),
                    fields: fields
                        .iter()
                        .map(|(n, s, e)| (n.clone(), *s, self.elaborate_expr(e)))
                        .collect(),
                },
            ),

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

    fn elaborate_handler(&mut self, handler: &Handler) -> Handler {
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
    fn resolve_trait_method(
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
    fn desugar_semigroup_concat(
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
    fn try_symbol_intrinsic_lambda(&self, node_id: crate::ast::NodeId, span: Span) -> Option<Expr> {
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

    fn resolve_call_dict_nth(
        &self,
        trait_name: &str,
        callee_id: crate::ast::NodeId,
        call_id: crate::ast::NodeId,
        span: Span,
        occurrence: usize,
    ) -> Option<Expr> {
        self.resolve_dict_nth(trait_name, callee_id, span, occurrence)
            .or_else(|| {
                (callee_id != call_id)
                    .then(|| self.resolve_dict_nth(trait_name, call_id, span, occurrence))
                    .flatten()
            })
    }

    fn resolve_dict_from_arg_type(&self, trait_name: &str, arg: &Expr, span: Span) -> Option<Expr> {
        let ty = self.type_at_node.get(&arg.id)?.clone();
        self.dict_for_type(trait_name, &[], &ty, span)
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
                    // KnownSymbol with concrete symbol: dict is a bare String
                    // carrying the symbol's source name. SymbolIntrinsic lowers
                    // to the binary literal at codegen.
                    if let Some(sym) = &ev.resolved_symbol {
                        return Some(Expr::synth(
                            span,
                            ExprKind::SymbolIntrinsic {
                                symbol: sym.clone(),
                            },
                        ));
                    }
                    if let Some(record_ty) = &ev.resolved_record_type {
                        return self.dict_for_type(
                            trait_name,
                            &ev.trait_type_args,
                            record_ty,
                            span,
                        );
                    }
                    return match &ev.resolved_type {
                        Some((type_name, args)) => {
                            // Concrete type: build the dict via dict_for_type,
                            // which handles where-clause constraints correctly.
                            let ty = Type::Con(type_name.clone(), args.clone());
                            self.dict_for_type(trait_name, &ev.trait_type_args, &ty, span)
                        }
                        None => {
                            // Polymorphic: use the dict param from current function.
                            // If evidence has a type_var_name, use it to build the
                            // specific dict param name (handles multiple where-clause
                            // bounds for the same trait, e.g. `where {e: Show, a: Show}`).
                            if let Some(ref var_name) = ev.type_var_name {
                                self.dict_param_for_trait_var(
                                    trait_name,
                                    var_name,
                                    &ev.trait_type_args,
                                    span,
                                )
                            } else {
                                self.current_dict_param_or_supertrait(trait_name, span)
                            }
                        }
                    };
                }
            }
        }

        // No evidence at this node -- fall back to current function's dict param
        // (handles inferred constraints where the typechecker absorbed the constraint
        // into the function's scheme rather than recording node-level evidence).
        if let Some(expr) = self.current_dict_param_or_supertrait(trait_name, span) {
            return Some(expr);
        }

        // No matching evidence for this trait. Might be a built-in trait
        // (Num, Eq) that uses direct BEAM BIF dispatch rather than dictionary dispatch.
        None
    }

    fn supertrait_index(&self, subtrait: &str, required_supertrait: &str) -> Option<usize> {
        self.traits.get(subtrait).and_then(|info| {
            info.supertraits
                .iter()
                .position(|supertrait| supertrait == required_supertrait)
        })
    }

    fn project_supertrait_dict(
        &self,
        subtrait: &str,
        required_supertrait: &str,
        dict: Expr,
        span: Span,
    ) -> Option<Expr> {
        self.supertrait_index(subtrait, required_supertrait)
            .map(|supertrait_index| {
                Expr::synth(
                    span,
                    ExprKind::DictSuperAccess {
                        dict: Box::new(dict),
                        trait_name: subtrait.to_string(),
                        supertrait_index,
                    },
                )
            })
    }

    fn dict_param_for_trait_var(
        &self,
        trait_name: &str,
        var_name: &str,
        trait_type_args: &[Type],
        span: Span,
    ) -> Option<Expr> {
        // For multi-variable-determinant fundeps, several constraints on the
        // same self var are distinguished by a determinant suffix baked into
        // the dict-param's var key. Try the qualified key first; for ordinary
        // traits the suffix is empty so this is identical to the base lookup.
        let suffix = dict_var_suffix_from_types(&self.traits, trait_name, trait_type_args);
        let qualified_var = format!("{}{}", var_name, suffix);
        if let Some(param_name) = self
            .current_dict_params_by_var
            .get(&(trait_name.to_string(), qualified_var.clone()))
        {
            return Some(Expr::synth(
                span,
                ExprKind::Var {
                    name: param_name.clone(),
                },
            ));
        }

        for ((bound_trait, bound_var), param_name) in &self.current_dict_params_by_var {
            if bound_var == &qualified_var
                && let Some(projected) = self.project_supertrait_dict(
                    bound_trait,
                    trait_name,
                    Expr::synth(
                        span,
                        ExprKind::Var {
                            name: param_name.clone(),
                        },
                    ),
                    span,
                )
            {
                return Some(projected);
            }
        }

        None
    }

    fn current_dict_param_or_supertrait(&self, trait_name: &str, span: Span) -> Option<Expr> {
        if let Some(name) = self.current_dict_params.get(trait_name) {
            return Some(Expr::synth(span, ExprKind::Var { name: name.clone() }));
        }

        for (bound_trait, param_name) in &self.current_dict_params {
            if let Some(projected) = self.project_supertrait_dict(
                bound_trait,
                trait_name,
                Expr::synth(
                    span,
                    ExprKind::Var {
                        name: param_name.clone(),
                    },
                ),
                span,
            ) {
                return Some(projected);
            }
        }

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
                trait_name: trait_name.to_string(),
                method_index: 0,
            },
        ))
    }

    /// Build the dict expression for a concrete type (the dict itself, not the method).
    /// `trait_type_args` are the resolved extra type arguments for multi-param traits.
    fn dict_for_type(
        &self,
        trait_name: &str,
        trait_type_args: &[Type],
        ty: &Type,
        span: Span,
    ) -> Option<Expr> {
        if matches!(trait_name, "Num" | "Eq") {
            return Some(Expr::synth(span, ExprKind::Tuple { elements: vec![] }));
        }

        match ty {
            Type::Record(fields) if is_generic_trait(trait_name) => {
                Some(self.build_anon_record_generic_dict(fields, span))
            }
            Type::Con(name, args)
                if name == crate::typechecker::canonicalize_type_name("Tuple")
                    && (trait_name == SHOW || trait_name == DEBUG) =>
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
                // Tuple impls are arity-keyed (`Std.Base.Tuple.2`), so for
                // tuple lookup we synthesize that name from the args. Non-
                // tuple names pass through `arity_keyed_target_name` unchanged.
                let keyed_name = crate::typechecker::arity_keyed_target_name(name, args.len());
                let key = (
                    trait_name.to_string(),
                    trait_type_arg_names(trait_type_args),
                    keyed_name,
                );
                let (key, inferred_trait_args_from_target) = if self.dict_names.contains_key(&key) {
                    (key, false)
                } else {
                    let matches: Vec<_> = self
                        .dict_names
                        .keys()
                        .filter(|(candidate_trait, _, candidate_target)| {
                            candidate_trait == trait_name && candidate_target == &key.2
                        })
                        .cloned()
                        .collect();
                    let chosen = if matches.len() <= 1 {
                        matches.into_iter().next()
                    } else {
                        // Several impls share this trait + arity-keyed target
                        // head (e.g. two disjoint `Column src Required n a` and
                        // `Column src Optional n a` Selectable impls). The
                        // trait args here are typically still unresolved out-
                        // vars, so disambiguate on the concrete self type:
                        // match each impl's full target pattern against `ty` —
                        // the distinct concrete constructors in the determining
                        // positions leave exactly one match.
                        let mut pattern_matched: Vec<ImplKey> = matches
                            .into_iter()
                            .filter(|candidate| {
                                self.impl_infos
                                    .get(candidate)
                                    .and_then(|info| info.target_pattern.as_ref())
                                    .is_some_and(|pattern| {
                                        let mut subst = HashMap::new();
                                        match_type_pattern(pattern, ty, &mut subst)
                                    })
                            })
                            .collect();
                        (pattern_matched.len() == 1)
                            .then(|| pattern_matched.pop())
                            .flatten()
                    };
                    match chosen {
                        Some(key) => (key, true),
                        None => return None,
                    }
                };
                let dict_name = self.dict_names.get(&key)?;
                let impl_info = self.impl_infos.get(&key);
                let mut dict_expr: Expr = Expr::synth(
                    span,
                    ExprKind::DictRef {
                        name: dict_name.clone(),
                    },
                );
                if let Some(params) = self.impl_where_app_dict_params.get(&key) {
                    let target_arg_subst = Self::impl_type_param_subst(args);
                    for param in params {
                        let self_type =
                            substitute_pattern_vars(&param.self_type, &target_arg_subst);
                        let trait_type_args: Vec<Type> = param
                            .trait_type_args
                            .iter()
                            .map(|arg| substitute_pattern_vars(arg, &target_arg_subst))
                            .collect();
                        let sub_dict = self.dict_for_type(
                            &param.trait_name,
                            &trait_type_args,
                            &self_type,
                            span,
                        )?;
                        dict_expr = Expr::synth(
                            span,
                            ExprKind::App {
                                func: Box::new(dict_expr),
                                arg: Box::new(sub_dict),
                            },
                        );
                    }
                }
                if let Some(info) = impl_info
                    && let Some(pattern) = &info.target_pattern
                {
                    let mut subst = HashMap::new();
                    if !match_type_pattern(pattern, ty, &mut subst) {
                        return None;
                    }
                    if !inferred_trait_args_from_target {
                        if info.trait_type_args.len() != trait_type_args.len() {
                            return None;
                        }
                        for (pattern_arg, actual_arg) in
                            info.trait_type_args.iter().zip(trait_type_args.iter())
                        {
                            if !match_type_pattern(pattern_arg, actual_arg, &mut subst) {
                                return None;
                            }
                        }
                    }
                    for (constraint_trait, var_id, extra_types) in
                        &info.param_constraints_by_var_with_args
                    {
                        let arg_ty = subst.get(var_id)?;
                        let resolved_extra_types: Vec<Type> = extra_types
                            .iter()
                            .map(|extra| substitute_pattern_vars(extra, &subst))
                            .collect();
                        let sub_dict = self.dict_for_type(
                            constraint_trait,
                            &resolved_extra_types,
                            arg_ty,
                            span,
                        )?;
                        dict_expr = Expr::synth(
                            span,
                            ExprKind::App {
                                func: Box::new(dict_expr),
                                arg: Box::new(sub_dict),
                            },
                        );
                    }
                    for (constraint_trait, var_id) in &info.param_constraints_by_var {
                        let arg_ty = subst.get(var_id)?;
                        let sub_dict = self.dict_for_type(constraint_trait, &[], arg_ty, span)?;
                        dict_expr = Expr::synth(
                            span,
                            ExprKind::App {
                                func: Box::new(dict_expr),
                                arg: Box::new(sub_dict),
                            },
                        );
                    }
                } else if let Some(constraints) = self.impl_dict_params.get(&key) {
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
                // Polymorphic type var: look up the current scope's dict param
                // for this trait + var combination. Two key conventions live
                // in `current_dict_params_by_var`:
                //   - inferred constraints store keys as `"v{id}"`
                //   - explicit where-clause bounds store keys as the source
                //     name (e.g. `"a"`)
                // Try both. For the source-name path we translate the var id
                // through `where_bound_var_names` (recorded by the typechecker
                // at impl/fn registration). Without this translation, two
                // distinct vars bound to the same trait (e.g. tuple impl
                // `where {a: ToJson, b: ToJson, c: ToJson}`) would all fall
                // through to the single-trait fallback and resolve to the
                // last-inserted dict.
                let var_key = format!("v{}", id);
                if let Some(expr) =
                    self.dict_param_for_trait_var(trait_name, &var_key, trait_type_args, span)
                {
                    return Some(expr);
                }
                if let Some(src_name) = self.where_bound_var_names.get(id)
                    && let Some(expr) =
                        self.dict_param_for_trait_var(trait_name, src_name, trait_type_args, span)
                {
                    return Some(expr);
                }
                // Fall back to single-trait lookup
                self.current_dict_param_or_supertrait(trait_name, span)
            }
            Type::Symbol(name) => {
                // KnownSymbol's "dict" is the symbol's source name as a String.
                // SymbolIntrinsic lowers to a binary literal at codegen. This
                // branch fires when a parameterized impl (e.g.
                // `impl ToJson for Variant n a where {n: KnownSymbol, ...}`)
                // recursively constructs a sub-dict for the symbol parameter.
                Some(Expr::synth(
                    span,
                    ExprKind::SymbolIntrinsic {
                        symbol: name.clone(),
                    },
                ))
            }
            _ => None,
        }
    }

    fn build_anon_record_generic_dict(&self, fields: &[(String, Type)], span: Span) -> Expr {
        Expr::synth(
            span,
            ExprKind::Tuple {
                elements: vec![
                    self.build_anon_record_generic_to(fields, span),
                    self.build_anon_record_generic_from(fields, span),
                ],
            },
        )
    }

    fn build_anon_record_generic_to(&self, fields: &[(String, Type)], span: Span) -> Expr {
        let record_var_name = "__anon_rec".to_string();
        let record_var = Expr::synth(
            span,
            ExprKind::Var {
                name: record_var_name.clone(),
            },
        );
        let names: Vec<&str> = fields.iter().map(|(name, _)| name.as_str()).collect();
        let tag = crate::ast::anon_record_tag(&names);
        let inner = self.build_anon_record_rep_to_inner(fields, &record_var, &tag, span);
        let body = self.apply2(
            &generic_ctor("Record"),
            self.string_lit(&tag, span),
            inner,
            span,
        );
        Expr::synth(
            span,
            ExprKind::Lambda {
                params: vec![Pat::Var {
                    id: NodeId::fresh(),
                    name: record_var_name,
                    span,
                }],
                body: Box::new(body),
            },
        )
    }

    fn build_anon_record_generic_from(&self, fields: &[(String, Type)], span: Span) -> Expr {
        let field_var_names: Vec<String> = (0..fields.len()).map(|i| format!("__f{i}")).collect();
        let inner_pat = self.build_anon_record_rep_from_inner(&field_var_names, span);
        let record_pat = Pat::Constructor {
            id: NodeId::fresh(),
            name: generic_ctor("Record"),
            args: vec![
                Pat::Wildcard {
                    id: NodeId::fresh(),
                    span,
                },
                inner_pat,
            ],
            span,
        };
        let record_fields: Vec<(String, Span, Expr)> = fields
            .iter()
            .zip(field_var_names.iter())
            .map(|((field_name, _), var_name)| {
                (
                    field_name.clone(),
                    span,
                    Expr::synth(
                        span,
                        ExprKind::Var {
                            name: var_name.clone(),
                        },
                    ),
                )
            })
            .collect();
        Expr::synth(
            span,
            ExprKind::Lambda {
                params: vec![record_pat],
                body: Box::new(Expr::synth(
                    span,
                    ExprKind::AnonRecordCreate {
                        fields: record_fields,
                    },
                )),
            },
        )
    }

    fn build_anon_record_rep_to_inner(
        &self,
        fields: &[(String, Type)],
        record_var: &Expr,
        record_tag: &str,
        span: Span,
    ) -> Expr {
        if fields.is_empty() {
            return Expr::synth(
                span,
                ExprKind::Constructor {
                    name: generic_ctor("U1"),
                },
            );
        }
        let mut iter = fields.iter().rev();
        let (last_name, _) = iter.next().expect("non-empty fields");
        let mut acc = self.build_anon_record_field_to(last_name, record_var, record_tag, span);
        for (field_name, _) in iter {
            acc = self.apply2(
                &generic_ctor("And"),
                self.build_anon_record_field_to(field_name, record_var, record_tag, span),
                acc,
                span,
            );
        }
        acc
    }

    fn build_anon_record_field_to(
        &self,
        field_name: &str,
        record_var: &Expr,
        record_tag: &str,
        span: Span,
    ) -> Expr {
        let access = Expr::synth(
            span,
            ExprKind::FieldAccess {
                expr: Box::new(record_var.clone()),
                field: field_name.to_string(),
                record_name: Some(record_tag.to_string()),
            },
        );
        self.apply1(
            &generic_ctor("Labeled"),
            self.apply1(&generic_ctor("Leaf"), access, span),
            span,
        )
    }

    fn build_anon_record_rep_from_inner(&self, field_vars: &[String], span: Span) -> Pat {
        if field_vars.is_empty() {
            return Pat::Constructor {
                id: NodeId::fresh(),
                name: generic_ctor("U1"),
                args: vec![],
                span,
            };
        }
        let mut iter = field_vars.iter().rev();
        let last = iter.next().expect("non-empty field vars");
        let mut acc = self.build_anon_record_field_from(last, span);
        for var_name in iter {
            acc = Pat::Constructor {
                id: NodeId::fresh(),
                name: generic_ctor("And"),
                args: vec![self.build_anon_record_field_from(var_name, span), acc],
                span,
            };
        }
        acc
    }

    fn build_anon_record_field_from(&self, var_name: &str, span: Span) -> Pat {
        Pat::Constructor {
            id: NodeId::fresh(),
            name: generic_ctor("Labeled"),
            args: vec![Pat::Constructor {
                id: NodeId::fresh(),
                name: generic_ctor("Leaf"),
                args: vec![Pat::Var {
                    id: NodeId::fresh(),
                    name: var_name.to_string(),
                    span,
                }],
                span,
            }],
            span,
        }
    }

    fn apply1(&self, func: &str, arg: Expr, span: Span) -> Expr {
        Expr::synth(
            span,
            ExprKind::App {
                func: Box::new(Expr::synth(
                    span,
                    ExprKind::Constructor { name: func.into() },
                )),
                arg: Box::new(arg),
            },
        )
    }

    fn apply2(&self, func: &str, a: Expr, b: Expr, span: Span) -> Expr {
        Expr::synth(
            span,
            ExprKind::App {
                func: Box::new(self.apply1(func, a, span)),
                arg: Box::new(b),
            },
        )
    }

    fn string_lit(&self, value: &str, span: Span) -> Expr {
        Expr::synth(
            span,
            ExprKind::Lit {
                value: Lit::String(value.into(), StringKind::Normal),
            },
        )
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
                && ev.resolved_type.as_ref().is_some_and(|(name, _)| {
                    name == crate::typechecker::canonicalize_type_name("Tuple")
                })
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
