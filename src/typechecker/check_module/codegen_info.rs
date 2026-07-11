use std::collections::HashMap;

use super::ModuleExports;
use crate::typechecker::{
    EffectDefInfo, EffectOpSig, Scheme, ScopeMap, Type, arity_keyed_target_name,
    canonicalize_type_name, make_dict_name,
};

/// An effect operation definition for codegen: operation name and parameter count.
#[derive(Debug, Clone)]
pub struct EffectOpDef {
    pub name: String,
    /// Source-level parameter count before erasing `Unit` placeholders.
    pub source_param_count: usize,
    /// Runtime handler arity after erasing `Unit` placeholder parameters.
    pub runtime_param_count: usize,
    /// Indices of source params that survive runtime erasure.
    pub runtime_param_positions: Vec<usize>,
    /// For callback parameters, the effects absorbed by that parameter.
    pub param_absorbed_effects: HashMap<usize, Vec<String>>,
    /// Callback parameters whose function type carries an open effect row,
    /// including open-only rows with no named effects.
    pub param_open_rows: std::collections::HashSet<usize>,
    /// Dictionary parameter names for the op's own `where` constraints
    /// (e.g. `["__dict_PgType_a"]`). Threaded per call as trailing op args.
    pub dict_param_names: Vec<String>,
}

/// An effect definition for codegen: effect name, its operations, and type parameter count.
#[derive(Debug, Clone)]
pub struct EffectDef {
    pub name: String,
    pub ops: Vec<EffectOpDef>,
    pub type_param_count: usize,
}

fn impl_target_key(
    canonical_target: &str,
    target_type_expr: Option<&crate::ast::TypeExpr>,
    type_params: &[crate::ast::TypeParam],
) -> String {
    let arity = target_type_expr
        .filter(|expr| expr.head_name() == Some("Tuple"))
        .map(|expr| expr.app_arg_count())
        .unwrap_or(type_params.len());
    arity_keyed_target_name(canonical_target, arity)
}

/// A trait impl dict exported by a module.
#[derive(Debug, Clone)]
pub struct TraitImplDict {
    pub trait_name: String,
    /// Extra type arguments applied to the trait (e.g. ["NOK"] in `impl ConvertTo NOK for USD`).
    pub trait_type_args: Vec<String>,
    pub target_type: String,
    /// Module-qualified dict name (e.g. `__dict_Show_animals_Animal`).
    pub dict_name: String,
    /// Number of dict parameters (from where clause).
    pub arity: usize,
    /// Where-clause constraints as (constraint_trait, param_index) pairs.
    /// Used by the elaborator to pass correct sub-dicts for parameterized impls.
    pub param_constraints: Vec<(String, usize)>,
    /// Sorted, canonical effect names declared in the impl's `needs` clause.
    /// Applies uniformly to every method dispatched through this dict — codegen
    /// uses it to thread evidence at trait method call sites that elaborated
    /// to `DictMethodAccess`. Empty when the impl has no `needs` clause.
    pub impl_effects: Vec<String>,
}

/// Information about a module's exports needed by the lowerer/codegen.
/// Populated during typechecking alongside `tc_modules`.
#[derive(Debug, Clone, Default)]
pub struct ModuleCodegenInfo {
    /// Public type bindings: name -> scheme.
    pub exports: Vec<(String, Scheme)>,
    /// Public binding surface name -> canonical origin name.
    pub export_origins: Vec<(String, String)>,
    /// Public effect surface name -> canonical origin effect name.
    pub effect_origins: Vec<(String, String)>,
    /// Public effect definitions.
    pub effect_defs: Vec<EffectDef>,
    /// Public record definitions: record name -> ordered field names.
    pub record_fields: Vec<(String, Vec<String>)>,
    /// Public handler names.
    pub handler_defs: Vec<String>,
    /// Public handler surface name -> canonical origin handler name.
    pub handler_origins: Vec<(String, String)>,
    /// Public function effect annotations: name -> sorted effect names.
    pub fun_effects: Vec<(String, Vec<String>)>,
    /// Public type constructors: type name -> [constructor names].
    pub type_constructors: Vec<(String, Vec<String>)>,
    /// Trait impl dicts exported by this module.
    pub trait_impl_dicts: Vec<TraitImplDict>,
    /// External function mappings: (saga_name, erlang_module, erlang_func, arity).
    /// Includes both public and private externals (private ones are needed for handler inlining).
    pub external_funs: Vec<(String, String, String, usize)>,
    /// Compiler intrinsic exports: source name -> intrinsic id.
    pub intrinsic_exports: Vec<(String, crate::intrinsics::IntrinsicId)>,
}

fn collect_effects_from_fun_type(ty: &Type) -> Vec<String> {
    let mut effects = std::collections::BTreeSet::new();
    let mut current = ty;
    while let Type::Fun(_, ret, row) = current {
        for entry in &row.effects {
            effects.insert(entry.name.clone());
        }
        current = ret;
    }
    effects.into_iter().collect()
}

fn effect_param_absorbed_effects(op: &EffectOpSig) -> HashMap<usize, Vec<String>> {
    op.params
        .iter()
        .enumerate()
        .filter_map(|(idx, (_, ty))| {
            let effs = collect_effects_from_fun_type(ty);
            (!effs.is_empty()).then_some((idx, effs))
        })
        .collect()
}

fn effect_param_open_rows(op: &EffectOpSig) -> std::collections::HashSet<usize> {
    op.params
        .iter()
        .enumerate()
        .filter_map(|(idx, (_, ty))| {
            crate::codegen::lower::util::has_open_effect_row(ty).then_some(idx)
        })
        .collect()
}

/// Count the arity of a constructor from its type (number of Fun levels).
pub(super) fn ctor_arity(ty: &Type) -> usize {
    match ty {
        Type::Fun(_, ret, _) => 1 + ctor_arity(ret),
        _ => 0,
    }
}

/// Collect codegen-relevant info from a module's public declarations.
pub(super) fn collect_codegen_info(
    module_name: &str,
    program: &[crate::ast::Decl],
    exports: &ModuleExports,
    effects_map: &std::collections::HashMap<String, EffectDefInfo>,
    scope_map: &ScopeMap,
) -> ModuleCodegenInfo {
    use crate::ast::Decl;
    fn is_runtime_unit_param(ty: &crate::ast::TypeExpr) -> bool {
        match ty {
            crate::ast::TypeExpr::Named { name, .. } => {
                canonicalize_type_name(name) == canonicalize_type_name("Unit")
            }
            crate::ast::TypeExpr::Labeled { inner, .. } => is_runtime_unit_param(inner),
            _ => false,
        }
    }

    let canonical_type_name = |name: &str| -> String {
        scope_map
            .resolve_type(name)
            .map(|s| s.to_string())
            .unwrap_or_else(|| canonicalize_type_name(name).to_string())
    };

    let canonical_trait_type_args = |args: &[String]| -> Vec<String> {
        args.iter()
            .map(|arg| {
                if arg.starts_with(|c: char| c.is_uppercase()) || arg.contains('.') {
                    canonical_type_name(arg)
                } else {
                    arg.clone()
                }
            })
            .collect()
    };

    let mut effect_defs = Vec::new();
    let mut record_fields = Vec::new();
    let mut handler_defs = Vec::new();
    let mut fun_effects = Vec::new();
    let mut trait_impl_dicts = Vec::new();
    let mut external_funs = Vec::new();
    let mut intrinsic_exports = Vec::new();

    // Erlang module name: "Foo.Bar" -> "foo_bar"
    let erlang_module = module_name
        .split('.')
        .map(|s| s.to_lowercase())
        .collect::<Vec<_>>()
        .join("_");

    for decl in program {
        match decl {
            Decl::EffectDef {
                name,
                type_params,
                operations,
                ..
            } => {
                let canonical_effect = format!("{}.{}", module_name, name);
                let effect_info = effects_map
                    .get(&canonical_effect)
                    .unwrap_or_else(|| panic!("missing effect info for {canonical_effect}"));
                let ops = operations
                    .iter()
                    .map(|op| EffectOpDef {
                        name: op.node.name.clone(),
                        source_param_count: op.node.params.len(),
                        runtime_param_positions: op
                            .node
                            .params
                            .iter()
                            .enumerate()
                            .filter_map(|(idx, (_, ty))| {
                                (!is_runtime_unit_param(ty)).then_some(idx)
                            })
                            .collect(),
                        runtime_param_count: op
                            .node
                            .params
                            .iter()
                            .filter(|(_, ty)| !is_runtime_unit_param(ty))
                            .count(),
                        param_absorbed_effects: effect_info
                            .ops
                            .iter()
                            .find(|sig| sig.name == op.node.name)
                            .map(effect_param_absorbed_effects)
                            .unwrap_or_default(),
                        param_open_rows: effect_info
                            .ops
                            .iter()
                            .find(|sig| sig.name == op.node.name)
                            .map(effect_param_open_rows)
                            .unwrap_or_default(),
                        dict_param_names: crate::ast::op_dict_param_names(&op.node.where_clause),
                    })
                    .collect();
                // Codegen metadata is internal compiler state, so keep effect
                // op counts even for private effects. Public functions can
                // still `needs {PrivateEffect}`, and imported call sites need
                // the effect's runtime op arity to thread handler callbacks.
                effect_defs.push(EffectDef {
                    name: canonical_effect,
                    ops,
                    type_param_count: type_params.len(),
                });
            }
            Decl::NewEffect { name, .. } => {
                let canonical_effect = format!("{}.{}", module_name, name);
                let effect_info = effects_map
                    .get(&canonical_effect)
                    .unwrap_or_else(|| panic!("missing neweffect info for {canonical_effect}"));
                let is_unit = |ty: &Type| {
                    matches!(
                        ty,
                        Type::Con(n, args) if args.is_empty()
                            && canonicalize_type_name(n) == canonicalize_type_name("Unit")
                    )
                };
                let ops = effect_info
                    .ops
                    .iter()
                    .map(|op| {
                        let runtime_param_positions: Vec<usize> = op
                            .params
                            .iter()
                            .enumerate()
                            .filter_map(|(idx, (_, ty))| (!is_unit(ty)).then_some(idx))
                            .collect();
                        EffectOpDef {
                            name: op.name.clone(),
                            source_param_count: op.params.len(),
                            runtime_param_count: runtime_param_positions.len(),
                            runtime_param_positions,
                            param_absorbed_effects: effect_param_absorbed_effects(op),
                            param_open_rows: effect_param_open_rows(op),
                            dict_param_names: Vec::new(),
                        }
                    })
                    .collect();
                effect_defs.push(EffectDef {
                    name: canonical_effect,
                    ops,
                    type_param_count: 0,
                });
            }
            Decl::RecordDef {
                public: true,
                name,
                fields,
                ..
            } => {
                let field_names: Vec<String> = fields.iter().map(|f| f.node.0.clone()).collect();
                record_fields.push((name.clone(), field_names));
            }
            Decl::HandlerDef {
                public: true, name, ..
            } => {
                handler_defs.push(format!("{}.{}", module_name, name));
            }
            Decl::FunSignature {
                public: true,
                name,
                effects,
                ..
            } if !effects.is_empty() => {
                // Strip beam-native effects (same as elaboration), canonicalize names
                let mut sorted: Vec<String> = effects
                    .iter()
                    .filter(|e| {
                        !matches!(
                            e.name.as_str(),
                            "Actor" | "Process" | "Monitor" | "Link" | "Timer"
                        )
                    })
                    .map(|e| {
                        // Resolve effect name to canonical via scope_map
                        scope_map
                            .resolve_effect(&e.name)
                            .map(|s| s.to_string())
                            .unwrap_or_else(|| {
                                // Fallback: try effects_map directly, or qualify with module
                                if effects_map.contains_key(&e.name) {
                                    e.name.clone()
                                } else {
                                    format!("{}.{}", module_name, e.name)
                                }
                            })
                    })
                    .collect();
                sorted.sort();
                if !sorted.is_empty() {
                    fun_effects.push((name.clone(), sorted));
                }
            }
            Decl::FunSignature {
                name,
                params,
                annotations,
                ..
            } => {
                if annotations.iter().any(|a| a.name == "builtin") {
                    let canonical = format!("{}.{}", module_name, name);
                    let intrinsic = crate::intrinsics::intrinsic_id_for_canonical_name(&canonical)
                        .unwrap_or_else(|| {
                            panic!("@builtin declaration has no IntrinsicId mapping: {canonical}")
                        });
                    intrinsic_exports.push((name.clone(), intrinsic));
                }
                // Collect @external annotations for both public and private functions.
                // Private externals are needed for handler body inlining.
                if let Some(ext) = annotations.iter().find(|a| a.name == "external")
                    && ext.args.len() >= 3
                    && let (
                        crate::ast::Lit::String(erl_mod, _),
                        crate::ast::Lit::String(erl_func, _),
                    ) = (&ext.args[1], &ext.args[2])
                {
                    external_funs.push((
                        name.clone(),
                        erl_mod.clone(),
                        erl_func.clone(),
                        params.len(),
                    ));
                }
            }
            Decl::ImplDef {
                trait_name,
                trait_type_args,
                target_type,
                target_type_expr,
                type_params,
                where_clause,
                where_apps,
                needs,
                ..
            } => {
                // Resolve trait name to canonical form via scope_map
                let canonical_trait = scope_map
                    .resolve_trait(trait_name)
                    .map(|s| s.to_string())
                    .unwrap_or_else(|| format!("{}.{}", module_name, trait_name));
                let trait_type_arg_names: Vec<String> = trait_type_args
                    .iter()
                    .map(|te| {
                        // Use the head name of an App chain so a parameterized
                        // type like `List a` reduces to `List` for the
                        // dict-name key.
                        let head = te.head_name().unwrap_or("");
                        match te {
                            crate::ast::TypeExpr::Var { name, .. } => name.clone(),
                            _ => scope_map
                                .resolve_type(head)
                                .map(|s| s.to_string())
                                .unwrap_or_else(|| canonical_type_name(head)),
                        }
                    })
                    .collect();
                let canonical_trait_type_args = canonical_trait_type_args(&trait_type_arg_names);
                let canonical_target_type = canonical_type_name(target_type);
                let canonical_target_type = impl_target_key(
                    &canonical_target_type,
                    target_type_expr.as_ref(),
                    type_params,
                );
                let dict_name = make_dict_name(
                    &canonical_trait,
                    &canonical_trait_type_args,
                    &erlang_module,
                    &canonical_target_type,
                );
                // Cross-module dict-constructor arity. This MUST equal the
                // number of dict parameters the elaborator emits for the
                // constructor (`Elaborator::dict_params_from_where_apps` +
                // `dict_params_from_where`, consumed in `program.rs`), since the
                // emitted constructor's arity is `dict_params.len()` and an
                // importing module references it via `make_fun(..., arity)`.
                //
                // A naive `where_apps.len()` overcounts: a where-app whose first
                // type argument is *concrete* (not a type variable) carries no
                // runtime dict — e.g. `where {ConvertTo Int b}` resolves to a
                // statically-known impl, which the elaborator skips. Counting
                // them inflated the exported arity, so `make_fun` referenced the
                // dict at the wrong arity and crashed at runtime. Num/Eq bounds
                // likewise use BIFs, not dicts, and are skipped on both sides.
                let where_app_arity = where_apps
                    .iter()
                    .filter(|app| {
                        !matches!(app.trait_name.as_str(), "Num" | "Eq")
                            && matches!(
                                app.type_args.first(),
                                Some(crate::ast::TypeExpr::Var { .. })
                            )
                    })
                    .count();
                let where_clause_arity = where_clause
                    .iter()
                    .flat_map(|b| b.traits.iter())
                    .filter(|tr| tr.name != "Num" && tr.name != "Eq")
                    .count();
                let arity = where_app_arity + where_clause_arity;
                let var_to_idx: std::collections::HashMap<&str, usize> = type_params
                    .iter()
                    .enumerate()
                    .map(|(i, tp)| (tp.name.as_str(), i))
                    .collect();
                let param_constraints: Vec<(String, usize)> = where_clause
                    .iter()
                    .flat_map(|bound| {
                        let idx = var_to_idx
                            .get(bound.type_var.as_str())
                            .copied()
                            .unwrap_or(0);
                        bound.traits.iter().map(move |tr| {
                            let resolved = scope_map
                                .resolve_trait(&tr.name)
                                .unwrap_or(tr.name.as_str())
                                .to_string();
                            (resolved, idx)
                        })
                    })
                    .collect();
                let mut impl_effects: Vec<String> = needs
                    .iter()
                    .map(|e| {
                        scope_map
                            .resolve_effect(&e.name)
                            .map(|s| s.to_string())
                            .unwrap_or_else(|| e.name.clone())
                    })
                    .collect();
                impl_effects.sort();
                impl_effects.dedup();
                trait_impl_dicts.push(TraitImplDict {
                    trait_name: canonical_trait,
                    trait_type_args: canonical_trait_type_args,
                    target_type: canonical_target_type,
                    dict_name,
                    arity,
                    param_constraints,
                    impl_effects,
                });
            }
            _ => {}
        }
    }

    ModuleCodegenInfo {
        exports: exports.bindings.clone(),
        export_origins: exports
            .binding_origins
            .iter()
            .map(|(surface, origin)| (surface.clone(), origin.clone()))
            .collect(),
        effect_origins: exports
            .effect_origins
            .iter()
            .map(|(surface, origin)| (surface.clone(), origin.clone()))
            .collect(),
        effect_defs,
        record_fields,
        handler_defs,
        handler_origins: exports
            .handler_origins
            .iter()
            .map(|(surface, origin)| (surface.clone(), origin.clone()))
            .collect(),
        fun_effects,
        type_constructors: exports.type_constructors.clone().into_iter().collect(),
        trait_impl_dicts,
        external_funs,
        intrinsic_exports,
    }
}
