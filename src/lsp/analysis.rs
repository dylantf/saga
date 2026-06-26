use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::hash::{Hash, Hasher};
use std::path::{Path, PathBuf};

use saga::{ast, typechecker};
use tower_lsp::lsp_types::Url;

use super::{ModuleInterfaceUpdate, extract_module_info};

pub(super) fn source_fingerprint(source: &str) -> u64 {
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    source.hash(&mut hasher);
    hasher.finish()
}

pub(super) fn module_interface_fingerprint(exports: &typechecker::ModuleExports) -> u64 {
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    hash_module_exports(exports, &mut hasher);
    hasher.finish()
}

fn hash_module_exports(exports: &typechecker::ModuleExports, state: &mut impl Hasher) {
    "ModuleExports".hash(state);
    hash_sorted_pairs(&exports.bindings, state, hash_scheme);
    hash_string_map(&exports.binding_origins, state);
    hash_string_vec_map(&exports.type_constructors, state);
    hash_sorted_map(&exports.inlinable_constructors, state, |ctors, state| {
        hash_sorted_pairs(ctors, state, hash_scheme);
    });
    hash_string_map(&exports.type_origins, state);
    hash_sorted_map(&exports.record_defs, state, hash_record_info);
    hash_sorted_map(&exports.traits, state, hash_trait_info);
    hash_string_map(&exports.trait_origins, state);
    hash_sorted_map(&exports.trait_impls, state, hash_impl_info);
    hash_sorted_map(&exports.effects, state, hash_effect_def_info);
    hash_string_map(&exports.effect_origins, state);
    hash_sorted_map(&exports.handlers, state, hash_handler_info);
    hash_string_map(&exports.handler_origins, state);
    hash_sorted_map(&exports.type_arity, state, |arity, state| arity.hash(state));
    hash_sorted_map(&exports.type_param_kinds, state, |kinds, state| {
        hash_vec(kinds, state, |kind, state| kind.hash(state));
    });
    hash_sorted_map(&exports.type_aliases, state, hash_type_alias_info);
    let effectful: BTreeSet<_> = exports.effectful_funs.iter().collect();
    hash_vec(
        &effectful.into_iter().collect::<Vec<_>>(),
        state,
        |name, state| {
            name.hash(state);
        },
    );
}

fn hash_sorted_pairs<T, H: Hasher>(
    values: &[(String, T)],
    state: &mut H,
    hash_value: impl Fn(&T, &mut H),
) {
    let sorted: BTreeMap<_, _> = values.iter().map(|(key, value)| (key, value)).collect();
    hash_vec(
        &sorted.into_iter().collect::<Vec<_>>(),
        state,
        |(key, value), state| {
            key.hash(state);
            hash_value(value, state);
        },
    );
}

fn hash_string_map<H: Hasher>(values: &HashMap<String, String>, state: &mut H) {
    hash_sorted_map(values, state, |value, state| value.hash(state));
}

fn hash_string_vec_map<H: Hasher>(values: &HashMap<String, Vec<String>>, state: &mut H) {
    hash_sorted_map(values, state, |value, state| value.hash(state));
}

fn hash_sorted_map<K, V, H: Hasher>(
    values: &HashMap<K, V>,
    state: &mut H,
    hash_value: impl Fn(&V, &mut H),
) where
    K: Ord + Hash,
{
    let sorted: BTreeMap<_, _> = values.iter().collect();
    hash_vec(
        &sorted.into_iter().collect::<Vec<_>>(),
        state,
        |(key, value), state| {
            key.hash(state);
            hash_value(value, state);
        },
    );
}

fn hash_vec<T, H: Hasher>(values: &[T], state: &mut H, hash_value: impl Fn(&T, &mut H)) {
    values.len().hash(state);
    for value in values {
        hash_value(value, state);
    }
}

fn hash_scheme<H: Hasher>(scheme: &typechecker::Scheme, state: &mut H) {
    scheme.forall.hash(state);
    hash_vec(
        &scheme.constraints,
        state,
        |(trait_name, var_id, extra_args), state| {
            trait_name.hash(state);
            var_id.hash(state);
            hash_vec(extra_args, state, hash_type);
        },
    );
    hash_type(&scheme.ty, state);
}

fn hash_type<H: Hasher>(ty: &typechecker::Type, state: &mut H) {
    match ty {
        typechecker::Type::Var(id) => {
            "Var".hash(state);
            id.hash(state);
        }
        typechecker::Type::Fun(param, ret, effects) => {
            "Fun".hash(state);
            hash_type(param, state);
            hash_type(ret, state);
            hash_effect_row(effects, state);
        }
        typechecker::Type::Con(name, args) => {
            "Con".hash(state);
            name.hash(state);
            hash_vec(args, state, hash_type);
        }
        typechecker::Type::Record(fields) => {
            "Record".hash(state);
            hash_vec(fields, state, |(name, ty), state| {
                name.hash(state);
                hash_type(ty, state);
            });
        }
        typechecker::Type::Symbol(value) => {
            "Symbol".hash(state);
            value.hash(state);
        }
        typechecker::Type::Error => {
            "Error".hash(state);
        }
    }
}

fn hash_effect_row<H: Hasher>(row: &typechecker::EffectRow, state: &mut H) {
    let mut effects = row.effects.clone();
    effects.sort_by(|a, b| {
        a.name
            .cmp(&b.name)
            .then_with(|| format!("{:?}", a.args).cmp(&format!("{:?}", b.args)))
    });
    hash_vec(&effects, state, |entry, state| {
        entry.name.hash(state);
        hash_vec(&entry.args, state, hash_type);
    });
    hash_vec(&row.tails, state, hash_type);
}

fn hash_record_info<H: Hasher>(info: &typechecker::RecordInfo, state: &mut H) {
    info.type_params.hash(state);
    hash_vec(&info.fields, state, |(name, ty), state| {
        name.hash(state);
        hash_type(ty, state);
    });
}

fn hash_trait_info<H: Hasher>(info: &typechecker::TraitInfo, state: &mut H) {
    hash_vec(&info.type_params, state, |(name, kind), state| {
        name.hash(state);
        kind.hash(state);
    });
    info.supertraits.hash(state);
    hash_vec(&info.methods, state, hash_trait_method_info);
    info.is_functional.hash(state);
    match &info.fundep {
        Some(fundep) => {
            true.hash(state);
            fundep.determinant.hash(state);
            fundep.determined.hash(state);
        }
        None => false.hash(state),
    }
}

fn hash_trait_method_info<H: Hasher>(info: &typechecker::TraitMethodInfo, state: &mut H) {
    info.name.hash(state);
    hash_vec(&info.param_types, state, hash_type);
    hash_type(&info.return_type, state);
    info.trait_param_id.hash(state);
    hash_scheme(&info.scheme, state);
    info.effect_sig.effects.hash(state);
    info.effect_sig.is_open_row.hash(state);
    info.effect_sig.user_arity.hash(state);
}

fn hash_impl_info<H: Hasher>(info: &typechecker::ImplInfo, state: &mut H) {
    info.param_constraints.hash(state);
    info.param_constraints_by_var.hash(state);
    hash_vec(
        &info.param_constraints_by_var_with_args,
        state,
        |(trait_name, var_id, extra_args), state| {
            trait_name.hash(state);
            var_id.hash(state);
            hash_vec(extra_args, state, hash_type);
        },
    );
    match &info.target_pattern {
        Some(ty) => {
            true.hash(state);
            hash_type(ty, state);
        }
        None => false.hash(state),
    }
    hash_vec(&info.trait_type_args, state, hash_type);
    info.target_type_param_ids.hash(state);
    hash_string_vec_map(&info.method_effects, state);
    hash_vec(&info.where_app_dict_params, state, |param, state| {
        param.trait_name.hash(state);
        hash_vec(&param.trait_type_args, state, hash_type);
        hash_type(&param.self_type, state);
    });
}

fn hash_effect_def_info<H: Hasher>(info: &typechecker::EffectDefInfo, state: &mut H) {
    info.type_params.hash(state);
    hash_vec(&info.ops, state, |op, state| {
        op.name.hash(state);
        op.effect_name.hash(state);
        hash_vec(&op.params, state, |(label, ty), state| {
            label.hash(state);
            hash_type(ty, state);
        });
        hash_type(&op.return_type, state);
        hash_effect_row(&op.needs, state);
        hash_vec(
            &op.constraints,
            state,
            |(trait_name, var_id, extra_args), state| {
                trait_name.hash(state);
                var_id.hash(state);
                hash_vec(extra_args, state, hash_type);
            },
        );
    });
    info.source_module.hash(state);
}

fn hash_handler_info<H: Hasher>(info: &typechecker::HandlerInfo, state: &mut H) {
    info.effects.hash(state);
    match &info.return_type {
        Some((param, body)) => {
            true.hash(state);
            hash_type(param, state);
            hash_type(body, state);
        }
        None => false.hash(state),
    }
    hash_effect_row(&info.needs_effects, state);
    info.forall.hash(state);
    let where_constraints: BTreeMap<_, _> = info.where_constraints.iter().collect();
    hash_vec(
        &where_constraints.into_iter().collect::<Vec<_>>(),
        state,
        |((effect_name, param_index), constraints), state| {
            effect_name.hash(state);
            param_index.hash(state);
            hash_vec(constraints, state, |(trait_name, vars), state| {
                trait_name.hash(state);
                vars.hash(state);
            });
        },
    );
    info.source_module.hash(state);
}

fn hash_type_alias_info<H: Hasher>(info: &typechecker::TypeAliasInfo, state: &mut H) {
    info.param_vars.hash(state);
    info.param_kinds.hash(state);
    hash_type(&info.body, state);
}

pub(super) fn source_fingerprint_for_path(
    path: &Path,
    source_overlay: &HashMap<PathBuf, String>,
) -> Option<u64> {
    if let Some(source) = source_overlay.get(path) {
        return Some(source_fingerprint(source));
    }
    std::fs::read_to_string(path)
        .ok()
        .map(|source| source_fingerprint(&source))
}

pub(super) fn builtin_module_source_fingerprint(module_name: &str) -> Option<u64> {
    let path: Vec<String> = module_name.split('.').map(str::to_string).collect();
    typechecker::builtin_module_source(&path).map(source_fingerprint)
}

pub(super) fn collect_module_interface_updates(
    current_uri: Option<&Url>,
    current_program: &ast::Program,
    checker: &typechecker::Checker,
    check: &typechecker::CheckResult,
    source_overlay: &HashMap<PathBuf, String>,
    cached_source_fingerprints: &HashMap<String, u64>,
    include_current: bool,
) -> Vec<ModuleInterfaceUpdate> {
    let mut updates = Vec::new();

    for (module_name, exports) in check.module_exports() {
        let path = check.resolve_module_path(module_name);
        let source_fingerprint = match &path {
            Some(path) => source_fingerprint_for_path(path, source_overlay),
            None => builtin_module_source_fingerprint(module_name),
        };
        let Some(source_fingerprint) = source_fingerprint else {
            continue;
        };
        if cached_source_fingerprints.get(module_name) == Some(&source_fingerprint) {
            continue;
        }
        updates.push(ModuleInterfaceUpdate {
            module_name: module_name.clone(),
            path,
            source_fingerprint,
            interface_fingerprint: module_interface_fingerprint(exports),
            exports: exports.clone(),
            codegen_info: check.codegen_info().get(module_name).cloned(),
            check_result: check.module_check_results().get(module_name).cloned(),
            is_current: false,
        });
    }

    if include_current {
        let (Some(uri), (Some(module_name), _)) =
            (current_uri, extract_module_info(current_program))
        else {
            return updates;
        };
        let Ok(path) = uri.to_file_path() else {
            return updates;
        };
        let Some(source_fingerprint) = source_fingerprint_for_path(&path, source_overlay) else {
            return updates;
        };
        let exports = typechecker::ModuleExports::collect(current_program, checker);
        updates.push(ModuleInterfaceUpdate {
            module_name,
            path: Some(path),
            source_fingerprint,
            interface_fingerprint: module_interface_fingerprint(&exports),
            exports,
            codegen_info: None,
            check_result: Some(check.clone()),
            is_current: true,
        });
    }

    updates
}
