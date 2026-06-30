use project_config::ProjectConfig;
use saga::{hex, project_config, typechecker};

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fs;
use std::hash::{Hash, Hasher};
use std::path::{Path, PathBuf};

pub(super) const BUILD_HASH: &str = env!("SAGA_BUILD_HASH");
pub(super) const BUILD_MANIFEST_VERSION: u32 = 7;

/// Build manifest written to `_build/<profile>/.manifest` for cache invalidation.
#[derive(serde::Serialize, serde::Deserialize)]
pub(super) struct BuildManifest {
    #[serde(default)]
    pub(super) manifest_version: u32,
    pub(super) entry_module: String,
    pub(super) source_file: String,
    pub(super) source_mtime: u64,
    pub(super) compiler_version: String,
    #[serde(default)]
    pub(super) profile: String,
    #[serde(default)]
    pub(super) stdlib_fingerprint: String,
    #[serde(default)]
    pub(super) input_fingerprints: Vec<BuildInputFingerprint>,
    #[serde(default)]
    pub(super) dependency_fingerprints: Vec<BuildDependencyFingerprint>,
    #[serde(default)]
    pub(super) output_artifacts: Vec<String>,
    #[serde(default)]
    pub(super) module_artifacts: Vec<BuildModuleArtifact>,
}

#[derive(Clone, Debug, Eq, PartialEq, serde::Serialize, serde::Deserialize)]
pub(super) struct BuildInputFingerprint {
    pub(super) path: String,
    pub(super) hash: String,
}

#[derive(Clone, Debug, Eq, PartialEq, serde::Serialize, serde::Deserialize)]
pub(super) struct BuildModuleArtifact {
    pub(super) module_name: String,
    pub(super) source_path: String,
    pub(super) source_hash: String,
    pub(super) interface_fingerprint: String,
    pub(super) core: String,
    pub(super) beam: String,
}

#[derive(Clone, Debug, Eq, PartialEq, serde::Serialize, serde::Deserialize)]
pub(super) struct BuildDependencyFingerprint {
    pub(super) id: String,
    pub(super) name: String,
    pub(super) kind: String,
    pub(super) fingerprint: String,
}

#[derive(Debug, Default, Eq, PartialEq)]
pub(super) struct InputFingerprintChanges {
    pub(super) added: Vec<String>,
    pub(super) removed: Vec<String>,
    pub(super) changed: Vec<String>,
}

pub(super) struct BuildManifestInput {
    pub(super) entry_module: String,
    pub(super) source_file: String,
    pub(super) source_mtime: u64,
    pub(super) profile: String,
    pub(super) stdlib_fingerprint: String,
    pub(super) input_fingerprints: Vec<BuildInputFingerprint>,
    pub(super) dependency_fingerprints: Vec<BuildDependencyFingerprint>,
    pub(super) output_artifacts: Vec<String>,
    pub(super) module_artifacts: Vec<BuildModuleArtifact>,
}

impl BuildManifest {
    fn path(build_dir: &Path) -> PathBuf {
        build_dir.join(".manifest")
    }

    pub(super) fn write(&self, build_dir: &Path) {
        let path = Self::path(build_dir);
        let content = toml::to_string(self).expect("failed to serialize manifest");
        write_atomic(&path, content.as_bytes(), "manifest");
    }

    pub(super) fn read(build_dir: &Path) -> Option<Self> {
        let path = Self::path(build_dir);
        let content = fs::read_to_string(&path).ok()?;
        toml::from_str(&content).ok()
    }
}

pub(super) fn file_mtime(path: &Path) -> u64 {
    fs::metadata(path)
        .and_then(|m| m.modified())
        .ok()
        .and_then(|t| t.duration_since(std::time::UNIX_EPOCH).ok())
        .map(|d| d.as_secs())
        .unwrap_or(0)
}

pub(super) fn write_atomic(path: &Path, bytes: &[u8], label: &str) {
    let tmp = path.with_extension(format!("tmp-{}", std::process::id()));
    fs::write(&tmp, bytes).unwrap_or_else(|e| {
        eprintln!("Error writing {}: {}", label, e);
    });
    fs::rename(&tmp, path).unwrap_or_else(|e| {
        let _ = fs::remove_file(&tmp);
        eprintln!("Error finalizing {}: {}", label, e);
    });
}

pub(super) fn content_hash(bytes: &[u8]) -> String {
    let mut hash = 0xcbf29ce484222325u64;
    for byte in bytes {
        hash ^= u64::from(*byte);
        hash = hash.wrapping_mul(0x100000001b3);
    }
    format!("{hash:016x}")
}

pub(super) fn module_interface_fingerprint(exports: &typechecker::ModuleExports) -> String {
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    hash_module_exports(exports, &mut hasher);
    format!("{:016x}", hasher.finish())
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

fn file_content_hash(path: &Path) -> Option<String> {
    fs::read(path).ok().map(|bytes| content_hash(&bytes))
}

fn push_input_fingerprint(
    inputs: &mut Vec<BuildInputFingerprint>,
    display_root: &Path,
    path: &Path,
) {
    let Some(hash) = file_content_hash(path) else {
        return;
    };
    let display_path = path
        .strip_prefix(display_root)
        .unwrap_or(path)
        .to_string_lossy()
        .to_string();
    inputs.push(BuildInputFingerprint {
        path: display_path,
        hash,
    });
}

fn collect_files_with_ext(dir: &Path, ext: &str, out: &mut Vec<PathBuf>) {
    let Ok(entries) = fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            collect_files_with_ext(&path, ext, out);
        } else if path.extension().is_some_and(|path_ext| path_ext == ext) {
            out.push(path);
        }
    }
}

fn collect_source_root_files(root: &Path, source_roots: &[&str], ext: &str) -> Vec<PathBuf> {
    let mut files = Vec::new();
    for source_root in source_roots {
        let dir = root.join(source_root);
        if dir.is_dir() {
            collect_files_with_ext(&dir, ext, &mut files);
        }
    }
    files.sort();
    files
}

fn collect_all_files(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            collect_all_files(&path, out);
        } else if path.is_file() {
            out.push(path);
        }
    }
}

fn display_path(display_root: &Path, path: &Path) -> String {
    path.strip_prefix(display_root)
        .unwrap_or(path)
        .to_string_lossy()
        .to_string()
}

fn hash_parts(parts: &[String]) -> String {
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    for part in parts {
        part.hash(&mut hasher);
    }
    format!("{:016x}", hasher.finish())
}

fn fingerprint_files(display_root: &Path, files: &[PathBuf]) -> Vec<String> {
    let mut parts = Vec::new();
    for path in files {
        let Some(hash) = file_content_hash(path) else {
            continue;
        };
        parts.push(format!("{}={}", display_path(display_root, path), hash));
    }
    parts.sort();
    parts
}

fn dependency_source_fingerprint(root: &Path, display_root: &Path) -> String {
    let mut files = Vec::new();
    for path in [root.join("project.toml"), root.join("saga.lock")] {
        if path.is_file() {
            files.push(path);
        }
    }
    files.extend(collect_source_root_files(root, &["src", "lib"], "saga"));
    files.extend(collect_source_root_files(
        root,
        &["src", "lib", "tests"],
        "erl",
    ));
    hash_parts(&fingerprint_files(display_root, &files))
}

fn dependency_artifact_fingerprint(root: &Path, display_root: &Path) -> String {
    let mut files = Vec::new();
    for dir_name in ["ebin", "priv"] {
        let dir = root.join(dir_name);
        if dir.is_dir() {
            collect_all_files(&dir, &mut files);
        }
    }
    hash_parts(&fingerprint_files(display_root, &files))
}

fn lock_entry_fingerprint(name: &str, lockfile: Option<&project_config::Lockfile>) -> String {
    let Some(entry) = lockfile.and_then(|lockfile| lockfile.deps.get(name)) else {
        return "unlocked".to_string();
    };
    hash_parts(&[
        entry.git.clone().unwrap_or_default(),
        entry.r#ref.clone().unwrap_or_default(),
        entry.commit.clone().unwrap_or_default(),
        entry.hex.clone().unwrap_or_default(),
        entry.version.clone().unwrap_or_default(),
        entry.checksum.clone().unwrap_or_default(),
    ])
}

fn dep_entry_parts(name: &str, dep: &project_config::DepEntry) -> Vec<String> {
    vec![
        name.to_string(),
        dep.path.clone().unwrap_or_default(),
        dep.git.clone().unwrap_or_default(),
        dep.tag.clone().unwrap_or_default(),
        dep.branch.clone().unwrap_or_default(),
        dep.rev.clone().unwrap_or_default(),
        dep.alias.clone().unwrap_or_default(),
        dep.version.clone().unwrap_or_default(),
    ]
}

fn dependency_root_for_fingerprint(
    project_root: &Path,
    config_dir: &Path,
    name: &str,
    dep: &project_config::DepEntry,
) -> PathBuf {
    if let Some(path) = &dep.path {
        config_dir
            .join(path)
            .canonicalize()
            .unwrap_or_else(|_| config_dir.join(path))
    } else {
        hex::package_dir(project_root, name)
    }
}

fn collect_dependency_fingerprints_recursive(
    project_root: &Path,
    config_dir: &Path,
    deps: &HashMap<String, project_config::DepEntry>,
    lockfile: Option<&project_config::Lockfile>,
    seen: &mut BTreeSet<String>,
    out: &mut Vec<BuildDependencyFingerprint>,
) {
    for (name, dep) in deps {
        let kind = if dep.is_hex() {
            "hex"
        } else if dep.git.is_some() {
            "git"
        } else {
            "path"
        };
        let root = dependency_root_for_fingerprint(project_root, config_dir, name, dep);
        let root_display = display_path(project_root, &root);
        let id = format!("{kind}:{name}:{root_display}");
        if !seen.insert(id.clone()) {
            continue;
        }

        let source_fingerprint = if dep.is_hex() {
            "opaque".to_string()
        } else {
            dependency_source_fingerprint(&root, project_root)
        };
        let artifact_fingerprint = dependency_artifact_fingerprint(&root, project_root);
        let mut parts = dep_entry_parts(name, dep);
        parts.extend([
            kind.to_string(),
            root_display,
            lock_entry_fingerprint(name, lockfile),
            source_fingerprint,
            artifact_fingerprint,
        ]);
        out.push(BuildDependencyFingerprint {
            id,
            name: name.clone(),
            kind: kind.to_string(),
            fingerprint: hash_parts(&parts),
        });

        if !dep.is_hex() {
            let dep_config = ProjectConfig::load(&root);
            if let Some(transitive) = &dep_config.deps {
                collect_dependency_fingerprints_recursive(
                    project_root,
                    &root,
                    transitive,
                    lockfile,
                    seen,
                    out,
                );
            }
        }
    }
}

pub(super) fn project_dependency_fingerprints(
    project_root: &Path,
    config: &ProjectConfig,
) -> Vec<BuildDependencyFingerprint> {
    let mut fingerprints = Vec::new();
    let mut seen = BTreeSet::new();
    let lockfile = project_config::Lockfile::load(project_root);
    if let Some(deps) = &config.deps {
        collect_dependency_fingerprints_recursive(
            project_root,
            project_root,
            deps,
            lockfile.as_ref(),
            &mut seen,
            &mut fingerprints,
        );
    }
    fingerprints.sort_by(|a, b| a.id.cmp(&b.id));
    fingerprints
}

pub(super) fn project_input_fingerprints(
    project_root: &Path,
    config: &ProjectConfig,
) -> Vec<BuildInputFingerprint> {
    let mut inputs = Vec::new();
    push_input_fingerprint(
        &mut inputs,
        project_root,
        &project_root.join("project.toml"),
    );
    push_input_fingerprint(&mut inputs, project_root, &project_root.join("saga.lock"));

    for path in collect_source_root_files(project_root, &["src", "lib"], "saga") {
        push_input_fingerprint(&mut inputs, project_root, &path);
    }
    for path in collect_source_root_files(project_root, &["src", "lib", "tests"], "erl") {
        push_input_fingerprint(&mut inputs, project_root, &path);
    }

    if let Some(deps) = &config.deps {
        for dep_root in project_config::dep_root_paths(project_root, deps) {
            push_input_fingerprint(&mut inputs, project_root, &dep_root.join("project.toml"));
            push_input_fingerprint(&mut inputs, project_root, &dep_root.join("saga.lock"));
            for path in collect_source_root_files(&dep_root, &["src", "lib"], "saga") {
                push_input_fingerprint(&mut inputs, project_root, &path);
            }
            for path in collect_source_root_files(&dep_root, &["src", "lib", "tests"], "erl") {
                push_input_fingerprint(&mut inputs, project_root, &path);
            }
        }
    }

    inputs.sort_by(|a, b| a.path.cmp(&b.path));
    inputs
}

pub(super) fn script_input_fingerprints(file: &str) -> Vec<BuildInputFingerprint> {
    let path = Path::new(file);
    let Some(hash) = file_content_hash(path) else {
        return Vec::new();
    };
    vec![BuildInputFingerprint {
        path: relative_source_path(file),
        hash,
    }]
}

pub(super) fn compare_input_fingerprints(
    expected: &[BuildInputFingerprint],
    actual: &[BuildInputFingerprint],
) -> Result<(), String> {
    if expected.is_empty() {
        return Err("manifest missing input fingerprints".to_string());
    }
    if expected == actual {
        return Ok(());
    }

    let expected_by_path: BTreeMap<&str, &str> = expected
        .iter()
        .map(|input| (input.path.as_str(), input.hash.as_str()))
        .collect();
    let actual_by_path: BTreeMap<&str, &str> = actual
        .iter()
        .map(|input| (input.path.as_str(), input.hash.as_str()))
        .collect();

    for path in expected_by_path.keys() {
        if !actual_by_path.contains_key(path) {
            return Err(format!("input removed: {path}"));
        }
    }
    for path in actual_by_path.keys() {
        if !expected_by_path.contains_key(path) {
            return Err(format!("input added: {path}"));
        }
    }
    for (path, expected_hash) in &expected_by_path {
        if actual_by_path
            .get(path)
            .is_some_and(|actual_hash| actual_hash != expected_hash)
        {
            return Err(format!("input changed: {path}"));
        }
    }

    Err("input fingerprints changed".to_string())
}

pub(super) fn compare_dependency_fingerprints(
    expected: &[BuildDependencyFingerprint],
    actual: &[BuildDependencyFingerprint],
) -> Result<(), String> {
    if expected == actual {
        return Ok(());
    }

    let expected_by_id: BTreeMap<&str, &BuildDependencyFingerprint> =
        expected.iter().map(|dep| (dep.id.as_str(), dep)).collect();
    let actual_by_id: BTreeMap<&str, &BuildDependencyFingerprint> =
        actual.iter().map(|dep| (dep.id.as_str(), dep)).collect();

    for id in expected_by_id.keys() {
        if !actual_by_id.contains_key(id) {
            return Err(format!("dependency removed: {id}"));
        }
    }
    for id in actual_by_id.keys() {
        if !expected_by_id.contains_key(id) {
            return Err(format!("dependency added: {id}"));
        }
    }
    for (id, expected_dep) in &expected_by_id {
        if actual_by_id
            .get(id)
            .is_some_and(|actual_dep| actual_dep.fingerprint != expected_dep.fingerprint)
        {
            return Err(format!("dependency changed: {id}"));
        }
    }

    Err("dependency fingerprints changed".to_string())
}

pub(super) fn input_fingerprint_changes(
    expected: &[BuildInputFingerprint],
    actual: &[BuildInputFingerprint],
) -> InputFingerprintChanges {
    let expected_by_path: BTreeMap<&str, &str> = expected
        .iter()
        .map(|input| (input.path.as_str(), input.hash.as_str()))
        .collect();
    let actual_by_path: BTreeMap<&str, &str> = actual
        .iter()
        .map(|input| (input.path.as_str(), input.hash.as_str()))
        .collect();

    let mut changes = InputFingerprintChanges::default();
    for path in expected_by_path.keys() {
        if !actual_by_path.contains_key(path) {
            changes.removed.push((*path).to_string());
        }
    }
    for path in actual_by_path.keys() {
        if !expected_by_path.contains_key(path) {
            changes.added.push((*path).to_string());
        }
    }
    for (path, expected_hash) in &expected_by_path {
        if actual_by_path
            .get(path)
            .is_some_and(|actual_hash| actual_hash != expected_hash)
        {
            changes.changed.push((*path).to_string());
        }
    }
    changes
}

pub(super) fn relative_source_path(file: &str) -> String {
    std::env::current_dir()
        .ok()
        .and_then(|cwd| {
            Path::new(file)
                .strip_prefix(&cwd)
                .ok()
                .map(|p| p.to_string_lossy().to_string())
        })
        .unwrap_or_else(|| file.to_string())
}

pub(super) fn write_build_manifest(build_dir: &Path, input: BuildManifestInput) {
    BuildManifest {
        manifest_version: BUILD_MANIFEST_VERSION,
        entry_module: input.entry_module,
        source_file: input.source_file,
        source_mtime: input.source_mtime,
        compiler_version: BUILD_HASH.to_string(),
        profile: input.profile,
        stdlib_fingerprint: input.stdlib_fingerprint,
        input_fingerprints: input.input_fingerprints,
        dependency_fingerprints: input.dependency_fingerprints,
        output_artifacts: input.output_artifacts,
        module_artifacts: input.module_artifacts,
    }
    .write(build_dir);
}

pub(super) fn missing_output_artifact(
    build_dir: &Path,
    manifest: &BuildManifest,
) -> Option<String> {
    if manifest.output_artifacts.is_empty() {
        return Some("manifest missing output artifacts".to_string());
    }

    manifest
        .output_artifacts
        .iter()
        .find(|artifact| !build_dir.join(artifact).exists())
        .cloned()
}

pub(super) fn module_artifacts_ready(
    build_dir: &Path,
    manifest: &BuildManifest,
    module_name: &str,
) -> bool {
    manifest
        .module_artifacts
        .iter()
        .find(|artifact| artifact.module_name == module_name)
        .is_some_and(|artifact| {
            build_dir.join(&artifact.core).exists() && build_dir.join(&artifact.beam).exists()
        })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn test_root(name: &str) -> PathBuf {
        let root =
            std::env::temp_dir().join(format!("saga-cache-test-{}-{}", name, std::process::id()));
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).unwrap();
        root
    }

    fn write(path: &Path, contents: &str) {
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, contents).unwrap();
    }

    fn fingerprint(path: &str, hash: &str) -> BuildInputFingerprint {
        BuildInputFingerprint {
            path: path.to_string(),
            hash: hash.to_string(),
        }
    }

    #[test]
    fn compare_input_fingerprints_accepts_identical_inputs() {
        let inputs = vec![fingerprint("src/Main.saga", "abc")];
        assert_eq!(compare_input_fingerprints(&inputs, &inputs), Ok(()));
    }

    #[test]
    fn compare_input_fingerprints_reports_added_removed_and_changed_inputs() {
        let expected = vec![fingerprint("src/Main.saga", "abc")];

        assert_eq!(
            compare_input_fingerprints(&expected, &[]),
            Err("input removed: src/Main.saga".to_string())
        );
        assert_eq!(
            compare_input_fingerprints(&expected, &[fingerprint("src/Main.saga", "def")]),
            Err("input changed: src/Main.saga".to_string())
        );
        assert_eq!(
            compare_input_fingerprints(
                &expected,
                &[
                    fingerprint("src/Main.saga", "abc"),
                    fingerprint("src/Extra.saga", "def")
                ]
            ),
            Err("input added: src/Extra.saga".to_string())
        );
    }

    #[test]
    fn project_input_fingerprints_are_content_based() {
        let root = test_root("content");
        let source = root.join("src/Main.saga");
        write(
            &root.join("project.toml"),
            "[project]\nname = \"cache-test\"\n",
        );
        write(&source, "module Main\n\nmain _ = ()\n");

        let first = project_input_fingerprints(&root, &ProjectConfig::default());
        write(&source, "module Main\n\nmain _ = ()\n");
        let second = project_input_fingerprints(&root, &ProjectConfig::default());

        assert_eq!(first, second);

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn project_input_fingerprints_detect_source_add_remove_and_change() {
        let root = test_root("project-changes");
        let main = root.join("src/Main.saga");
        let extra = root.join("src/Extra.saga");
        write(
            &root.join("project.toml"),
            "[project]\nname = \"cache-test\"\n",
        );
        write(&main, "module Main\n\nmain _ = ()\n");

        let initial = project_input_fingerprints(&root, &ProjectConfig::default());

        write(&extra, "module Extra\n\nvalue = 1\n");
        let with_extra = project_input_fingerprints(&root, &ProjectConfig::default());
        assert_eq!(
            compare_input_fingerprints(&initial, &with_extra),
            Err("input added: src/Extra.saga".to_string())
        );

        write(&main, "module Main\n\nmain _ = 1\n");
        let changed = project_input_fingerprints(&root, &ProjectConfig::default());
        assert_eq!(
            compare_input_fingerprints(&with_extra, &changed),
            Err("input changed: src/Main.saga".to_string())
        );

        fs::remove_file(&extra).unwrap();
        let removed = project_input_fingerprints(&root, &ProjectConfig::default());
        assert_eq!(
            compare_input_fingerprints(&with_extra, &removed),
            Err("input removed: src/Extra.saga".to_string())
        );

        let _ = fs::remove_dir_all(root);
    }

    fn dep_fingerprint(id: &str, hash: &str) -> BuildDependencyFingerprint {
        BuildDependencyFingerprint {
            id: id.to_string(),
            name: id.to_string(),
            kind: "path".to_string(),
            fingerprint: hash.to_string(),
        }
    }

    #[test]
    fn compare_dependency_fingerprints_reports_added_removed_and_changed_deps() {
        let expected = vec![dep_fingerprint("path:dep:/dep", "abc")];

        assert_eq!(
            compare_dependency_fingerprints(&expected, &[]),
            Err("dependency removed: path:dep:/dep".to_string())
        );
        assert_eq!(
            compare_dependency_fingerprints(&expected, &[dep_fingerprint("path:dep:/dep", "def")]),
            Err("dependency changed: path:dep:/dep".to_string())
        );
        assert_eq!(
            compare_dependency_fingerprints(
                &expected,
                &[
                    dep_fingerprint("path:dep:/dep", "abc"),
                    dep_fingerprint("path:extra:/extra", "def")
                ]
            ),
            Err("dependency added: path:extra:/extra".to_string())
        );
    }

    #[test]
    fn project_dependency_fingerprints_track_transitive_path_sources() {
        let root = test_root("transitive-deps");
        write(
            &root.join("project.toml"),
            "[deps]\nparent = { path = \"deps/parent\" }\n",
        );
        write(
            &root.join("deps/parent/project.toml"),
            "[library]\nmodule = \"Parent\"\nexpose = [\"Parent\"]\n\n[deps]\nchild = { path = \"../child\" }\n",
        );
        write(
            &root.join("deps/parent/src/Parent.saga"),
            "module Parent\n\npub fun value : Unit -> Int\nvalue _ = 1\n",
        );
        write(
            &root.join("deps/child/project.toml"),
            "[library]\nmodule = \"Child\"\nexpose = [\"Child\"]\n",
        );
        let child_source = root.join("deps/child/src/Child.saga");
        write(
            &child_source,
            "module Child\n\npub fun value : Unit -> Int\nvalue _ = 1\n",
        );
        let config = ProjectConfig::load(&root);

        let initial = project_dependency_fingerprints(&root, &config);
        assert_eq!(initial.len(), 2);
        assert!(initial.iter().any(|dep| dep.id.starts_with("path:parent:")));
        assert!(initial.iter().any(|dep| dep.id.starts_with("path:child:")));

        write(
            &child_source,
            "module Child\n\npub fun value : Unit -> Int\nvalue _ = 2\n",
        );
        let changed = project_dependency_fingerprints(&root, &config);

        assert_ne!(initial, changed);
        assert!(
            compare_dependency_fingerprints(&initial, &changed)
                .unwrap_err()
                .starts_with("dependency changed: path:child:")
        );

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn project_dependency_fingerprints_track_hex_artifacts() {
        let root = test_root("hex-deps");
        write(
            &root.join("project.toml"),
            "[deps]\njson = { version = \"1.0.0\" }\n",
        );
        write(
            &root.join("saga.lock"),
            "[deps.json]\nhex = \"json\"\nversion = \"1.0.0\"\nchecksum = \"abc\"\n",
        );
        let beam = root.join("deps/json/ebin/json.beam");
        write(&beam, "beam-v1");
        let config = ProjectConfig::load(&root);

        let initial = project_dependency_fingerprints(&root, &config);
        assert_eq!(initial.len(), 1);
        assert_eq!(initial[0].kind, "hex");

        write(&beam, "beam-v2");
        let changed = project_dependency_fingerprints(&root, &config);

        assert_ne!(initial, changed);
        assert_eq!(
            compare_dependency_fingerprints(&initial, &changed),
            Err("dependency changed: hex:json:deps/json".to_string())
        );

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn script_input_fingerprints_track_script_content() {
        let root = test_root("script");
        let script = root.join("hello.saga");
        write(&script, "main _ = ()\n");

        let initial = script_input_fingerprints(script.to_str().unwrap());
        write(&script, "main _ = 1\n");
        let changed = script_input_fingerprints(script.to_str().unwrap());

        assert_eq!(
            compare_input_fingerprints(&initial, &changed),
            Err(format!("input changed: {}", script.display()))
        );

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn missing_output_artifact_requires_manifest_outputs_to_exist() {
        let root = test_root("outputs");
        let manifest = BuildManifest {
            manifest_version: BUILD_MANIFEST_VERSION,
            entry_module: "main".to_string(),
            source_file: "project.toml".to_string(),
            source_mtime: 0,
            compiler_version: BUILD_HASH.to_string(),
            profile: "dev".to_string(),
            stdlib_fingerprint: "stdlib".to_string(),
            input_fingerprints: vec![fingerprint("project.toml", "abc")],
            dependency_fingerprints: Vec::new(),
            output_artifacts: vec!["main.beam".to_string(), "app_worker.beam".to_string()],
            module_artifacts: vec![],
        };

        write(&root.join("main.beam"), "");
        assert_eq!(
            missing_output_artifact(&root, &manifest),
            Some("app_worker.beam".to_string())
        );

        write(&root.join("app_worker.beam"), "");
        assert_eq!(missing_output_artifact(&root, &manifest), None);

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn input_fingerprint_changes_reports_all_changes() {
        let expected = vec![
            fingerprint("project.toml", "aaa"),
            fingerprint("src/A.saga", "bbb"),
            fingerprint("src/Removed.saga", "ccc"),
        ];
        let actual = vec![
            fingerprint("project.toml", "aaa"),
            fingerprint("src/A.saga", "changed"),
            fingerprint("src/Added.saga", "ddd"),
        ];

        assert_eq!(
            input_fingerprint_changes(&expected, &actual),
            InputFingerprintChanges {
                added: vec!["src/Added.saga".to_string()],
                removed: vec!["src/Removed.saga".to_string()],
                changed: vec!["src/A.saga".to_string()],
            }
        );
    }

    #[test]
    fn module_artifacts_ready_requires_core_and_beam() {
        let root = test_root("module-artifacts");
        let manifest = BuildManifest {
            manifest_version: BUILD_MANIFEST_VERSION,
            entry_module: "main".to_string(),
            source_file: "project.toml".to_string(),
            source_mtime: 0,
            compiler_version: BUILD_HASH.to_string(),
            profile: "dev".to_string(),
            stdlib_fingerprint: "stdlib".to_string(),
            input_fingerprints: vec![fingerprint("project.toml", "abc")],
            dependency_fingerprints: Vec::new(),
            output_artifacts: vec!["main.beam".to_string()],
            module_artifacts: vec![BuildModuleArtifact {
                module_name: "Main".to_string(),
                source_path: "src/Main.saga".to_string(),
                source_hash: "abc".to_string(),
                interface_fingerprint: "iface".to_string(),
                core: "main.core".to_string(),
                beam: "main.beam".to_string(),
            }],
        };

        write(&root.join("main.core"), "");
        assert!(!module_artifacts_ready(&root, &manifest, "Main"));
        write(&root.join("main.beam"), "");
        assert!(module_artifacts_ready(&root, &manifest, "Main"));
        assert!(!module_artifacts_ready(&root, &manifest, "Other"));

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn module_interface_fingerprint_is_order_stable_and_ignores_docs() {
        let int_scheme = typechecker::Scheme {
            forall: Vec::new(),
            constraints: Vec::new(),
            ty: typechecker::Type::Con("Int".to_string(), Vec::new()),
        };
        let bool_scheme = typechecker::Scheme {
            forall: Vec::new(),
            constraints: Vec::new(),
            ty: typechecker::Type::Con("Bool".to_string(), Vec::new()),
        };

        let mut left = typechecker::ModuleExports {
            bindings: vec![
                ("two".to_string(), int_scheme.clone()),
                ("one".to_string(), int_scheme.clone()),
            ],
            ..Default::default()
        };
        left.binding_origins
            .insert("one".to_string(), "Example.one".to_string());
        left.binding_origins
            .insert("two".to_string(), "Example.two".to_string());
        left.type_arity.insert("Pair".to_string(), 2);
        left.type_arity.insert("Box".to_string(), 1);
        left.doc_comments.insert(
            "one".to_string(),
            vec!["docs do not force rebuild".to_string()],
        );

        let mut right = typechecker::ModuleExports {
            bindings: vec![
                ("one".to_string(), int_scheme.clone()),
                ("two".to_string(), int_scheme),
            ],
            ..Default::default()
        };
        right
            .binding_origins
            .insert("two".to_string(), "Example.two".to_string());
        right
            .binding_origins
            .insert("one".to_string(), "Example.one".to_string());
        right.type_arity.insert("Box".to_string(), 1);
        right.type_arity.insert("Pair".to_string(), 2);
        right
            .doc_comments
            .insert("one".to_string(), vec!["different docs".to_string()]);

        assert_eq!(
            module_interface_fingerprint(&left),
            module_interface_fingerprint(&right)
        );

        right.bindings[0].1 = bool_scheme;
        assert_ne!(
            module_interface_fingerprint(&left),
            module_interface_fingerprint(&right)
        );
    }
}
