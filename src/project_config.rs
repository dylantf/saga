use serde::Deserialize;
use std::collections::HashMap;
use std::path::Path;

use crate::typechecker;

/// Parsed project.toml configuration.
#[derive(Debug, Deserialize, Default)]
pub struct ProjectConfig {
    #[serde(default)]
    pub project: ProjectSection,
    #[serde(default)]
    pub library: Option<LibrarySection>,
    #[serde(default)]
    pub bin: Option<BinSection>,
    #[serde(default)]
    pub deps: Option<HashMap<String, DepEntry>>,
}

#[derive(Debug, Deserialize, Default)]
#[allow(dead_code)]
pub struct ProjectSection {
    #[serde(default)]
    pub name: Option<String>,
    #[serde(default)]
    pub tests_dir: Option<String>,
}

#[derive(Debug, Deserialize, Clone)]
pub struct LibrarySection {
    pub module: String,
    pub expose: Vec<String>,
}

#[derive(Debug, Deserialize, Clone, Default)]
pub struct BinSection {
    #[serde(default)]
    pub main: Option<String>,
}

#[derive(Debug, Deserialize, Clone)]
pub struct DepEntry {
    pub path: String,
    #[serde(rename = "as")]
    pub alias: Option<String>,
}

impl ProjectConfig {
    pub fn load(project_root: &Path) -> Self {
        let path = project_root.join("project.toml");
        match std::fs::read_to_string(&path) {
            Ok(contents) => toml::from_str(&contents).unwrap_or_else(|e| {
                eprintln!("Warning: failed to parse project.toml: {}", e);
                ProjectConfig::default()
            }),
            Err(_) => ProjectConfig::default(),
        }
    }

    pub fn tests_dir(&self) -> &str {
        self.project.tests_dir.as_deref().unwrap_or("tests")
    }

    /// The main entry point file. Defaults to "Main.dy".
    pub fn main_file(&self) -> &str {
        self.bin
            .as_ref()
            .and_then(|b| b.main.as_deref())
            .unwrap_or("Main.dy")
    }

    /// Whether this project can be run (has a binary entry point).
    pub fn is_bin(&self) -> bool {
        // Backward compat: if no [library] or [bin] section, treat as bin
        if self.library.is_none() && self.bin.is_none() {
            return true;
        }
        self.bin.is_some()
    }

    /// Whether this project is a library.
    #[allow(dead_code)]
    pub fn is_library(&self) -> bool {
        self.library.is_some()
    }

    /// Validate the config, returning errors if any.
    pub fn validate(&self) -> Result<(), String> {
        if let Some(lib) = &self.library {
            for exposed in &lib.expose {
                if exposed != &lib.module && !exposed.starts_with(&format!("{}.", lib.module)) {
                    return Err(format!(
                        "exposed module '{}' must be prefixed by library module '{}'",
                        exposed, lib.module
                    ));
                }
            }
        }

        if let Some(deps) = &self.deps {
            for (name, dep) in deps {
                let dep_path = Path::new(&dep.path);
                if !dep_path.exists() {
                    return Err(format!(
                        "dependency '{}' path '{}' does not exist",
                        name, dep.path
                    ));
                }
                if !dep_path.join("project.toml").exists() {
                    return Err(format!(
                        "dependency '{}' at '{}' has no project.toml",
                        name, dep.path
                    ));
                }
            }
        }

        Ok(())
    }
}

/// Resolve dependencies and merge their modules into the checker's module map.
pub fn resolve_deps(
    checker: &mut typechecker::Checker,
    project_root: &Path,
    deps: &HashMap<String, DepEntry>,
) -> Result<(), String> {
    let mut dep_modules = typechecker::ModuleMap::new();

    for (dep_name, dep_entry) in deps {
        let dep_path = project_root.join(&dep_entry.path);
        let dep_path = dep_path
            .canonicalize()
            .map_err(|e| format!("dependency '{}' path '{}': {}", dep_name, dep_entry.path, e))?;

        eprintln!("  Resolving dependency '{}'...", dep_name);

        let dep_config = ProjectConfig::load(&dep_path);
        let lib = dep_config.library.ok_or_else(|| {
            format!(
                "dependency '{}' at '{}' has no [library] section in project.toml",
                dep_name,
                dep_path.display()
            )
        })?;

        let dep_map = typechecker::scan_project_modules(&dep_path).map_err(|e| {
            format!("scanning dependency '{}': {}", dep_name, e)
        })?;

        for exposed in &lib.expose {
            let file_path = dep_map.get(exposed).ok_or_else(|| {
                format!(
                    "dependency '{}' exposes module '{}' but it was not found",
                    dep_name, exposed
                )
            })?.clone();

            let mapped_name = if let Some(alias) = &dep_entry.alias {
                if exposed == &lib.module {
                    alias.clone()
                } else if let Some(suffix) = exposed.strip_prefix(&format!("{}.", lib.module)) {
                    format!("{}.{}", alias, suffix)
                } else {
                    exposed.clone()
                }
            } else {
                exposed.clone()
            };

            if let Some(existing) = dep_modules.get(&mapped_name) {
                return Err(format!(
                    "module name collision '{}' between dependency '{}' and another dependency ({}). \
                     Hint: use `as` in project.toml to alias one of the dependencies",
                    mapped_name, dep_name, existing.display()
                ));
            }

            dep_modules.insert(mapped_name, file_path);
        }
    }

    if !dep_modules.is_empty() {
        let module_names: Vec<&str> = dep_modules.keys().map(|s| s.as_str()).collect();
        eprintln!(
            "  Resolved {} dependency module(s): {}",
            module_names.len(),
            module_names.join(", ")
        );
        let mut map = checker.module_map().cloned().unwrap_or_default();
        for (name, path) in dep_modules {
            if let Some(existing) = map.get(&name) {
                return Err(format!(
                    "dependency module '{}' conflicts with local module at {}. \
                     Hint: use `as` in project.toml to alias the dependency",
                    name,
                    existing.display()
                ));
            }
            map.insert(name, path);
        }
        checker.set_module_map(map);
    }

    Ok(())
}
