use std::collections::HashMap;
use std::path::{Path, PathBuf};

/// Map from module name (e.g. "Foo.Bar.Baz") to the file path that declares it.
pub type ModuleMap = HashMap<String, PathBuf>;

/// Visibility metadata for a module: which package it originates from and whether
/// it is exposed across the package boundary (listed in `[library] expose`).
#[derive(Debug, Clone)]
pub struct ModuleVisibility {
    pub package: String,
    pub exposed: bool,
}

/// Map from module name to its visibility metadata. Modules without an entry
/// are treated as local (no package, accessible only to other local modules).
pub type ModuleVisibilityMap = HashMap<String, ModuleVisibility>;

/// Scan all .saga files under `root`, extract their `module` declarations,
/// and build a map from declared module name to file path.
pub fn scan_project_modules(root: &Path) -> Result<ModuleMap, String> {
    let mut map = ModuleMap::new();
    for entry_point in ["src", "lib"] {
        let dir = root.join(entry_point);
        if dir.is_dir() {
            scan_dir(&dir, root, &mut map, &[], false)?;
        }
    }
    Ok(map)
}

/// Scan a source directory for modules without skipping `tests/` subdirectories.
/// Allows the reserved `Std` namespace, since this is used to render the stdlib's
/// own docs and similar tooling outside the project-validation path.
pub fn scan_source_dir(root: &Path) -> Result<ModuleMap, String> {
    let mut map = ModuleMap::new();
    scan_dir(root, root, &mut map, &["_build", "deps"], true)?;
    Ok(map)
}

fn scan_dir(
    dir: &Path,
    root: &Path,
    map: &mut ModuleMap,
    skip_dirs: &[&str],
    allow_std: bool,
) -> Result<(), String> {
    let entries =
        std::fs::read_dir(dir).map_err(|e| format!("cannot read {}: {}", dir.display(), e))?;
    for entry in entries {
        let entry = entry.map_err(|e| format!("read_dir error: {}", e))?;
        let path = entry.path();
        if path.is_dir() {
            if path
                .file_name()
                .is_some_and(|n| skip_dirs.iter().any(|s| n == *s))
            {
                continue;
            }
            scan_dir(&path, root, map, skip_dirs, allow_std)?;
        } else if path.extension().is_some_and(|ext| ext == "saga") {
            match extract_module_name(&path) {
                Ok(Some(module_name)) => {
                    if !allow_std && (module_name.starts_with("Std.") || module_name == "Std") {
                        let rel = path.strip_prefix(root).unwrap_or(&path);
                        return Err(format!(
                            "module '{}' in {} uses the reserved `Std` namespace",
                            module_name,
                            rel.display()
                        ));
                    }
                    if let Some(existing) = map.get(&module_name) {
                        return Err(format!(
                            "module '{}' declared in both {} and {}",
                            module_name,
                            existing.display(),
                            path.display()
                        ));
                    }
                    map.insert(module_name, path);
                }
                Ok(None) => {
                    let rel = path.strip_prefix(root).unwrap_or(&path);
                    eprintln!(
                        "warning: {} has no module declaration, skipping",
                        rel.display()
                    );
                }
                Err(e) => {
                    let rel = path.strip_prefix(root).unwrap_or(&path);
                    eprintln!("warning: could not scan {}: {}", rel.display(), e);
                }
            }
        }
    }
    Ok(())
}

/// Extract the module name from a .saga file by lexing and scanning for the
/// first `module` declaration. Returns None if no module declaration is found.
fn extract_module_name(path: &Path) -> Result<Option<String>, String> {
    let source = std::fs::read_to_string(path)
        .map_err(|e| format!("cannot read {}: {}", path.display(), e))?;
    let tokens = crate::lexer::Lexer::new(&source)
        .lex()
        .map_err(|e| format!("lex error: {}", e.message))?;

    // Scan tokens for: Module UpperIdent (.UpperIdent)*
    use crate::token::Token;
    let mut i = 0;
    while i < tokens.len() {
        if matches!(tokens[i].token, Token::Module) {
            i += 1;
            // Collect the dotted module path
            let mut parts: Vec<String> = Vec::new();
            if i < tokens.len()
                && let Token::UpperIdent(name) = &tokens[i].token
            {
                parts.push(name.clone());
                i += 1;
                while i + 1 < tokens.len() {
                    if matches!(tokens[i].token, Token::Dot) {
                        if let Token::UpperIdent(name) = &tokens[i + 1].token {
                            parts.push(name.clone());
                            i += 2;
                        } else {
                            break;
                        }
                    } else {
                        break;
                    }
                }
            }
            if !parts.is_empty() {
                return Ok(Some(parts.join(".")));
            }
        }
        i += 1;
    }
    Ok(None)
}

/// Returns the embedded source for a builtin stdlib module, if it exists.
/// All builtin stdlib modules: (module name, source).
pub const BUILTIN_MODULES: &[(&str, &str)] = &[
    ("Std.Base", include_str!("../../stdlib/Base.saga")),
    ("Std.Maybe", include_str!("../../stdlib/Maybe.saga")),
    ("Std.Result", include_str!("../../stdlib/Result.saga")),
    ("Std.List", include_str!("../../stdlib/List.saga")),
    ("Std.Bool", include_str!("../../stdlib/Bool.saga")),
    ("Std.Dict", include_str!("../../stdlib/Dict.saga")),
    ("Std.Int", include_str!("../../stdlib/Int.saga")),
    ("Std.Float", include_str!("../../stdlib/Float.saga")),
    ("Std.String", include_str!("../../stdlib/String.saga")),
    ("Std.Regex", include_str!("../../stdlib/Regex.saga")),
    ("Std.Tuple", include_str!("../../stdlib/Tuple.saga")),
    ("Std.Actor", include_str!("../../stdlib/Actor.saga")),
    ("Std.Fail", include_str!("../../stdlib/Fail.saga")),
    ("Std.Control", include_str!("../../stdlib/Control.saga")),
    (
        "Std.Supervisor",
        include_str!("../../stdlib/Supervisor.saga"),
    ),
    ("Std.Async", include_str!("../../stdlib/Async.saga")),
    ("Std.IO.Unsafe", include_str!("../../stdlib/IO.Unsafe.saga")),
    ("Std.IO", include_str!("../../stdlib/IO.saga")),
    ("Std.Math", include_str!("../../stdlib/Math.saga")),
    ("Std.Test", include_str!("../../stdlib/Test.saga")),
    ("Std.Process", include_str!("../../stdlib/Process.saga")),
    ("Std.File", include_str!("../../stdlib/File.saga")),
    ("Std.Set", include_str!("../../stdlib/Set.saga")),
    ("Std.Time", include_str!("../../stdlib/Time.saga")),
    ("Std.DateTime", include_str!("../../stdlib/DateTime.saga")),
    ("Std.BitString", include_str!("../../stdlib/BitString.saga")),
    ("Std.Dynamic", include_str!("../../stdlib/Dynamic.saga")),
    ("Std.Ref", include_str!("../../stdlib/Ref.saga")),
    ("Std.AtomicRef", include_str!("../../stdlib/AtomicRef.saga")),
    ("Std.Vec", include_str!("../../stdlib/Vec.saga")),
    ("Std.Stream", include_str!("../../stdlib/Stream.saga")),
    ("Std.Array", include_str!("../../stdlib/Array.saga")),
    ("Std.Env", include_str!("../../stdlib/Env.saga")),
    ("Std.Generic", include_str!("../../stdlib/Generic.saga")),
];

pub fn builtin_module_source(module_path: &[String]) -> Option<&'static str> {
    let name = module_path.join(".");
    BUILTIN_MODULES
        .iter()
        .find(|(mod_name, _)| *mod_name == name)
        .map(|(_, src)| *src)
}
