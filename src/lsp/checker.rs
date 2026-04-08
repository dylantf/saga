use std::path::{Path, PathBuf};

use dylang::project_config::{self, ProjectConfig};
use dylang::typechecker;

/// Walk up from `start` looking for a directory containing `project.toml`.
pub fn find_project_root(start: &Path) -> Option<PathBuf> {
    let mut dir = start.to_path_buf();
    loop {
        if dir.join("project.toml").exists() {
            return Some(dir);
        }
        if !dir.pop() {
            return None;
        }
    }
}

pub fn make_checker(project_root: Option<PathBuf>) -> typechecker::Checker {
    let mut checker = typechecker::Checker::with_prelude(project_root.clone())
        .expect("failed to initialize checker");

    // Resolve dependencies if we have a project root with deps configured
    if let Some(root) = &project_root {
        let config = ProjectConfig::load(root);
        if let Some(deps) = &config.deps
            && let Err(e) = project_config::resolve_deps(&mut checker, root, deps)
        {
            eprintln!("[LSP] Warning: failed to resolve dependencies: {}", e);
        }
    }

    checker
}
