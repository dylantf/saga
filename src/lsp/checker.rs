use std::path::{Path, PathBuf};

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
    typechecker::Checker::with_prelude(project_root).expect("failed to initialize checker")
}
