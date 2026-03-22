pub mod build;
pub mod commands;
pub mod diagnostics;

use std::path::PathBuf;

/// Walk up from cwd looking for project.toml.
pub fn find_project_root() -> Option<PathBuf> {
    let mut dir = std::env::current_dir().ok()?;
    loop {
        if dir.join("project.toml").exists() {
            return Some(dir);
        }
        if !dir.pop() {
            return None;
        }
    }
}
