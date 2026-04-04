use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

fn main() {
    let git_hash = std::process::Command::new("git")
        .args(["rev-parse", "--short", "HEAD"])
        .output()
        .ok()
        .and_then(|o| String::from_utf8(o.stdout).ok())
        .map(|s| s.trim().to_string())
        .unwrap_or_else(|| "unknown".into());

    let dirty = std::process::Command::new("git")
        .args(["status", "--porcelain"])
        .output()
        .ok()
        .map(|o| !o.stdout.is_empty())
        .unwrap_or(false);

    let build_hash = if dirty {
        let timestamp = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_secs();
        format!("{git_hash}-dev.{timestamp}")
    } else {
        git_hash
    };

    println!("cargo:rustc-env=DYLANG_BUILD_HASH={build_hash}");

    // Hash all stdlib source files (.dy + .erl) for cache invalidation.
    // The stdlib cache is keyed on this hash so it only rebuilds when
    // stdlib source actually changes, not on every compiler rebuild.
    let mut hasher = DefaultHasher::new();
    let mut stdlib_files: Vec<_> = std::fs::read_dir("src/stdlib")
        .expect("cannot read src/stdlib")
        .filter_map(|e| e.ok())
        .map(|e| e.path())
        .filter(|p| {
            p.extension()
                .is_some_and(|ext| ext == "dy" || ext == "erl")
        })
        .collect();
    // Sort for deterministic hashing
    stdlib_files.sort();
    for path in &stdlib_files {
        let content = std::fs::read(path).expect("cannot read stdlib file");
        path.file_name().unwrap().to_str().unwrap().hash(&mut hasher);
        content.hash(&mut hasher);
        // Tell cargo to rerun if this file changes
        println!("cargo:rerun-if-changed={}", path.display());
    }
    let stdlib_hash = format!("{:016x}", hasher.finish());
    println!("cargo:rustc-env=DYLANG_STDLIB_HASH={stdlib_hash}");
}
