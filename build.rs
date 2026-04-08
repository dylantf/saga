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

    // Tell cargo to rerun when stdlib files change (so include_str! picks up changes)
    let mut stdlib_files: Vec<_> = std::fs::read_dir("src/stdlib")
        .expect("cannot read src/stdlib")
        .filter_map(|e| e.ok())
        .map(|e| e.path())
        .filter(|p| p.extension().is_some_and(|ext| ext == "dy" || ext == "erl"))
        .collect();
    stdlib_files.sort();
    for path in &stdlib_files {
        println!("cargo:rerun-if-changed={}", path.display());
    }
    // Compiler changes also need to invalidate DYLANG_BUILD_HASH so stdlib and
    // project caches are not reused across incompatible lowering/codegen builds.
    println!("cargo:rerun-if-changed=src");
}
