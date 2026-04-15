use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::path::{Path, PathBuf};

/// Directory for a dependency within the project's deps/ folder.
pub fn package_dir(project_root: &Path, name: &str) -> PathBuf {
    project_root.join("deps").join(name)
}

/// Path to the ebin directory for a dependency.
pub fn package_ebin_dir(project_root: &Path, name: &str) -> PathBuf {
    package_dir(project_root, name).join("ebin")
}

/// Whether a dependency is already compiled in this project.
/// Checks for `.beam` files in ebin/, not just the directory existing,
/// because Hex packages can ship an ebin/ with only a `.app` file.
pub fn is_compiled(project_root: &Path, name: &str) -> bool {
    let ebin = package_ebin_dir(project_root, name);
    ebin.exists()
        && std::fs::read_dir(&ebin)
            .map(|entries| {
                entries
                    .flatten()
                    .any(|e| e.path().extension().is_some_and(|ext| ext == "beam"))
            })
            .unwrap_or(false)
}

/// Global cache directory for Hex tarball downloads.
fn hex_tarball_cache_dir() -> PathBuf {
    let home = std::env::var("HOME").unwrap_or_else(|_| ".".to_string());
    PathBuf::from(home).join(".saga").join("cache").join("hex")
}

// --- Hex API types ---

#[derive(Debug, Deserialize, Serialize)]
pub struct HexRelease {
    pub version: String,
    pub checksum: String,
    pub requirements: HashMap<String, HexRequirement>,
    pub meta: HexReleaseMeta,
}

#[derive(Debug, Deserialize, Serialize)]
pub struct HexRequirement {
    pub optional: bool,
    pub app: String,
    pub requirement: String,
}

#[derive(Debug, Deserialize, Serialize)]
pub struct HexReleaseMeta {
    pub app: String,
    pub build_tools: Vec<String>,
}

#[derive(Debug, Deserialize)]
pub struct HexPackageInfo {
    pub name: String,
    pub releases: Vec<HexPackageRelease>,
}

#[derive(Debug, Deserialize)]
pub struct HexPackageRelease {
    pub version: String,
}

// --- API client ---

fn hex_client() -> reqwest::blocking::Client {
    reqwest::blocking::Client::builder()
        .user_agent("saga")
        .build()
        .expect("failed to create HTTP client")
}

/// Fetch release metadata from the Hex API.
pub fn fetch_release(name: &str, version: &str) -> Result<HexRelease, String> {
    let url = format!("https://hex.pm/api/packages/{}/releases/{}", name, version);
    let resp = hex_client()
        .get(&url)
        .header("Accept", "application/json")
        .send()
        .map_err(|e| format!("failed to fetch {}: {}", url, e))?;

    if !resp.status().is_success() {
        return Err(format!(
            "Hex package '{}' version '{}' not found (HTTP {})",
            name,
            version,
            resp.status()
        ));
    }

    resp.json::<HexRelease>().map_err(|e| {
        format!(
            "failed to parse release metadata for {}-{}: {}",
            name, version, e
        )
    })
}

/// Fetch package info (all versions) from the Hex API.
pub fn fetch_package_info(name: &str) -> Result<HexPackageInfo, String> {
    let url = format!("https://hex.pm/api/packages/{}", name);
    let resp = hex_client()
        .get(&url)
        .header("Accept", "application/json")
        .send()
        .map_err(|e| format!("failed to fetch {}: {}", url, e))?;

    if !resp.status().is_success() {
        return Err(format!(
            "Hex package '{}' not found (HTTP {})",
            name,
            resp.status()
        ));
    }

    resp.json::<HexPackageInfo>()
        .map_err(|e| format!("failed to parse package info for {}: {}", name, e))
}

// --- Tarball download & extraction ---

/// Download a Hex tarball and extract its contents into deps/{name}/.
/// Returns the package directory path.
pub fn download_and_extract(
    project_root: &Path,
    name: &str,
    version: &str,
) -> Result<PathBuf, String> {
    let pkg_dir = package_dir(project_root, name);

    // Already extracted?
    if pkg_dir.join("src").exists() {
        return Ok(pkg_dir);
    }

    // Check global tarball cache first
    let cache_dir = hex_tarball_cache_dir();
    let tarball_cache = cache_dir.join(format!("{}-{}.tar", name, version));
    let tarball_bytes = if tarball_cache.exists() {
        std::fs::read(&tarball_cache)
            .map_err(|e| format!("failed to read cached tarball: {}", e))?
            .into()
    } else {
        let url = format!("https://repo.hex.pm/tarballs/{}-{}.tar", name, version);
        let resp = hex_client()
            .get(&url)
            .send()
            .map_err(|e| format!("failed to download {}: {}", url, e))?;

        if !resp.status().is_success() {
            return Err(format!(
                "failed to download Hex tarball for {}-{} (HTTP {})",
                name,
                version,
                resp.status()
            ));
        }

        let bytes = resp
            .bytes()
            .map_err(|e| format!("failed to read tarball bytes: {}", e))?;

        // Cache the tarball globally
        std::fs::create_dir_all(&cache_dir)
            .map_err(|e| format!("failed to create tarball cache dir: {}", e))?;
        std::fs::write(&tarball_cache, &bytes)
            .map_err(|e| format!("failed to cache tarball: {}", e))?;

        bytes
    };

    std::fs::create_dir_all(&pkg_dir).map_err(|e| format!("failed to create deps dir: {}", e))?;

    // The outer tarball is uncompressed and contains: VERSION, CHECKSUM, metadata.config, contents.tar.gz
    let mut outer_tar = tar::Archive::new(tarball_bytes.as_ref());
    let mut contents_tar_gz = None;

    for entry in outer_tar
        .entries()
        .map_err(|e| format!("failed to read outer tarball: {}", e))?
    {
        let mut entry = entry.map_err(|e| format!("failed to read tar entry: {}", e))?;
        let path = entry
            .path()
            .map_err(|e| format!("failed to read tar entry path: {}", e))?
            .to_path_buf();

        if path.to_string_lossy() == "contents.tar.gz" {
            let mut buf = Vec::new();
            std::io::Read::read_to_end(&mut entry, &mut buf)
                .map_err(|e| format!("failed to read contents.tar.gz: {}", e))?;
            contents_tar_gz = Some(buf);
        }
    }

    let contents_bytes =
        contents_tar_gz.ok_or_else(|| "contents.tar.gz not found in Hex tarball".to_string())?;

    // Extract the inner gzipped tarball
    let gz = flate2::read::GzDecoder::new(contents_bytes.as_slice());
    let mut inner_tar = tar::Archive::new(gz);
    inner_tar
        .unpack(&pkg_dir)
        .map_err(|e| format!("failed to extract contents: {}", e))?;

    Ok(pkg_dir)
}

// --- Compilation ---

/// Compile a package using erlang.mk (make app).
/// `pkg_dir` is the directory containing the Makefile and erlang.mk.
/// `project_root` is used to set DEPS_DIR so erlang.mk finds sibling deps.
/// Returns the ebin directory path.
pub fn compile_with_erlang_mk(
    pkg_dir: &Path,
    name: &str,
    project_root: &Path,
) -> Result<PathBuf, String> {
    let ebin_dir = pkg_dir.join("ebin");
    let deps_dir = project_root.join("deps");

    // Remove pre-existing ebin/ from the Hex tarball (contains only .app,
    // no .beam files). erlang.mk treats an existing ebin/ as "already built"
    // and skips compilation.
    if ebin_dir.exists() {
        let _ = std::fs::remove_dir_all(&ebin_dir);
    }

    let status = std::process::Command::new("make")
        .args(["app"])
        .current_dir(pkg_dir)
        .env("DEPS_DIR", &deps_dir)
        .status()
        .map_err(|e| format!("failed to run make: {}", e))?;

    if !status.success() {
        return Err(format!("make app failed for '{}'", name));
    }

    if !ebin_dir.exists() {
        return Err(format!(
            "make app compiled '{}' but no ebin directory was produced",
            name
        ));
    }

    Ok(ebin_dir)
}

/// Compile a package using rebar3 bare compile.
/// `pkg_dir` is the directory containing the source and rebar.config.
/// `project_root` is used to find dependency ebin dirs for `--paths`.
/// `name` is used for error messages and to find rebar3's output dir.
/// Returns the ebin directory path.
pub fn compile_with_rebar3(
    pkg_dir: &Path,
    name: &str,
    project_root: &Path,
) -> Result<PathBuf, String> {
    let ebin_dir = pkg_dir.join("ebin");

    // Build --paths: the package's own ebin dir plus all dep ebin dirs
    let dep_ebin_dirs = collect_dep_ebin_dirs(project_root);
    let mut paths = vec![ebin_dir.to_string_lossy().to_string()];
    for dir in &dep_ebin_dirs {
        paths.push(dir.to_string_lossy().to_string());
    }
    let paths_arg = paths.join(":");

    // rebar3 bare compile outputs to <output_dir>/ebin/.
    // Point it at the package dir so ebin/ lands where we expect.
    // ERL_LIBS lets rebar3 find dep application roots for -include_lib resolution
    let deps_dir = project_root.join("deps");

    let status = std::process::Command::new("rebar3")
        .args(["bare", "compile", "--paths", &paths_arg])
        .current_dir(pkg_dir)
        .env("REBAR_BARE_COMPILER_OUTPUT_DIR", pkg_dir)
        .env("REBAR_PROFILE", "prod")
        .env("ERL_LIBS", &deps_dir)
        .status()
        .map_err(|e| {
            if e.kind() == std::io::ErrorKind::NotFound {
                format!(
                    "dependency '{}' requires rebar3 for compilation, \
                     but rebar3 is not on PATH. Install rebar3: https://rebar3.org",
                    name
                )
            } else {
                format!("failed to run rebar3: {}", e)
            }
        })?;

    if !status.success() {
        let _ = std::fs::remove_dir_all(&ebin_dir);
        return Err(format!("rebar3 bare compile failed for '{}'", name));
    }

    // rebar3 may put ebin inside _build — copy beams to our ebin dir if needed
    let rebar_ebin = pkg_dir
        .join("_build")
        .join("default")
        .join("lib")
        .join(name)
        .join("ebin");
    if rebar_ebin.exists() && rebar_ebin != ebin_dir {
        std::fs::create_dir_all(&ebin_dir)
            .map_err(|e| format!("failed to create ebin dir: {}", e))?;
        for entry in std::fs::read_dir(&rebar_ebin)
            .map_err(|e| format!("failed to read rebar ebin: {}", e))?
        {
            let entry = entry.map_err(|e| format!("failed to read entry: {}", e))?;
            let dest = ebin_dir.join(entry.file_name());
            if !dest.exists() {
                std::fs::copy(entry.path(), &dest)
                    .map_err(|e| format!("failed to copy {}: {}", entry.path().display(), e))?;
            }
        }
    }

    // Also copy priv/ directory if it exists (NIF .so files live here)
    let priv_dir = pkg_dir.join("priv");
    if priv_dir.exists() {
        let dest_priv = ebin_dir.parent().unwrap().join("priv");
        if !dest_priv.exists() {
            copy_dir_recursive(&priv_dir, &dest_priv)?;
        }
    }

    if !ebin_dir.exists() {
        return Err(format!(
            "rebar3 compiled '{}' but no ebin directory was produced",
            name
        ));
    }

    Ok(ebin_dir)
}

/// Recursively copy a directory.
fn copy_dir_recursive(src: &Path, dst: &Path) -> Result<(), String> {
    std::fs::create_dir_all(dst).map_err(|e| format!("failed to create dir: {}", e))?;
    for entry in std::fs::read_dir(src)
        .map_err(|e| format!("failed to read dir {}: {}", src.display(), e))?
    {
        let entry = entry.map_err(|e| format!("failed to read entry: {}", e))?;
        let dest = dst.join(entry.file_name());
        if entry.file_type().is_ok_and(|t| t.is_dir()) {
            copy_dir_recursive(&entry.path(), &dest)?;
        } else {
            std::fs::copy(entry.path(), &dest)
                .map_err(|e| format!("failed to copy {}: {}", entry.path().display(), e))?;
        }
    }
    Ok(())
}

/// Collect ebin directories from all installed deps under `project_root/deps/`.
fn collect_dep_ebin_dirs(project_root: &Path) -> Vec<PathBuf> {
    let deps_dir = project_root.join("deps");
    let Ok(entries) = std::fs::read_dir(&deps_dir) else {
        return vec![];
    };
    entries
        .flatten()
        .filter_map(|e| {
            let ebin = e.path().join("ebin");
            ebin.exists().then_some(ebin)
        })
        .collect()
}

/// Compile .erl files in a package's src/ directory with erlc.
/// `project_root` is used to find dependency ebin dirs for `-pa` and `-include_lib`.
/// Returns the ebin directory path.
pub fn compile_erlang(pkg_dir: &Path, name: &str, project_root: &Path) -> Result<PathBuf, String> {
    let src_dir = pkg_dir.join("src");
    let ebin_dir = pkg_dir.join("ebin");

    if !src_dir.exists() {
        return Err(format!("dependency '{}' has no src/ directory", name));
    }

    std::fs::create_dir_all(&ebin_dir).map_err(|e| format!("failed to create ebin dir: {}", e))?;

    let erl_files: Vec<PathBuf> = std::fs::read_dir(&src_dir)
        .map_err(|e| format!("failed to read src dir: {}", e))?
        .filter_map(|e| e.ok())
        .filter(|e| e.path().extension().is_some_and(|ext| ext == "erl"))
        .map(|e| e.path())
        .collect();

    if erl_files.is_empty() {
        return Err(format!("dependency '{}' has no .erl files in src/", name));
    }

    // Collect -pa flags for dependency ebin dirs (needed for -include_lib resolution)
    let dep_ebin_dirs = collect_dep_ebin_dirs(project_root);

    for erl_file in &erl_files {
        let mut cmd = std::process::Command::new("erlc");
        cmd.arg("-o").arg(&ebin_dir);

        // Add -I for the package's own include/ and src/ dirs
        let include_dir = pkg_dir.join("include");
        if include_dir.exists() {
            cmd.arg("-I").arg(&include_dir);
        }
        cmd.arg("-I").arg(&src_dir);

        // Add -pa for each dep ebin dir (resolves -include_lib)
        for ebin in &dep_ebin_dirs {
            cmd.arg("-pa").arg(ebin);
        }

        cmd.arg(erl_file);

        // Let stderr inherit so the user sees erlc output directly
        let status = cmd
            .status()
            .map_err(|e| format!("failed to run erlc: {}", e))?;

        if !status.success() {
            let _ = std::fs::remove_dir_all(&ebin_dir);
            return Err(format!("erlc failed for {}", erl_file.display()));
        }
    }

    // Copy .app.src to ebin/ as .app (if it exists)
    let app_src = src_dir.join(format!("{}.app.src", name));
    if app_src.exists() {
        let app_dst = ebin_dir.join(format!("{}.app", name));
        std::fs::copy(&app_src, &app_dst).map_err(|e| format!("failed to copy .app.src: {}", e))?;
    }

    Ok(ebin_dir)
}

/// Compile Erlang source files in a Hex package to .beam files.
/// Selects the build tool based on what the package contains:
/// - erlang.mk file -> make app
/// - rebar.config -> rebar3 bare compile
/// - otherwise -> raw erlc
///
/// Returns the ebin directory path.
pub fn compile_package(project_root: &Path, name: &str) -> Result<PathBuf, String> {
    let pkg_dir = package_dir(project_root, name);

    if is_compiled(project_root, name) {
        return Ok(pkg_dir.join("ebin"));
    }

    if pkg_dir.join("erlang.mk").exists() {
        compile_with_erlang_mk(&pkg_dir, name, project_root)
    } else if pkg_dir.join("rebar.config").exists() {
        compile_with_rebar3(&pkg_dir, name, project_root)
    } else {
        compile_erlang(&pkg_dir, name, project_root)
    }
}

/// Fetch metadata, download, and extract a Hex package without compiling it.
/// Returns the release metadata (needed to discover transitive deps).
pub fn prepare_package(
    project_root: &Path,
    name: &str,
    version: &str,
) -> Result<HexRelease, String> {
    let pkg_dir = package_dir(project_root, name);
    let release_json_path = pkg_dir.join("release.json");

    // Load cached release.json if available, otherwise fetch from API
    let release = if release_json_path.exists() {
        let contents = std::fs::read_to_string(&release_json_path)
            .map_err(|e| format!("failed to read cached release.json: {}", e))?;
        serde_json::from_str(&contents)
            .map_err(|e| format!("failed to parse cached release.json: {}", e))?
    } else {
        let release = fetch_release(name, version)?;
        std::fs::create_dir_all(&pkg_dir)
            .map_err(|e| format!("failed to create deps dir: {}", e))?;
        let json = serde_json::to_string_pretty(&release)
            .map_err(|e| format!("failed to serialize release metadata: {}", e))?;
        std::fs::write(&release_json_path, json)
            .map_err(|e| format!("failed to write release.json: {}", e))?;
        release
    };

    // Download and extract tarball (skips if already extracted)
    download_and_extract(project_root, name, version)?;

    Ok(release)
}
