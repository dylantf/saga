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
pub fn is_compiled(project_root: &Path, name: &str) -> bool {
    package_ebin_dir(project_root, name).exists()
}

/// Global cache directory for Hex tarball downloads.
fn hex_tarball_cache_dir() -> PathBuf {
    let home = std::env::var("HOME").unwrap_or_else(|_| ".".to_string());
    PathBuf::from(home).join(".dylang").join("cache").join("hex")
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
        .user_agent("dylang")
        .build()
        .expect("failed to create HTTP client")
}

/// Fetch release metadata from the Hex API.
pub fn fetch_release(name: &str, version: &str) -> Result<HexRelease, String> {
    let url = format!(
        "https://hex.pm/api/packages/{}/releases/{}",
        name, version
    );
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

    resp.json::<HexRelease>()
        .map_err(|e| format!("failed to parse release metadata for {}-{}: {}", name, version, e))
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
                name, version, resp.status()
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

    std::fs::create_dir_all(&pkg_dir)
        .map_err(|e| format!("failed to create deps dir: {}", e))?;

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

/// Whether a package directory needs rebar3 to compile (has NIFs, hooks, etc.).
pub fn needs_rebar3(pkg_dir: &Path) -> bool {
    // Has c_src/ or native/ directory (NIF source)
    if pkg_dir.join("c_src").exists() || pkg_dir.join("native").exists() {
        return true;
    }

    // Has rebar.config with pre_hooks or port_specs
    let rebar_config = pkg_dir.join("rebar.config");
    if rebar_config.exists()
        && let Ok(contents) = std::fs::read_to_string(&rebar_config)
        && (contents.contains("pre_hooks")
            || contents.contains("port_specs")
            || contents.contains("provider_hooks"))
    {
        return true;
    }

    false
}

/// Compile a package using rebar3 bare compile.
/// `pkg_dir` is the directory containing the source and rebar.config.
/// `name` is used for error messages and to find rebar3's output dir.
/// Returns the ebin directory path.
pub fn compile_with_rebar3(pkg_dir: &Path, name: &str) -> Result<PathBuf, String> {
    let ebin_dir = pkg_dir.join("ebin");

    // rebar3 bare compile outputs to <output_dir>/ebin/.
    // Point it at the package dir so ebin/ lands where we expect.
    let output = std::process::Command::new("rebar3")
        .args(["bare", "compile", "--paths", ebin_dir.to_str().unwrap_or(".")])
        .current_dir(pkg_dir)
        .env("REBAR_BARE_COMPILER_OUTPUT_DIR", pkg_dir)
        .env("REBAR_PROFILE", "prod")
        .stderr(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .output()
        .map_err(|e| {
            if e.kind() == std::io::ErrorKind::NotFound {
                format!(
                    "dependency '{}' requires rebar3 for compilation (has native code), \
                     but rebar3 is not on PATH. Install rebar3: https://rebar3.org",
                    name
                )
            } else {
                format!("failed to run rebar3: {}", e)
            }
        })?;

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        let stdout = String::from_utf8_lossy(&output.stdout);
        let _ = std::fs::remove_dir_all(&ebin_dir);
        return Err(format!(
            "rebar3 bare compile failed for '{}':\n{}\n{}",
            name,
            stdout.trim(),
            stderr.trim()
        ));
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
    for entry in
        std::fs::read_dir(src).map_err(|e| format!("failed to read dir {}: {}", src.display(), e))?
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

/// Compile .erl files in a package's src/ directory with erlc.
/// Returns the ebin directory path.
pub fn compile_erlang(pkg_dir: &Path, name: &str) -> Result<PathBuf, String> {
    let src_dir = pkg_dir.join("src");
    let ebin_dir = pkg_dir.join("ebin");

    if ebin_dir.exists() {
        return Ok(ebin_dir);
    }

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

    for erl_file in &erl_files {
        let output = std::process::Command::new("erlc")
            .arg("-o")
            .arg(&ebin_dir)
            .arg(erl_file)
            .stderr(std::process::Stdio::piped())
            .output()
            .map_err(|e| format!("failed to run erlc: {}", e))?;

        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr);
            let _ = std::fs::remove_dir_all(&ebin_dir);
            return Err(format!(
                "erlc failed for {}: {}",
                erl_file.display(),
                stderr.trim()
            ));
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
/// Uses raw erlc for simple packages, rebar3 for packages with NIFs/hooks.
/// Returns the ebin directory path.
pub fn compile_package(project_root: &Path, name: &str) -> Result<PathBuf, String> {
    let pkg_dir = package_dir(project_root, name);

    if pkg_dir.join("ebin").exists() {
        return Ok(pkg_dir.join("ebin"));
    }

    if needs_rebar3(&pkg_dir) {
        compile_with_rebar3(&pkg_dir, name)
    } else {
        compile_erlang(&pkg_dir, name)
    }
}

/// Full install pipeline for a single Hex package: fetch metadata, download, extract, compile.
/// Returns (ebin_dir, release_info).
pub fn install_package(
    project_root: &Path,
    name: &str,
    version: &str,
) -> Result<(PathBuf, HexRelease), String> {
    let pkg_dir = package_dir(project_root, name);

    // Check if already compiled
    if is_compiled(project_root, name) {
        // Load cached release.json for dep info
        let release_json_path = pkg_dir.join("release.json");
        let release = if release_json_path.exists() {
            let contents = std::fs::read_to_string(&release_json_path)
                .map_err(|e| format!("failed to read cached release.json: {}", e))?;
            serde_json::from_str(&contents)
                .map_err(|e| format!("failed to parse cached release.json: {}", e))?
        } else {
            fetch_release(name, version)?
        };
        return Ok((package_ebin_dir(project_root, name), release));
    }

    // Fetch release metadata
    let release = fetch_release(name, version)?;

    // Cache release.json
    std::fs::create_dir_all(&pkg_dir)
        .map_err(|e| format!("failed to create deps dir: {}", e))?;
    let release_json = serde_json::to_string_pretty(&release)
        .map_err(|e| format!("failed to serialize release metadata: {}", e))?;
    std::fs::write(pkg_dir.join("release.json"), release_json)
        .map_err(|e| format!("failed to write release.json: {}", e))?;

    // Download and extract tarball
    download_and_extract(project_root, name, version)?;

    // Compile
    let ebin_dir = compile_package(project_root, name)?;

    Ok((ebin_dir, release))
}
