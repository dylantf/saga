use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::path::PathBuf;

/// Global cache directory for Hex packages.
fn hex_cache_dir() -> PathBuf {
    let home = std::env::var("HOME").unwrap_or_else(|_| ".".to_string());
    PathBuf::from(home)
        .join(".dylang")
        .join("cache")
        .join("hex")
}

/// Cache directory for a specific package version.
pub fn package_cache_dir(name: &str, version: &str) -> PathBuf {
    hex_cache_dir().join(format!("{}-{}", name, version))
}

/// Path to the ebin directory for a cached Hex package.
pub fn package_ebin_dir(name: &str, version: &str) -> PathBuf {
    package_cache_dir(name, version).join("ebin")
}

/// Whether a Hex package is already cached and compiled.
pub fn is_cached(name: &str, version: &str) -> bool {
    package_ebin_dir(name, version).exists()
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

/// Download a Hex tarball and extract its contents to the cache.
/// Returns the cache directory path.
pub fn download_and_extract(name: &str, version: &str) -> Result<PathBuf, String> {
    let cache_dir = package_cache_dir(name, version);

    // Already extracted?
    if cache_dir.join("src").exists() {
        return Ok(cache_dir);
    }

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

    let tarball_bytes = resp
        .bytes()
        .map_err(|e| format!("failed to read tarball bytes: {}", e))?;

    std::fs::create_dir_all(&cache_dir)
        .map_err(|e| format!("failed to create cache dir: {}", e))?;

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
        .unpack(&cache_dir)
        .map_err(|e| format!("failed to extract contents: {}", e))?;

    Ok(cache_dir)
}

// --- Compilation ---

/// Compile Erlang source files in a Hex package to .beam files.
/// Returns the ebin directory path.
pub fn compile_package(name: &str, version: &str) -> Result<PathBuf, String> {
    let cache_dir = package_cache_dir(name, version);
    let src_dir = cache_dir.join("src");
    let ebin_dir = cache_dir.join("ebin");

    if ebin_dir.exists() {
        return Ok(ebin_dir);
    }

    if !src_dir.exists() {
        return Err(format!(
            "Hex package {}-{} has no src/ directory",
            name, version
        ));
    }

    std::fs::create_dir_all(&ebin_dir).map_err(|e| format!("failed to create ebin dir: {}", e))?;

    // Find all .erl files in src/
    let erl_files: Vec<PathBuf> = std::fs::read_dir(&src_dir)
        .map_err(|e| format!("failed to read src dir: {}", e))?
        .filter_map(|e| e.ok())
        .filter(|e| e.path().extension().is_some_and(|ext| ext == "erl"))
        .map(|e| e.path())
        .collect();

    if erl_files.is_empty() {
        return Err(format!(
            "Hex package {}-{} has no .erl files in src/",
            name, version
        ));
    }

    // Compile each .erl file with erlc
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
            // Clean up partial ebin on failure
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

/// Full install pipeline for a single Hex package: fetch metadata, download, extract, compile.
/// Returns (ebin_dir, release_info).
pub fn install_package(name: &str, version: &str) -> Result<(PathBuf, HexRelease), String> {
    // Check if already fully cached
    if is_cached(name, version) {
        // Load cached release.json for dep info
        let cache_dir = package_cache_dir(name, version);
        let release_json_path = cache_dir.join("release.json");
        let release = if release_json_path.exists() {
            let contents = std::fs::read_to_string(&release_json_path)
                .map_err(|e| format!("failed to read cached release.json: {}", e))?;
            serde_json::from_str(&contents)
                .map_err(|e| format!("failed to parse cached release.json: {}", e))?
        } else {
            fetch_release(name, version)?
        };
        return Ok((package_ebin_dir(name, version), release));
    }

    // Fetch release metadata
    let release = fetch_release(name, version)?;

    // Cache release.json
    let cache_dir = package_cache_dir(name, version);
    std::fs::create_dir_all(&cache_dir)
        .map_err(|e| format!("failed to create cache dir: {}", e))?;
    let release_json = serde_json::to_string_pretty(&release)
        .map_err(|e| format!("failed to serialize release metadata: {}", e))?;
    std::fs::write(cache_dir.join("release.json"), release_json)
        .map_err(|e| format!("failed to write release.json: {}", e))?;

    // Download and extract tarball
    download_and_extract(name, version)?;

    // Compile
    let ebin_dir = compile_package(name, version)?;

    Ok((ebin_dir, release))
}
