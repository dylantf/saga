use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::time::{Duration as StdDuration, Instant as StdInstant};

use saga::{derive, desugar, lexer, parser, project_config, typechecker};
use tower_lsp::lsp_types::*;

use super::analysis::collect_module_interface_updates;
use super::semantic_builder::build_semantic_index;
use super::state::ProjectSemanticIndexUpdate;
use super::text::{LineIndex, span_to_range};
use super::{
    CachedDefinitionSources, ParseJobResult, ParseSnapshot, SemanticSnapshot, SharedState,
    document_version_is_current, extract_module_info,
};

#[derive(Default)]
struct AnalysisTimings {
    lex: StdDuration,
    parse: StdDuration,
    checker: StdDuration,
    derive_imports: StdDuration,
    derive_expand: StdDuration,
    desugar: StdDuration,
    typecheck: StdDuration,
    cache_update: StdDuration,
    definitions: StdDuration,
    total: StdDuration,
}

fn timed<T>(slot: &mut StdDuration, f: impl FnOnce() -> T) -> T {
    let start = StdInstant::now();
    let result = f();
    *slot = start.elapsed();
    result
}

pub(super) fn duration_ms(duration: StdDuration) -> String {
    format!("{:.1}ms", duration.as_secs_f64() * 1000.0)
}

fn trace_elapsed(label: impl AsRef<str>, start: StdInstant) {
    trace(format!(
        "{} elapsed={}",
        label.as_ref(),
        duration_ms(start.elapsed())
    ));
}

pub(super) fn trace(message: impl AsRef<str>) {
    if std::env::var_os("SAGA_LSP_TRACE").is_none() {
        return;
    }

    let line = format!("[saga-lsp] {}", message.as_ref());
    if let Some(path) = std::env::var_os("SAGA_LSP_TRACE_FILE") {
        use std::io::Write;
        if let Ok(mut file) = std::fs::OpenOptions::new()
            .create(true)
            .append(true)
            .open(path)
        {
            let _ = writeln!(file, "{line}");
        }
    } else {
        eprintln!("{line}");
    }
}

pub(super) fn display_project_root(root: Option<&PathBuf>) -> String {
    root.map(|path| path.display().to_string())
        .unwrap_or_else(|| "<loose>".to_string())
}

fn trace_analysis(
    uri: Option<&Url>,
    version: i32,
    project_root: Option<&PathBuf>,
    stage: &str,
    timings: &AnalysisTimings,
    diagnostics: usize,
) {
    trace(format!(
        "analysis {stage} uri={} version={version} root={} diagnostics={diagnostics} total={} lex={} parse={} checker={} derive_imports={} derive_expand={} desugar={} typecheck={} cache_update={} definitions={}",
        uri.map(ToString::to_string)
            .unwrap_or_else(|| "<unknown>".to_string()),
        display_project_root(project_root),
        duration_ms(timings.total),
        duration_ms(timings.lex),
        duration_ms(timings.parse),
        duration_ms(timings.checker),
        duration_ms(timings.derive_imports),
        duration_ms(timings.derive_expand),
        duration_ms(timings.desugar),
        duration_ms(timings.typecheck),
        duration_ms(timings.cache_update),
        duration_ms(timings.definitions),
    ));
}

fn diagnostic_at(
    line_index: &LineIndex,
    source: &str,
    offset: usize,
    message: String,
) -> Diagnostic {
    let start = line_index.offset_to_position(offset, source);
    let end_offset = (offset.saturating_add(1)).min(source.len());
    let end = line_index.offset_to_position(end_offset, source);
    Diagnostic {
        range: Range { start, end },
        severity: Some(DiagnosticSeverity::ERROR),
        message,
        ..Default::default()
    }
}

fn typechecker_diagnostic_at(
    line_index: &LineIndex,
    source: &str,
    diagnostic: &typechecker::Diagnostic,
) -> Diagnostic {
    let span = diagnostic
        .span
        .unwrap_or(saga::token::Span { start: 0, end: 1 });
    let severity = match diagnostic.severity {
        typechecker::Severity::Error => DiagnosticSeverity::ERROR,
        typechecker::Severity::Warning => DiagnosticSeverity::WARNING,
    };

    Diagnostic {
        range: span_to_range(&span, line_index, source),
        severity: Some(severity),
        message: diagnostic.message.clone(),
        ..Default::default()
    }
}

fn find_project_root(start: &Path) -> Option<PathBuf> {
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

pub(super) fn project_root_for_uri(uri: &Url) -> Option<PathBuf> {
    uri.to_file_path()
        .ok()
        .and_then(|path| path.parent().map(Path::to_path_buf))
        .and_then(|dir| find_project_root(&dir))
}

fn checker_for_analysis(
    shared: &SharedState,
    project_root: Option<PathBuf>,
    requested_modules: Option<&std::collections::HashSet<String>>,
) -> std::result::Result<typechecker::Checker, typechecker::Diagnostic> {
    trace(format!(
        "checker prep start root={}",
        display_project_root(project_root.as_ref())
    ));
    let overlay_start = StdInstant::now();
    let source_overlay = open_source_overlay(shared);
    trace_elapsed("checker prep overlay-build", overlay_start);
    trace(format!(
        "checker prep overlay root={} count={}",
        display_project_root(project_root.as_ref()),
        source_overlay.len()
    ));
    let open_modules_start = StdInstant::now();
    let open_modules = open_module_map(shared, project_root.as_deref());
    trace_elapsed("checker prep open-modules-build", open_modules_start);
    trace(format!(
        "checker prep open-modules root={} count={}",
        display_project_root(project_root.as_ref()),
        open_modules.len()
    ));

    let base_lookup_start = StdInstant::now();
    let cached_base = {
        let projects = shared.projects.lock().unwrap_or_else(|e| e.into_inner());
        projects.base_checker(&project_root)
    };
    trace_elapsed("checker prep base-lookup", base_lookup_start);

    if let Some(base) = cached_base {
        trace(format!(
            "checker prep base-cache-hit root={}",
            display_project_root(project_root.as_ref())
        ));
        let prepare_start = StdInstant::now();
        let mut checker = prepare_checker_for_analysis(
            base,
            project_root.clone(),
            source_overlay.clone(),
            open_modules,
        );
        cache_checker_module_names(shared, project_root.clone(), &checker);
        trace_elapsed("checker prep prepare-checker", prepare_start);
        trace(format!(
            "checker prep prepared root={}",
            display_project_root(project_root.as_ref())
        ));
        let seed_start = StdInstant::now();
        let seeded = shared
            .projects
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .seed_module_interfaces(
                &project_root,
                &mut checker,
                &source_overlay,
                requested_modules,
            );
        trace_elapsed("checker prep seed-interfaces", seed_start);
        if seeded > 0 {
            trace(format!(
                "seeded module interfaces root={} count={seeded}",
                display_project_root(project_root.as_ref())
            ));
        }
        trace(format!(
            "checker prep finish root={}",
            display_project_root(project_root.as_ref())
        ));
        return Ok(checker);
    }

    trace(format!(
        "checker prep base-cache-miss root={}",
        display_project_root(project_root.as_ref())
    ));
    let mut built = checker_base_for_project(project_root.clone())?;
    trace(format!(
        "checker prep base-built root={}",
        display_project_root(project_root.as_ref())
    ));
    let warmed_interfaces = collect_module_interface_updates(
        None,
        &Vec::new(),
        &built,
        &built.to_lsp_result(),
        &source_overlay,
        &HashMap::new(),
        false,
    );
    if !warmed_interfaces.is_empty() {
        let applied = shared
            .projects
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .apply_module_interface_updates(project_root.clone(), warmed_interfaces);
        trace(format!(
            "checker prep harvested warmed interfaces root={} count={}",
            display_project_root(project_root.as_ref()),
            applied.updated
        ));
    }
    built.clear_module_semantic_caches();
    let base = {
        let mut projects = shared.projects.lock().unwrap_or_else(|e| e.into_inner());
        projects.store_base_checker(project_root.clone(), built)
    };
    trace(format!(
        "checker prep base-stored root={}",
        display_project_root(project_root.as_ref())
    ));
    let mut checker = prepare_checker_for_analysis(
        base,
        project_root.clone(),
        source_overlay.clone(),
        open_modules,
    );
    cache_checker_module_names(shared, project_root.clone(), &checker);
    trace(format!(
        "checker prep prepared root={}",
        display_project_root(project_root.as_ref())
    ));
    let seeded = shared
        .projects
        .lock()
        .unwrap_or_else(|e| e.into_inner())
        .seed_module_interfaces(
            &project_root,
            &mut checker,
            &source_overlay,
            requested_modules,
        );
    if seeded > 0 {
        trace(format!(
            "seeded module interfaces root={} count={seeded}",
            display_project_root(project_root.as_ref())
        ));
    }
    trace(format!(
        "checker prep finish root={}",
        display_project_root(project_root.as_ref())
    ));
    Ok(checker)
}

fn cache_checker_module_names(
    shared: &SharedState,
    project_root: Option<PathBuf>,
    checker: &typechecker::Checker,
) {
    let Some(module_map) = checker.module_map() else {
        return;
    };
    let module_names = module_map.keys().cloned().collect::<Vec<_>>();
    if module_names.is_empty() {
        return;
    }
    let mut projects = shared.projects.lock().unwrap_or_else(|e| e.into_inner());
    projects.replace_module_names(project_root, module_names);
}

pub(super) fn checker_base_for_project(
    project_root: Option<PathBuf>,
) -> std::result::Result<typechecker::Checker, typechecker::Diagnostic> {
    let mut checker = typechecker::Checker::with_prelude(project_root.clone())?;
    if let Some(root) = &project_root {
        let config = project_config::ProjectConfig::load(root);
        if let Some(deps) = &config.deps
            && let Err(e) = project_config::resolve_deps(&mut checker, root, deps)
        {
            eprintln!("[LSP] Warning: failed to resolve dependencies: {e}");
        }
    }
    Ok(checker)
}

pub(super) fn prepare_checker_for_analysis(
    mut checker: typechecker::Checker,
    project_root: Option<PathBuf>,
    source_overlay: HashMap<PathBuf, String>,
    open_modules: typechecker::ModuleMap,
) -> typechecker::Checker {
    if let Some(root) = project_root
        && let Ok(module_map) = typechecker::scan_project_modules(&root)
    {
        let mut refreshed_map = checker.module_map().cloned().unwrap_or_default();
        refreshed_map.retain(|_, path| !is_local_project_module_path(&root, path));
        for path in open_modules.values() {
            refreshed_map.retain(|_, existing_path| existing_path != path);
        }
        refreshed_map.extend(module_map);
        refreshed_map.extend(open_modules);
        checker.set_module_map(refreshed_map);
    }
    checker.set_source_overlay(source_overlay);
    checker
}

fn is_local_project_module_path(root: &Path, path: &Path) -> bool {
    path.starts_with(root.join("src")) || path.starts_with(root.join("lib"))
}

fn open_source_overlay(shared: &SharedState) -> HashMap<PathBuf, String> {
    let documents = shared.documents.lock().unwrap_or_else(|e| e.into_inner());
    documents
        .iter()
        .filter_map(|(uri, document)| Some((uri.to_file_path().ok()?, document.text.clone())))
        .collect()
}

fn open_module_map(shared: &SharedState, project_root: Option<&Path>) -> typechecker::ModuleMap {
    let documents = shared.documents.lock().unwrap_or_else(|e| e.into_inner());
    documents
        .iter()
        .filter_map(|(uri, document)| {
            if document.dirty {
                return None;
            }
            let path = uri.to_file_path().ok()?;
            if let Some(root) = project_root
                && !path.starts_with(root)
            {
                return None;
            }
            let parse = document.parse.as_ref()?;
            let (module_name, _) = extract_module_info(&parse.program);
            Some((module_name?, path))
        })
        .collect()
}

pub(super) fn analyze_document(
    shared: &SharedState,
    uri: Option<&Url>,
    version: i32,
    text: &str,
    project_root: Option<PathBuf>,
) -> ParseJobResult {
    let total_start = StdInstant::now();
    let mut timings = AnalysisTimings::default();
    let line_index = LineIndex::new(text);

    let tokens = match timed(&mut timings.lex, || lexer::Lexer::new(text).lex()) {
        Ok(tokens) => tokens,
        Err(e) => {
            let diagnostics = vec![diagnostic_at(&line_index, text, e.pos, e.message)];
            timings.total = total_start.elapsed();
            trace_analysis(
                uri,
                version,
                project_root.as_ref(),
                "lex-error",
                &timings,
                diagnostics.len(),
            );
            return ParseJobResult {
                version,
                parse: None,
                semantic: None,
                diagnostics,
                module_interfaces: Vec::new(),
                semantic_index_update: None,
                force_dependents: true,
            };
        }
    };
    trace(format!(
        "analysis checkpoint uri={} version={version} stage=lex-ok",
        uri.map(ToString::to_string)
            .unwrap_or_else(|| "<unknown>".to_string())
    ));

    let mut parser = parser::Parser::new(tokens);
    match timed(&mut timings.parse, || parser.parse_program()) {
        Ok(program) => {
            trace(format!(
                "analysis checkpoint uri={} version={version} stage=parse-ok",
                uri.map(ToString::to_string)
                    .unwrap_or_else(|| "<unknown>".to_string())
            ));
            let source: Arc<str> = Arc::from(text);
            let parse = ParseSnapshot {
                version,
                source: Arc::clone(&source),
                line_index: line_index.clone(),
                program: program.clone(),
            };
            let (_, direct_imports) = extract_module_info(&program);

            let mut checker = match timed(&mut timings.checker, || {
                checker_for_analysis(shared, project_root.clone(), Some(&direct_imports))
            }) {
                Ok(checker) => checker,
                Err(e) => {
                    let diagnostics = vec![typechecker_diagnostic_at(&line_index, text, &e)];
                    timings.total = total_start.elapsed();
                    trace_analysis(
                        uri,
                        version,
                        project_root.as_ref(),
                        "checker-error",
                        &timings,
                        diagnostics.len(),
                    );
                    return ParseJobResult {
                        version,
                        parse: Some(parse),
                        semantic: None,
                        diagnostics,
                        module_interfaces: Vec::new(),
                        semantic_index_update: None,
                        force_dependents: true,
                    };
                }
            };
            trace(format!(
                "analysis checkpoint uri={} version={version} stage=checker-ok",
                uri.map(ToString::to_string)
                    .unwrap_or_else(|| "<unknown>".to_string())
            ));

            let source_overlay = open_source_overlay(shared);
            if let (Some(current_module), _) = extract_module_info(&program) {
                checker.evict_module(&current_module);
            }
            let imported = timed(&mut timings.derive_imports, || {
                checker.collect_imported_decls_cached(&program, &source_overlay)
            });
            trace(format!(
                "analysis checkpoint uri={} version={version} stage=derive-imports-ok",
                uri.map(ToString::to_string)
                    .unwrap_or_else(|| "<unknown>".to_string())
            ));
            let mut semantic_program = program;
            let derive_errors = timed(&mut timings.derive_expand, || {
                derive::expand_derives(&mut semantic_program, &imported)
            });
            trace(format!(
                "analysis checkpoint uri={} version={version} stage=derive-expand-ok",
                uri.map(ToString::to_string)
                    .unwrap_or_else(|| "<unknown>".to_string())
            ));
            timed(&mut timings.desugar, || {
                desugar::desugar_program(&mut semantic_program)
            });
            trace(format!(
                "analysis checkpoint uri={} version={version} stage=desugar-ok",
                uri.map(ToString::to_string)
                    .unwrap_or_else(|| "<unknown>".to_string())
            ));
            if !document_version_is_current(shared, uri, version) {
                timings.total = total_start.elapsed();
                trace_analysis(
                    uri,
                    version,
                    project_root.as_ref(),
                    "stale-before-typecheck",
                    &timings,
                    0,
                );
                return ParseJobResult {
                    version,
                    parse: Some(parse),
                    semantic: None,
                    diagnostics: Vec::new(),
                    module_interfaces: Vec::new(),
                    semantic_index_update: None,
                    force_dependents: false,
                };
            }
            let check = timed(&mut timings.typecheck, || {
                checker.check_program_lsp(&mut semantic_program)
            });
            trace(format!(
                "analysis checkpoint uri={} version={version} stage=typecheck-ok",
                uri.map(ToString::to_string)
                    .unwrap_or_else(|| "<unknown>".to_string())
            ));
            let include_current_interface = !check.has_errors()
                && derive_errors
                    .iter()
                    .all(|diagnostic| !matches!(diagnostic.severity, typechecker::Severity::Error));
            let cached_source_fingerprints = shared
                .projects
                .lock()
                .unwrap_or_else(|e| e.into_inner())
                .cached_module_source_fingerprints(&project_root);
            trace(format!(
                "interface cache snapshot root={} count={}",
                display_project_root(project_root.as_ref()),
                cached_source_fingerprints.len()
            ));
            let module_interfaces = timed(&mut timings.cache_update, || {
                collect_module_interface_updates(
                    uri,
                    &semantic_program,
                    &checker,
                    &check,
                    &source_overlay,
                    &cached_source_fingerprints,
                    include_current_interface,
                )
            });
            if !module_interfaces.is_empty() {
                trace(format!(
                    "prepared module interfaces root={} count={}",
                    display_project_root(project_root.as_ref()),
                    module_interfaces.len()
                ));
            }
            let semantic_index = timed(&mut timings.definitions, || {
                let projects = shared.projects.lock().unwrap_or_else(|e| e.into_inner());
                build_semantic_index(
                    uri,
                    &line_index,
                    text,
                    &semantic_program,
                    &check,
                    &source_overlay,
                    CachedDefinitionSources {
                        projects: &projects,
                        project_root: &project_root,
                        direct_imports: &direct_imports,
                    },
                )
            });

            let mut diagnostics: Vec<Diagnostic> = derive_errors
                .iter()
                .map(|d| typechecker_diagnostic_at(&line_index, text, d))
                .collect();
            diagnostics.extend(
                check
                    .diagnostics
                    .iter()
                    .map(|d| typechecker_diagnostic_at(&line_index, text, d)),
            );

            timings.total = total_start.elapsed();
            trace_analysis(
                uri,
                version,
                project_root.as_ref(),
                "ok",
                &timings,
                diagnostics.len(),
            );

            let semantic_index_update = uri.and_then(|uri| {
                let (module_name, _) = extract_module_info(&semantic_program);
                module_name.map(|module_name| ProjectSemanticIndexUpdate {
                    module_name,
                    uri: uri.clone(),
                    index: semantic_index.clone(),
                })
            });

            ParseJobResult {
                version,
                parse: Some(parse),
                semantic: Some(SemanticSnapshot {
                    version,
                    source,
                    line_index,
                    check,
                    semantic_index,
                }),
                diagnostics,
                module_interfaces,
                semantic_index_update,
                force_dependents: !include_current_interface,
            }
        }
        Err(e) => {
            let diagnostics = vec![diagnostic_at(&line_index, text, e.span.start, e.message)];
            timings.total = total_start.elapsed();
            trace_analysis(
                uri,
                version,
                project_root.as_ref(),
                "parse-error",
                &timings,
                diagnostics.len(),
            );
            ParseJobResult {
                version,
                parse: None,
                semantic: None,
                diagnostics,
                module_interfaces: Vec::new(),
                semantic_index_update: None,
                force_dependents: true,
            }
        }
    }
}

pub(super) fn analyze_syntax_document(
    uri: Option<&Url>,
    version: i32,
    text: &str,
) -> ParseJobResult {
    let total_start = StdInstant::now();
    let mut timings = AnalysisTimings::default();
    let line_index = LineIndex::new(text);

    let tokens = match timed(&mut timings.lex, || lexer::Lexer::new(text).lex()) {
        Ok(tokens) => tokens,
        Err(e) => {
            let diagnostics = vec![diagnostic_at(&line_index, text, e.pos, e.message)];
            timings.total = total_start.elapsed();
            trace_analysis(
                uri,
                version,
                None,
                "syntax-lex-error",
                &timings,
                diagnostics.len(),
            );
            return ParseJobResult {
                version,
                parse: None,
                semantic: None,
                diagnostics,
                module_interfaces: Vec::new(),
                semantic_index_update: None,
                force_dependents: false,
            };
        }
    };

    let mut parser = parser::Parser::new(tokens);
    match timed(&mut timings.parse, || parser.parse_program()) {
        Ok(program) => {
            let source: Arc<str> = Arc::from(text);
            let parse = ParseSnapshot {
                version,
                source,
                line_index,
                program,
            };
            timings.total = total_start.elapsed();
            trace_analysis(uri, version, None, "syntax-ok", &timings, 0);
            ParseJobResult {
                version,
                parse: Some(parse),
                semantic: None,
                diagnostics: Vec::new(),
                module_interfaces: Vec::new(),
                semantic_index_update: None,
                force_dependents: false,
            }
        }
        Err(e) => {
            let diagnostics = vec![diagnostic_at(&line_index, text, e.span.start, e.message)];
            timings.total = total_start.elapsed();
            trace_analysis(
                uri,
                version,
                None,
                "syntax-parse-error",
                &timings,
                diagnostics.len(),
            );
            ParseJobResult {
                version,
                parse: None,
                semantic: None,
                diagnostics,
                module_interfaces: Vec::new(),
                semantic_index_update: None,
                force_dependents: false,
            }
        }
    }
}
