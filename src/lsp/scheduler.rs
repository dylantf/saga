use std::collections::HashMap;
use std::path::PathBuf;
use std::sync::Arc;
use std::sync::atomic::Ordering;
use std::time::Instant as StdInstant;

use tower_lsp::Client;
use tower_lsp::lsp_types::notification::Progress;
use tower_lsp::lsp_types::request::WorkDoneProgressCreate;
use tower_lsp::lsp_types::{
    MessageType, ProgressParams, ProgressParamsValue, ProgressToken, Url, WorkDoneProgress,
    WorkDoneProgressBegin, WorkDoneProgressCreateParams, WorkDoneProgressEnd,
};

use super::analysis_pipeline::{analyze_document, duration_ms, project_root_for_uri, trace};
use super::{
    CheckRequest, SEMANTIC_DEBOUNCE_MS, SharedState, apply_parse_result, current_document,
};

const MAX_CONCURRENT_ANALYSES: usize = 2;

/// Reconcile the analysis spinner with whether any job is currently running.
///
/// A single aggregate work-done progress is active whenever the in-flight set
/// is non-empty, so the editor shows one steady spinner across a burst of edits
/// (and across the slow first project load) rather than flickering per file.
fn reconcile_progress(
    active_token: &mut Option<ProgressToken>,
    seq: &mut u64,
    in_flight_empty: bool,
    supported: bool,
    client: &Client,
) {
    if !in_flight_empty && active_token.is_none() && supported {
        *seq += 1;
        let token = ProgressToken::String(format!("saga/analysis/{}", *seq));
        *active_token = Some(token.clone());
        let client = client.clone();
        tokio::spawn(async move {
            // The `$/progress` Begin must not precede a successful create.
            if client
                .send_request::<WorkDoneProgressCreate>(WorkDoneProgressCreateParams {
                    token: token.clone(),
                })
                .await
                .is_err()
            {
                return;
            }
            client
                .send_notification::<Progress>(ProgressParams {
                    token,
                    value: ProgressParamsValue::WorkDone(WorkDoneProgress::Begin(
                        WorkDoneProgressBegin {
                            title: "Saga: analyzing".to_string(),
                            cancellable: Some(false),
                            message: None,
                            percentage: None,
                        },
                    )),
                })
                .await;
        });
    } else if in_flight_empty && active_token.is_some() {
        let token = active_token.take().expect("token present");
        let client = client.clone();
        tokio::spawn(async move {
            client
                .send_notification::<Progress>(ProgressParams {
                    token,
                    value: ProgressParamsValue::WorkDone(WorkDoneProgress::End(
                        WorkDoneProgressEnd { message: None },
                    )),
                })
                .await;
        });
    }
}

/// Short display name for log messages: the file name, or the full URI.
fn display_name(uri: &Url) -> String {
    uri.path_segments()
        .and_then(|mut segments| segments.next_back())
        .filter(|segment| !segment.is_empty())
        .map(str::to_string)
        .unwrap_or_else(|| uri.to_string())
}

pub(super) async fn debounce_loop(
    mut rx: tokio::sync::mpsc::UnboundedReceiver<CheckRequest>,
    tx_for_dependents: tokio::sync::mpsc::UnboundedSender<CheckRequest>,
    client: Client,
    shared: Arc<SharedState>,
) {
    use tokio::time::{Duration, Instant, sleep_until};

    let debounce = Duration::from_millis(SEMANTIC_DEBOUNCE_MS);
    let mut pending: HashMap<Url, (i32, String, Option<PathBuf>, bool, Instant)> = HashMap::new();
    let mut in_flight: std::collections::HashSet<Url> = std::collections::HashSet::new();
    let (done_tx, mut done_rx) = tokio::sync::mpsc::unbounded_channel::<Url>();
    // Aggregate analysis spinner state. `active_token` is Some while a burst of
    // analysis is running; `progress_seq` mints a fresh token per burst.
    let mut active_token: Option<ProgressToken> = None;
    let mut progress_seq: u64 = 0;
    // Each analysis job builds its own checker (a full clone of the project
    // base), so unbounded parallelism multiplies peak memory by the number of
    // open dependents. Two concurrent jobs keeps the editor responsive while
    // bounding the peak.
    let analysis_slots = Arc::new(tokio::sync::Semaphore::new(MAX_CONCURRENT_ANALYSES));

    loop {
        if pending.is_empty() && in_flight.is_empty() {
            match rx.recv().await {
                Some(req) => {
                    queue_check_request(&mut pending, req, debounce);
                }
                None => break,
            }
        }

        let next_deadline = pending
            .iter()
            .filter(|(uri, _)| !in_flight.contains(*uri))
            .map(|(_, (_, _, _, _, deadline))| *deadline)
            .min();

        tokio::select! {
            biased;
            result = rx.recv() => {
                match result {
                    Some(req) => {
                        let uri = req.uri.clone();
                        let version = req.version;
                        queue_check_request(&mut pending, req, debounce);
                        if in_flight.contains(&uri) {
                            trace(format!(
                                "coalesce analysis while in-flight uri={uri} latest_version={version}"
                            ));
                        }
                    }
                    None => break,
                }
            }
            done = done_rx.recv() => {
                let Some(uri) = done else {
                    break;
                };
                in_flight.remove(&uri);
                trace(format!("analysis job complete uri={uri}"));
                reconcile_progress(
                    &mut active_token,
                    &mut progress_seq,
                    in_flight.is_empty(),
                    shared.client_supports_progress.load(Ordering::Relaxed),
                    &client,
                );
                if let Some((_, _, _, _, deadline)) = pending.get_mut(&uri) {
                    *deadline = Instant::now();
                }
            }
            _ = async {
                if let Some(deadline) = next_deadline {
                    sleep_until(deadline).await;
                } else {
                    std::future::pending::<()>().await;
                }
            } => {
                let now = Instant::now();
                let expired: Vec<Url> = pending
                    .iter()
                    .filter(|(uri, (_, _, _, _, deadline))| *deadline <= now && !in_flight.contains(*uri))
                    .map(|(uri, _)| uri.clone())
                    .collect();

                for uri in expired {
                    let Some((version, text, project_root, is_primary, _)) = pending.remove(&uri) else {
                        continue;
                    };
                    let Some(current) = current_document(&shared, &uri) else {
                        continue;
                    };
                    if current.version != version {
                        trace(format!(
                            "skip stale analysis before start uri={uri} request_version={version} current_version={}",
                            current.version
                        ));
                        continue;
                    }
                    in_flight.insert(uri.clone());
                    let client = client.clone();
                    let shared = Arc::clone(&shared);
                    let analysis_shared = Arc::clone(&shared);
                    let tx = tx_for_dependents.clone();
                    let done = done_tx.clone();
                    let analysis_uri = uri.clone();
                    let slots = Arc::clone(&analysis_slots);
                    trace(format!(
                        "analysis job start uri={uri} version={version} primary={is_primary}"
                    ));
                    tokio::spawn(async move {
                        let Ok(_permit) = slots.acquire_owned().await else {
                            let _ = done.send(uri);
                            return;
                        };
                        // The document may have changed while waiting for a
                        // slot; skip and let the re-enqueued request run.
                        if current_document(&shared, &uri)
                            .is_none_or(|current| current.version != version)
                        {
                            trace(format!(
                                "skip stale analysis after slot wait uri={uri} request_version={version}"
                            ));
                            let _ = done.send(uri);
                            return;
                        }
                        let job_start = StdInstant::now();
                        let join_result = tokio::task::spawn_blocking(move || {
                            analyze_document(
                                &analysis_shared,
                                Some(&analysis_uri),
                                version,
                                &text,
                                project_root,
                            )
                        })
                        .await;
                        let result = match join_result {
                            Ok(result) => result,
                            Err(error) => {
                                trace(format!(
                                    "analysis job failed uri={uri} version={version} error={error}"
                                ));
                                let _ = done.send(uri);
                                return;
                            }
                        };
                        trace(format!(
                            "analysis job finish uri={uri} version={} elapsed={}",
                            result.version,
                            duration_ms(job_start.elapsed())
                        ));

                        if let Some(applied) = apply_parse_result(&shared, &uri, result) {
                            trace(format!(
                                "publish diagnostics uri={uri} version={version} count={}",
                                applied.diagnostics.len()
                            ));
                            if applied.first_load {
                                client
                                    .log_message(
                                        MessageType::INFO,
                                        format!(
                                            "{} analyzed in {}",
                                            display_name(&uri),
                                            duration_ms(job_start.elapsed())
                                        ),
                                    )
                                    .await;
                            }
                            client
                                .publish_diagnostics(uri.clone(), applied.diagnostics, Some(version))
                                .await;
                            if is_primary {
                                for dependent_uri in applied.dependents {
                                    if dependent_uri == uri {
                                        continue;
                                    }
                                    let Some(dependent) = current_document(&shared, &dependent_uri) else {
                                        continue;
                                    };
                                    trace(format!(
                                        "enqueue dependent uri={dependent_uri} because={uri} version={}",
                                        dependent.version
                                    ));
                                    let _ = tx.send(CheckRequest {
                                        project_root: project_root_for_uri(&dependent_uri),
                                        uri: dependent_uri,
                                        version: dependent.version,
                                        text: dependent.text,
                                        is_primary: false,
                                    });
                                }
                            }
                        }
                        let _ = done.send(uri);
                    });
                }
                reconcile_progress(
                    &mut active_token,
                    &mut progress_seq,
                    in_flight.is_empty(),
                    shared.client_supports_progress.load(Ordering::Relaxed),
                    &client,
                );
            }
        }
    }
}

fn queue_check_request(
    pending: &mut HashMap<Url, (i32, String, Option<PathBuf>, bool, tokio::time::Instant)>,
    req: CheckRequest,
    debounce: tokio::time::Duration,
) {
    let CheckRequest {
        uri,
        version,
        text,
        project_root,
        is_primary,
    } = req;
    pending
        .entry(uri)
        .and_modify(|entry| {
            entry.0 = version;
            entry.1 = text.clone();
            entry.2 = project_root.clone();
            entry.3 |= is_primary;
            entry.4 = tokio::time::Instant::now() + debounce;
        })
        .or_insert_with(|| {
            (
                version,
                text,
                project_root,
                is_primary,
                tokio::time::Instant::now() + debounce,
            )
        });
}
