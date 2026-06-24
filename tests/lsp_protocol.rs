use std::io::{BufRead, BufReader, Write};
use std::process::{Child, ChildStdin, Command, Stdio};
use std::sync::mpsc::{self, Receiver};
use std::thread;
use std::time::{Duration, Instant};

use serde_json::{Value, json};

struct LspHarness {
    child: Child,
    stdin: ChildStdin,
    rx: Receiver<Value>,
    next_id: i64,
}

impl LspHarness {
    fn start() -> Self {
        let mut child = Command::new(env!("CARGO_BIN_EXE_saga-lsp"))
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::null())
            .spawn()
            .expect("spawn saga-lsp");

        let stdin = child.stdin.take().expect("take child stdin");
        let stdout = child.stdout.take().expect("take child stdout");
        let (tx, rx) = mpsc::channel();

        thread::spawn(move || {
            let mut reader = BufReader::new(stdout);
            while let Ok(message) = read_lsp_message(&mut reader) {
                if tx.send(message).is_err() {
                    break;
                }
            }
        });

        Self {
            child,
            stdin,
            rx,
            next_id: 1,
        }
    }

    fn initialize(&mut self) {
        let id = self.send_request(
            "initialize",
            json!({
                "processId": null,
                "rootUri": null,
                "capabilities": {}
            }),
        );
        self.recv_until(Duration::from_secs(5), |message| {
            message.get("id").and_then(Value::as_i64) == Some(id)
        })
        .expect("initialize response");
        self.send_notification("initialized", json!({}));
    }

    fn send_request(&mut self, method: &str, params: Value) -> i64 {
        let id = self.next_id;
        self.next_id += 1;
        self.send(json!({
            "jsonrpc": "2.0",
            "id": id,
            "method": method,
            "params": params,
        }));
        id
    }

    fn send_notification(&mut self, method: &str, params: Value) {
        self.send(json!({
            "jsonrpc": "2.0",
            "method": method,
            "params": params,
        }));
    }

    fn send(&mut self, message: Value) {
        let body = serde_json::to_vec(&message).expect("serialize lsp message");
        write!(self.stdin, "Content-Length: {}\r\n\r\n", body.len()).expect("write lsp header");
        self.stdin.write_all(&body).expect("write lsp body");
        self.stdin.flush().expect("flush lsp message");
    }

    fn recv_until(
        &self,
        timeout: Duration,
        mut predicate: impl FnMut(&Value) -> bool,
    ) -> Option<Value> {
        let deadline = Instant::now() + timeout;
        loop {
            let now = Instant::now();
            if now >= deadline {
                return None;
            }
            let remaining = deadline.saturating_duration_since(now);
            let message = self.rx.recv_timeout(remaining).ok()?;
            if predicate(&message) {
                return Some(message);
            }
        }
    }
}

impl Drop for LspHarness {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}

fn read_lsp_message(reader: &mut impl BufRead) -> std::io::Result<Value> {
    let mut content_length = None;
    loop {
        let mut line = String::new();
        let bytes = reader.read_line(&mut line)?;
        if bytes == 0 {
            return Err(std::io::ErrorKind::UnexpectedEof.into());
        }
        let trimmed = line.trim_end();
        if trimmed.is_empty() {
            break;
        }
        if let Some(value) = trimmed.strip_prefix("Content-Length:") {
            content_length = Some(value.trim().parse::<usize>().map_err(|e| {
                std::io::Error::new(std::io::ErrorKind::InvalidData, e.to_string())
            })?);
        }
    }

    let len = content_length.ok_or_else(|| {
        std::io::Error::new(std::io::ErrorKind::InvalidData, "missing Content-Length")
    })?;
    let mut body = vec![0; len];
    reader.read_exact(&mut body)?;
    serde_json::from_slice(&body)
        .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e.to_string()))
}

fn publish_diagnostics(message: &Value) -> Option<&Value> {
    (message.get("method").and_then(Value::as_str) == Some("textDocument/publishDiagnostics"))
        .then(|| message.get("params"))?
}

fn saga_uri(name: &str) -> String {
    format!("file:///tmp/{name}.saga")
}

#[test]
fn publishes_syntax_diagnostics_with_document_version() {
    let mut lsp = LspHarness::start();
    lsp.initialize();

    lsp.send_notification(
        "textDocument/didOpen",
        json!({
            "textDocument": {
                "uri": saga_uri("broken"),
                "languageId": "saga",
                "version": 1,
                "text": "module Main\n\nfun main : Unit -> Unit\nmain () = "
            }
        }),
    );

    let params = lsp
        .recv_until(Duration::from_secs(5), |message| {
            publish_diagnostics(message).is_some()
        })
        .and_then(|message| publish_diagnostics(&message).cloned())
        .expect("publish diagnostics notification");

    assert_eq!(params["version"], 1);
    assert!(
        params["diagnostics"]
            .as_array()
            .is_some_and(|d| !d.is_empty()),
        "expected at least one syntax diagnostic, got {params:?}"
    );
}

#[test]
fn coalesces_changes_and_publishes_only_current_version() {
    let mut lsp = LspHarness::start();
    lsp.initialize();
    let uri = saga_uri("coalesce");

    lsp.send_notification(
        "textDocument/didOpen",
        json!({
            "textDocument": {
                "uri": uri,
                "languageId": "saga",
                "version": 1,
                "text": "module Main\n\nfun main : Unit -> Unit\nmain () = "
            }
        }),
    );
    lsp.send_notification(
        "textDocument/didChange",
        json!({
            "textDocument": {
                "uri": saga_uri("coalesce"),
                "version": 2
            },
            "contentChanges": [{
                "text": "module Main\n\nfun main : Unit -> Unit\nmain () = ()\n"
            }]
        }),
    );

    let params = lsp
        .recv_until(Duration::from_secs(5), |message| {
            publish_diagnostics(message).is_some()
        })
        .and_then(|message| publish_diagnostics(&message).cloned())
        .expect("publish diagnostics notification");

    assert_eq!(params["version"], 2);
    assert_eq!(
        params["diagnostics"].as_array().map(Vec::len),
        Some(0),
        "expected valid version 2 to clear diagnostics, got {params:?}"
    );
}

#[test]
fn document_symbols_come_from_latest_parse_snapshot() {
    let mut lsp = LspHarness::start();
    lsp.initialize();
    let uri = saga_uri("symbols");

    lsp.send_notification(
        "textDocument/didOpen",
        json!({
            "textDocument": {
                "uri": uri,
                "languageId": "saga",
                "version": 1,
                "text": "module Main\n\nfun main : Unit -> Unit\nmain () = ()\n"
            }
        }),
    );

    let params = lsp
        .recv_until(Duration::from_secs(5), |message| {
            publish_diagnostics(message).is_some()
        })
        .and_then(|message| publish_diagnostics(&message).cloned())
        .expect("publish diagnostics notification");
    assert_eq!(
        params["diagnostics"].as_array().map(Vec::len),
        Some(0),
        "fixture must parse before documentSymbol request, got {params:?}"
    );

    let id = lsp.send_request(
        "textDocument/documentSymbol",
        json!({
            "textDocument": {
                "uri": saga_uri("symbols")
            }
        }),
    );
    let response = lsp
        .recv_until(Duration::from_secs(5), |message| {
            message.get("id").and_then(Value::as_i64) == Some(id)
        })
        .expect("documentSymbol response");

    let names: Vec<_> = response["result"]
        .as_array()
        .expect("flat document symbols")
        .iter()
        .filter_map(|symbol| symbol["name"].as_str())
        .collect();

    assert!(names.contains(&"Main"), "missing module symbol: {names:?}");
    assert!(
        names.contains(&"main"),
        "missing function symbol: {names:?}"
    );
}

#[test]
fn completion_uses_current_text_and_preserved_parse_snapshot() {
    let mut lsp = LspHarness::start();
    lsp.initialize();
    let uri = saga_uri("completion");

    lsp.send_notification(
        "textDocument/didOpen",
        json!({
            "textDocument": {
                "uri": uri,
                "languageId": "saga",
                "version": 1,
                "text": "module Main\n\nfun main : Unit -> Unit\nmain () = ()\n"
            }
        }),
    );
    lsp.recv_until(Duration::from_secs(5), |message| {
        publish_diagnostics(message).is_some()
    })
    .expect("initial diagnostics");

    lsp.send_notification(
        "textDocument/didChange",
        json!({
            "textDocument": {
                "uri": saga_uri("completion"),
                "version": 2
            },
            "contentChanges": [{
                "text": "module Main\n\nm"
            }]
        }),
    );
    lsp.recv_until(Duration::from_secs(5), |message| {
        publish_diagnostics(message).and_then(|params| params["version"].as_i64()) == Some(2)
    })
    .expect("broken document diagnostics");

    let id = lsp.send_request(
        "textDocument/completion",
        json!({
            "textDocument": {
                "uri": saga_uri("completion")
            },
            "position": {
                "line": 2,
                "character": 1
            }
        }),
    );
    let response = lsp
        .recv_until(Duration::from_secs(5), |message| {
            message.get("id").and_then(Value::as_i64) == Some(id)
        })
        .expect("completion response");

    let labels: Vec<_> = response["result"]
        .as_array()
        .expect("completion item array")
        .iter()
        .filter_map(|item| item["label"].as_str())
        .collect();

    assert!(
        labels.contains(&"main"),
        "missing preserved parse completion: {labels:?}"
    );
    assert!(
        labels.contains(&"module"),
        "missing keyword completion: {labels:?}"
    );
}

#[test]
fn hover_returns_type_from_semantic_snapshot() {
    let mut lsp = LspHarness::start();
    lsp.initialize();
    let uri = saga_uri("hover");
    let source = "\
module Main

fun id : Unit -> Unit
id x = x

fun main : Unit -> Unit
main () = id ()
";

    lsp.send_notification(
        "textDocument/didOpen",
        json!({
            "textDocument": {
                "uri": uri,
                "languageId": "saga",
                "version": 1,
                "text": source
            }
        }),
    );
    let params = lsp
        .recv_until(Duration::from_secs(5), |message| {
            publish_diagnostics(message).is_some()
        })
        .and_then(|message| publish_diagnostics(&message).cloned())
        .expect("publish diagnostics notification");
    assert_eq!(
        params["diagnostics"].as_array().map(Vec::len),
        Some(0),
        "fixture must typecheck before hover request, got {params:?}"
    );

    let id = lsp.send_request(
        "textDocument/hover",
        json!({
            "textDocument": {
                "uri": saga_uri("hover")
            },
            "position": {
                "line": 6,
                "character": 10
            }
        }),
    );
    let response = lsp
        .recv_until(Duration::from_secs(5), |message| {
            message.get("id").and_then(Value::as_i64) == Some(id)
        })
        .expect("hover response");
    let value = response["result"]["contents"]["value"]
        .as_str()
        .expect("hover markdown value");

    assert!(value.contains("id: Unit -> Unit"), "{value}");
}
