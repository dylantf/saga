use std::io::{BufRead, BufReader, Write};
use std::path::{Path, PathBuf};
use std::process::{Child, ChildStdin, Command, Stdio};
use std::sync::mpsc::{self, Receiver};
use std::thread;
use std::time::{Duration, Instant};

use serde_json::{Value, json};
use tower_lsp::lsp_types::Url;

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

fn diagnostics_for_uri<'a>(message: &'a Value, uri: &str) -> Option<&'a Value> {
    let params = publish_diagnostics(message)?;
    (params["uri"].as_str() == Some(uri)).then_some(params)
}

fn wait_for_diagnostics(lsp: &LspHarness, uri: &str, version: i64, ordinal: usize) -> Value {
    let mut seen = 0;
    lsp.recv_until(Duration::from_secs(5), |message| {
        let Some(params) = diagnostics_for_uri(message, uri) else {
            return false;
        };
        if params["version"].as_i64() != Some(version) {
            return false;
        }
        seen += 1;
        seen >= ordinal
    })
    .and_then(|message| publish_diagnostics(&message).cloned())
    .expect("publish diagnostics notification")
}

fn saga_uri(name: &str) -> String {
    format!("file:///tmp/{name}.saga")
}

fn file_uri(path: &Path) -> String {
    Url::from_file_path(path).expect("file URL").to_string()
}

fn temp_project(name: &str) -> PathBuf {
    let unique = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .expect("clock before epoch")
        .as_nanos();
    let root =
        std::env::temp_dir().join(format!("saga-lsp-{name}-{}-{unique}", std::process::id()));
    std::fs::create_dir_all(root.join("src")).expect("create temp project src");
    std::fs::write(root.join("project.toml"), "").expect("write project.toml");
    root
}

#[test]
fn publishes_syntax_diagnostics_with_document_version() {
    let mut lsp = LspHarness::start();
    lsp.initialize();
    let uri = saga_uri("broken");

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

    let params = wait_for_diagnostics(&lsp, &uri, 1, 1);

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

    let params = wait_for_diagnostics(&lsp, &uri, 2, 1);

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

    let params = wait_for_diagnostics(&lsp, &uri, 1, 1);
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
    let params = wait_for_diagnostics(&lsp, &uri, 1, 2);
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

#[test]
fn goto_definition_uses_local_semantic_references() {
    let mut lsp = LspHarness::start();
    lsp.initialize();
    let uri = saga_uri("definition");
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
    let params = wait_for_diagnostics(&lsp, &uri, 1, 2);
    assert_eq!(
        params["diagnostics"].as_array().map(Vec::len),
        Some(0),
        "fixture must typecheck before definition request, got {params:?}"
    );

    let id = lsp.send_request(
        "textDocument/definition",
        json!({
            "textDocument": {
                "uri": saga_uri("definition")
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
        .expect("definition response");

    let line = response["result"]["range"]["start"]["line"]
        .as_u64()
        .expect("definition start line");
    assert!(
        line == 2 || line == 3,
        "unexpected definition response: {response:?}"
    );
}

#[test]
fn find_references_uses_semantic_identity() {
    let mut lsp = LspHarness::start();
    lsp.initialize();
    let uri = saga_uri("references");
    let source = "\
module Main

fun id : Unit -> Unit
id x = x

fun main : Unit -> Unit
main () = id (id ())
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
    let params = wait_for_diagnostics(&lsp, &uri, 1, 2);
    assert_eq!(
        params["diagnostics"].as_array().map(Vec::len),
        Some(0),
        "fixture must typecheck before references request, got {params:?}"
    );

    let id = lsp.send_request(
        "textDocument/references",
        json!({
            "textDocument": {
                "uri": saga_uri("references")
            },
            "position": {
                "line": 6,
                "character": 11
            },
            "context": {
                "includeDeclaration": true
            }
        }),
    );
    let response = lsp
        .recv_until(Duration::from_secs(5), |message| {
            message.get("id").and_then(Value::as_i64) == Some(id)
        })
        .expect("references response");
    let references = response["result"]
        .as_array()
        .expect("references result array");

    assert!(
        references.len() >= 3,
        "expected declaration and both call sites: {response:?}"
    );
    assert!(
        references.iter().any(|location| {
            location["range"]["start"]["line"].as_u64() == Some(2)
                || location["range"]["start"]["line"].as_u64() == Some(3)
        }),
        "expected declaration location: {response:?}"
    );
    assert!(
        references
            .iter()
            .filter(|location| location["range"]["start"]["line"].as_u64() == Some(6))
            .count()
            >= 2,
        "expected both call sites: {response:?}"
    );

    let id = lsp.send_request(
        "textDocument/references",
        json!({
            "textDocument": {
                "uri": saga_uri("references")
            },
            "position": {
                "line": 6,
                "character": 11
            },
            "context": {
                "includeDeclaration": false
            }
        }),
    );
    let response = lsp
        .recv_until(Duration::from_secs(5), |message| {
            message.get("id").and_then(Value::as_i64) == Some(id)
        })
        .expect("references response");
    let references = response["result"]
        .as_array()
        .expect("references result array");

    assert!(
        references
            .iter()
            .filter(|location| location["range"]["start"]["line"].as_u64() == Some(6))
            .count()
            >= 2,
        "expected both call sites without requiring declarations: {response:?}"
    );
    assert!(
        references.iter().all(|location| {
            location["range"]["start"]["line"].as_u64() != Some(2)
                && location["range"]["start"]["line"].as_u64() != Some(3)
        }),
        "declarations should be omitted when includeDeclaration is false: {response:?}"
    );
}

#[test]
fn hover_uses_project_imports() {
    let root = temp_project("imports");
    let helper_path = root.join("src/Helper.saga");
    let main_path = root.join("src/Main.saga");

    std::fs::write(
        &helper_path,
        "\
module Helper

pub fun forty_two : Unit -> Int
forty_two () = 42
",
    )
    .expect("write helper module");

    let main_source = "\
module Main

import Helper (forty_two)

fun main : Unit -> Int
main () = forty_two ()
";
    std::fs::write(&main_path, main_source).expect("write main module");

    let result = {
        let mut lsp = LspHarness::start();
        lsp.initialize();
        let uri = file_uri(&main_path);

        lsp.send_notification(
            "textDocument/didOpen",
            json!({
                "textDocument": {
                    "uri": uri,
                    "languageId": "saga",
                    "version": 1,
                    "text": main_source
                }
            }),
        );
        let params = wait_for_diagnostics(&lsp, &uri, 1, 2);
        assert_eq!(
            params["diagnostics"].as_array().map(Vec::len),
            Some(0),
            "fixture must typecheck before hover request, got {params:?}"
        );

        let id = lsp.send_request(
            "textDocument/hover",
            json!({
                "textDocument": {
                    "uri": file_uri(&main_path)
                },
                "position": {
                    "line": 5,
                    "character": 11
                }
            }),
        );
        lsp.recv_until(Duration::from_secs(5), |message| {
            message.get("id").and_then(Value::as_i64) == Some(id)
        })
        .expect("hover response")
    };

    let _ = std::fs::remove_dir_all(&root);

    let value = result["result"]["contents"]["value"]
        .as_str()
        .expect("hover markdown value");
    assert!(value.contains("forty_two: Unit -> Int"), "{value}");
}

#[test]
fn goto_definition_uses_cached_cross_module_locations() {
    let root = temp_project("cross-module-definition");
    let helper_path = root.join("src/Helper.saga");
    let main_path = root.join("src/Main.saga");

    std::fs::write(
        &helper_path,
        "\
module Helper

pub fun forty_two : Unit -> Int
forty_two () = 42
",
    )
    .expect("write helper module");

    let main_source = "\
module Main

import Helper (forty_two)

fun main : Unit -> Int
main () = forty_two ()
";
    std::fs::write(&main_path, main_source).expect("write main module");

    let result = {
        let mut lsp = LspHarness::start();
        lsp.initialize();
        let uri = file_uri(&main_path);

        lsp.send_notification(
            "textDocument/didOpen",
            json!({
                "textDocument": {
                    "uri": uri,
                    "languageId": "saga",
                    "version": 1,
                    "text": main_source
                }
            }),
        );
        let params = wait_for_diagnostics(&lsp, &uri, 1, 2);
        assert_eq!(
            params["diagnostics"].as_array().map(Vec::len),
            Some(0),
            "fixture must typecheck before definition request, got {params:?}"
        );

        let id = lsp.send_request(
            "textDocument/definition",
            json!({
                "textDocument": {
                    "uri": file_uri(&main_path)
                },
                "position": {
                    "line": 5,
                    "character": 11
                }
            }),
        );
        lsp.recv_until(Duration::from_secs(5), |message| {
            message.get("id").and_then(Value::as_i64) == Some(id)
        })
        .expect("definition response")
    };

    let _ = std::fs::remove_dir_all(&root);

    assert_eq!(
        result["result"]["uri"].as_str(),
        Some(file_uri(&helper_path).as_str())
    );
    let line = result["result"]["range"]["start"]["line"]
        .as_u64()
        .expect("definition start line");
    assert!(
        line == 2 || line == 3,
        "unexpected definition response: {result:?}"
    );
}

#[test]
fn find_references_includes_imported_definition_location() {
    let root = temp_project("cross-module-references");
    let helper_path = root.join("src/Helper.saga");
    let main_path = root.join("src/Main.saga");

    std::fs::write(
        &helper_path,
        "\
module Helper

pub fun forty_two : Unit -> Int
forty_two () = 42
",
    )
    .expect("write helper module");

    let main_source = "\
module Main

import Helper (forty_two)

fun main : Unit -> Int
main () = forty_two ()
";
    std::fs::write(&main_path, main_source).expect("write main module");

    let result = {
        let mut lsp = LspHarness::start();
        lsp.initialize();
        let uri = file_uri(&main_path);

        lsp.send_notification(
            "textDocument/didOpen",
            json!({
                "textDocument": {
                    "uri": uri,
                    "languageId": "saga",
                    "version": 1,
                    "text": main_source
                }
            }),
        );
        let params = wait_for_diagnostics(&lsp, &uri, 1, 2);
        assert_eq!(
            params["diagnostics"].as_array().map(Vec::len),
            Some(0),
            "fixture must typecheck before references request, got {params:?}"
        );

        let id = lsp.send_request(
            "textDocument/references",
            json!({
                "textDocument": {
                    "uri": file_uri(&main_path)
                },
                "position": {
                    "line": 5,
                    "character": 11
                },
                "context": {
                    "includeDeclaration": true
                }
            }),
        );
        lsp.recv_until(Duration::from_secs(5), |message| {
            message.get("id").and_then(Value::as_i64) == Some(id)
        })
        .expect("references response")
    };

    let _ = std::fs::remove_dir_all(&root);

    let references = result["result"]
        .as_array()
        .expect("references result array");
    assert!(
        references.iter().any(|location| {
            location["uri"].as_str() == Some(file_uri(&helper_path).as_str())
                && (location["range"]["start"]["line"].as_u64() == Some(2)
                    || location["range"]["start"]["line"].as_u64() == Some(3))
        }),
        "expected imported definition location: {result:?}"
    );
    assert!(
        references.iter().any(|location| {
            location["uri"].as_str() == Some(file_uri(&main_path).as_str())
                && location["range"]["start"]["line"].as_u64() == Some(5)
        }),
        "expected local call-site reference: {result:?}"
    );
}

#[test]
fn type_navigation_uses_imported_type_definition_location() {
    let root = temp_project("cross-module-type-navigation");
    let types_path = root.join("src/Types.saga");
    let main_path = root.join("src/Main.saga");

    std::fs::write(
        &types_path,
        "\
module Types

pub type BoardType =
  | Twintip
  | Hydrofoil
",
    )
    .expect("write types module");

    let main_source = "\
module Main

import Types (BoardType)

fun id_board : BoardType -> BoardType
id_board board = board
";
    std::fs::write(&main_path, main_source).expect("write main module");

    let result = {
        let mut lsp = LspHarness::start();
        lsp.initialize();
        let uri = file_uri(&main_path);

        lsp.send_notification(
            "textDocument/didOpen",
            json!({
                "textDocument": {
                    "uri": uri,
                    "languageId": "saga",
                    "version": 1,
                    "text": main_source
                }
            }),
        );
        let params = wait_for_diagnostics(&lsp, &uri, 1, 2);
        assert_eq!(
            params["diagnostics"].as_array().map(Vec::len),
            Some(0),
            "fixture must typecheck before type definition request, got {params:?}"
        );

        let definition_id = lsp.send_request(
            "textDocument/definition",
            json!({
                "textDocument": {
                    "uri": file_uri(&main_path)
                },
                "position": {
                    "line": 4,
                    "character": 15
                }
            }),
        );
        let definition = lsp
            .recv_until(Duration::from_secs(5), |message| {
                message.get("id").and_then(Value::as_i64) == Some(definition_id)
            })
            .expect("definition response");

        let references_id = lsp.send_request(
            "textDocument/references",
            json!({
                "textDocument": {
                    "uri": file_uri(&main_path)
                },
                "position": {
                    "line": 4,
                    "character": 15
                },
                "context": {
                    "includeDeclaration": true
                }
            }),
        );
        let references = lsp
            .recv_until(Duration::from_secs(5), |message| {
                message.get("id").and_then(Value::as_i64) == Some(references_id)
            })
            .expect("references response");
        (definition, references)
    };

    let _ = std::fs::remove_dir_all(&root);

    let (definition, references) = result;
    assert_eq!(
        definition["result"]["uri"].as_str(),
        Some(file_uri(&types_path).as_str()),
        "expected imported type definition: {definition:?}"
    );
    assert_eq!(
        definition["result"]["range"]["start"]["line"].as_u64(),
        Some(2),
        "expected BoardType name span, not broad type decl: {definition:?}"
    );

    let references = references["result"]
        .as_array()
        .expect("references result array");
    assert!(
        references.iter().any(|location| {
            location["uri"].as_str() == Some(file_uri(&types_path).as_str())
                && location["range"]["start"]["line"].as_u64() == Some(2)
        }),
        "expected imported type declaration location: {references:?}"
    );
    assert!(
        references.iter().any(|location| {
            location["uri"].as_str() == Some(file_uri(&main_path).as_str())
                && location["range"]["start"]["line"].as_u64() == Some(4)
        }),
        "expected local type annotation references: {references:?}"
    );
}

#[test]
fn type_references_from_definition_include_importing_modules() {
    let root = temp_project("project-type-references");
    let types_path = root.join("src/Types.saga");
    let main_path = root.join("src/Main.saga");

    let types_source = "\
module Types

pub type BoardType =
  | Twintip
  | Hydrofoil
";
    std::fs::write(&types_path, types_source).expect("write types module");

    let main_source = "\
module Main

import Types (BoardType)

fun id_board : BoardType -> BoardType
id_board board = board
";
    std::fs::write(&main_path, main_source).expect("write main module");

    let result = {
        let mut lsp = LspHarness::start();
        lsp.initialize();
        let main_uri = file_uri(&main_path);
        let types_uri = file_uri(&types_path);

        lsp.send_notification(
            "textDocument/didOpen",
            json!({
                "textDocument": {
                    "uri": main_uri,
                    "languageId": "saga",
                    "version": 1,
                    "text": main_source
                }
            }),
        );
        let main_params = wait_for_diagnostics(&lsp, &main_uri, 1, 2);
        assert_eq!(
            main_params["diagnostics"].as_array().map(Vec::len),
            Some(0),
            "main fixture must typecheck before references request, got {main_params:?}"
        );

        lsp.send_notification(
            "textDocument/didOpen",
            json!({
                "textDocument": {
                    "uri": types_uri,
                    "languageId": "saga",
                    "version": 1,
                    "text": types_source
                }
            }),
        );
        let types_params = wait_for_diagnostics(&lsp, &types_uri, 1, 2);
        assert_eq!(
            types_params["diagnostics"].as_array().map(Vec::len),
            Some(0),
            "types fixture must typecheck before references request, got {types_params:?}"
        );

        let references_id = lsp.send_request(
            "textDocument/references",
            json!({
                "textDocument": {
                    "uri": file_uri(&types_path)
                },
                "position": {
                    "line": 2,
                    "character": 10
                },
                "context": {
                    "includeDeclaration": true
                }
            }),
        );
        lsp.recv_until(Duration::from_secs(5), |message| {
            message.get("id").and_then(Value::as_i64) == Some(references_id)
        })
        .expect("references response")
    };

    let _ = std::fs::remove_dir_all(&root);

    let references = result["result"]
        .as_array()
        .expect("references result array");
    assert!(
        references.iter().any(|location| {
            location["uri"].as_str() == Some(file_uri(&types_path).as_str())
                && location["range"]["start"]["line"].as_u64() == Some(2)
        }),
        "expected defining type declaration location: {references:?}"
    );
    assert!(
        references.iter().any(|location| {
            location["uri"].as_str() == Some(file_uri(&main_path).as_str())
                && location["range"]["start"]["line"].as_u64() == Some(4)
        }),
        "expected importing module type annotation reference: {references:?}"
    );
}

#[test]
fn changing_imported_open_module_rechecks_open_dependents() {
    let root = temp_project("dependent-recheck");
    let helper_path = root.join("src/Helper.saga");
    let main_path = root.join("src/Main.saga");

    let helper_valid = "\
module Helper

pub fun forty_two : Unit -> Int
forty_two () = 42
";
    std::fs::write(&helper_path, helper_valid).expect("write helper module");

    let main_source = "\
module Main

import Helper (forty_two)

fun main : Unit -> Int
main () = forty_two ()
";
    std::fs::write(&main_path, main_source).expect("write main module");

    let main_uri = file_uri(&main_path);
    let helper_uri = file_uri(&helper_path);

    let result = {
        let mut lsp = LspHarness::start();
        lsp.initialize();

        lsp.send_notification(
            "textDocument/didOpen",
            json!({
                "textDocument": {
                    "uri": main_uri,
                    "languageId": "saga",
                    "version": 1,
                    "text": main_source
                }
            }),
        );
        lsp.recv_until(Duration::from_secs(5), |message| {
            diagnostics_for_uri(message, &file_uri(&main_path))
                .is_some_and(|params| params["diagnostics"].as_array().map(Vec::len) == Some(0))
        })
        .expect("initial main diagnostics");

        lsp.send_notification(
            "textDocument/didOpen",
            json!({
                "textDocument": {
                    "uri": helper_uri,
                    "languageId": "saga",
                    "version": 1,
                    "text": helper_valid
                }
            }),
        );
        lsp.recv_until(Duration::from_secs(5), |message| {
            diagnostics_for_uri(message, &file_uri(&helper_path))
                .is_some_and(|params| params["diagnostics"].as_array().map(Vec::len) == Some(0))
        })
        .expect("initial helper diagnostics");

        let helper_invalid = "\
module Helper

pub fun forty_two : Unit -> Int
forty_two () = \"nope\"
";
        std::fs::write(&helper_path, helper_invalid).expect("write invalid helper module");
        lsp.send_notification(
            "textDocument/didChange",
            json!({
                "textDocument": {
                    "uri": file_uri(&helper_path),
                    "version": 2
                },
                "contentChanges": [{
                    "text": helper_invalid
                }]
            }),
        );

        lsp.recv_until(Duration::from_secs(5), |message| {
            diagnostics_for_uri(message, &file_uri(&main_path)).is_some_and(|params| {
                params["version"].as_i64() == Some(1)
                    && params["diagnostics"]
                        .as_array()
                        .is_some_and(|diagnostics| !diagnostics.is_empty())
            })
        })
        .expect("dependent main diagnostics after helper change")
    };

    let _ = std::fs::remove_dir_all(&root);
    assert!(publish_diagnostics(&result).is_some());
}

#[test]
fn adding_imported_module_refreshes_project_module_map_without_restart() {
    let root = temp_project("module-map-refresh");
    let helper_path = root.join("src/Helper.saga");
    let main_path = root.join("src/Main.saga");

    let main_source = "\
module Main

import Helper (forty_two)

fun main : Unit -> Int
main () = forty_two ()
";
    std::fs::write(&main_path, main_source).expect("write main module");

    let main_uri = file_uri(&main_path);

    let result = {
        let mut lsp = LspHarness::start();
        lsp.initialize();

        lsp.send_notification(
            "textDocument/didOpen",
            json!({
                "textDocument": {
                    "uri": main_uri,
                    "languageId": "saga",
                    "version": 1,
                    "text": main_source
                }
            }),
        );
        lsp.recv_until(Duration::from_secs(5), |message| {
            diagnostics_for_uri(message, &file_uri(&main_path)).is_some_and(|params| {
                params["version"].as_i64() == Some(1)
                    && params["diagnostics"]
                        .as_array()
                        .is_some_and(|diagnostics| !diagnostics.is_empty())
            })
        })
        .expect("missing import diagnostics");

        std::fs::write(
            &helper_path,
            "\
module Helper

pub fun forty_two : Unit -> Int
forty_two () = 42
",
        )
        .expect("write helper module");

        lsp.send_notification(
            "textDocument/didChange",
            json!({
                "textDocument": {
                    "uri": file_uri(&main_path),
                    "version": 2
                },
                "contentChanges": [{
                    "text": main_source
                }]
            }),
        );

        lsp.recv_until(Duration::from_secs(5), |message| {
            diagnostics_for_uri(message, &file_uri(&main_path)).is_some_and(|params| {
                params["version"].as_i64() == Some(2)
                    && params["diagnostics"].as_array().map(Vec::len) == Some(0)
            })
        })
        .expect("diagnostics to clear after module map refresh")
    };

    let _ = std::fs::remove_dir_all(&root);
    assert!(publish_diagnostics(&result).is_some());
}

#[test]
fn unsaved_imported_module_change_rechecks_dependents_with_open_text() {
    let root = temp_project("unsaved-dependent-recheck");
    let helper_path = root.join("src/Helper.saga");
    let main_path = root.join("src/Main.saga");

    let helper_valid = "\
module Helper

pub fun value : Unit -> Int
value () = 42
";
    std::fs::write(&helper_path, helper_valid).expect("write helper module");

    let main_source = "\
module Main

import Helper (value)

fun main : Unit -> Int
main () = value ()
";
    std::fs::write(&main_path, main_source).expect("write main module");

    let result = {
        let mut lsp = LspHarness::start();
        lsp.initialize();

        lsp.send_notification(
            "textDocument/didOpen",
            json!({
                "textDocument": {
                    "uri": file_uri(&main_path),
                    "languageId": "saga",
                    "version": 1,
                    "text": main_source
                }
            }),
        );
        lsp.recv_until(Duration::from_secs(5), |message| {
            diagnostics_for_uri(message, &file_uri(&main_path))
                .is_some_and(|params| params["diagnostics"].as_array().map(Vec::len) == Some(0))
        })
        .expect("initial main diagnostics");

        lsp.send_notification(
            "textDocument/didOpen",
            json!({
                "textDocument": {
                    "uri": file_uri(&helper_path),
                    "languageId": "saga",
                    "version": 1,
                    "text": helper_valid
                }
            }),
        );
        lsp.recv_until(Duration::from_secs(5), |message| {
            diagnostics_for_uri(message, &file_uri(&helper_path))
                .is_some_and(|params| params["diagnostics"].as_array().map(Vec::len) == Some(0))
        })
        .expect("initial helper diagnostics");

        let helper_unsaved = "\
module Helper

pub fun value : Unit -> String
value () = \"forty two\"
";
        lsp.send_notification(
            "textDocument/didChange",
            json!({
                "textDocument": {
                    "uri": file_uri(&helper_path),
                    "version": 2
                },
                "contentChanges": [{
                    "text": helper_unsaved
                }]
            }),
        );

        lsp.recv_until(Duration::from_secs(5), |message| {
            diagnostics_for_uri(message, &file_uri(&main_path)).is_some_and(|params| {
                params["version"].as_i64() == Some(1)
                    && params["diagnostics"]
                        .as_array()
                        .is_some_and(|diagnostics| !diagnostics.is_empty())
            })
        })
        .expect("dependent main diagnostics from unsaved helper text")
    };

    let on_disk_helper = std::fs::read_to_string(&helper_path).expect("read helper from disk");
    let _ = std::fs::remove_dir_all(&root);

    assert_eq!(on_disk_helper, helper_valid);
    assert!(publish_diagnostics(&result).is_some());
}

#[test]
fn project_path_dependency_exposed_modules_are_available() {
    let root = temp_project("path-dependency");
    let dep_root = root.join("deps/kraken");
    let dep_src = dep_root.join("src");
    let main_path = root.join("src/Main.saga");
    let kraken_core_path = dep_src.join("Core.saga");

    std::fs::create_dir_all(&dep_src).expect("create dependency src");
    std::fs::write(
        root.join("project.toml"),
        "\
[project]
name = \"app\"

[deps]
kraken = { path = \"deps/kraken\" }
",
    )
    .expect("write app project.toml");
    std::fs::write(
        dep_root.join("project.toml"),
        "\
[project]
name = \"kraken\"

[library]
module = \"Kraken\"
expose = [\"Kraken.Core\"]
",
    )
    .expect("write dependency project.toml");
    std::fs::write(
        &kraken_core_path,
        "\
module Kraken.Core

pub fun answer : Unit -> Int
answer () = 42
",
    )
    .expect("write dependency module");

    let main_source = "\
module Main

import Kraken.Core (answer)

fun main : Unit -> Int
main () = answer ()
";
    std::fs::write(&main_path, main_source).expect("write main module");

    let result = {
        let mut lsp = LspHarness::start();
        lsp.initialize();

        lsp.send_notification(
            "textDocument/didOpen",
            json!({
                "textDocument": {
                    "uri": file_uri(&main_path),
                    "languageId": "saga",
                    "version": 1,
                    "text": main_source
                }
            }),
        );

        lsp.recv_until(Duration::from_secs(5), |message| {
            diagnostics_for_uri(message, &file_uri(&main_path)).is_some_and(|params| {
                params["version"].as_i64() == Some(1)
                    && params["diagnostics"].as_array().map(Vec::len) == Some(0)
            })
        })
        .expect("dependency import diagnostics to clear")
    };

    let _ = std::fs::remove_dir_all(&root);
    assert!(publish_diagnostics(&result).is_some());
}
