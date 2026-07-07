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

fn completion_items(lsp: &mut LspHarness, uri: &str, line: u32, character: u32) -> Vec<Value> {
    let id = lsp.send_request(
        "textDocument/completion",
        json!({
            "textDocument": {
                "uri": uri
            },
            "position": {
                "line": line,
                "character": character
            }
        }),
    );
    let response = lsp
        .recv_until(Duration::from_secs(5), |message| {
            message.get("id").and_then(Value::as_i64) == Some(id)
        })
        .expect("completion response");
    response["result"]
        .as_array()
        .unwrap_or_else(|| panic!("completion item array, got response: {response:?}"))
        .clone()
}

fn code_actions(lsp: &mut LspHarness, uri: &str, diagnostic: &Value) -> Vec<Value> {
    let id = lsp.send_request(
        "textDocument/codeAction",
        json!({
            "textDocument": {
                "uri": uri
            },
            "range": diagnostic["range"].clone(),
            "context": {
                "diagnostics": [diagnostic.clone()],
                "only": ["quickfix"]
            }
        }),
    );
    let response = lsp
        .recv_until(Duration::from_secs(5), |message| {
            message.get("id").and_then(Value::as_i64) == Some(id)
        })
        .expect("codeAction response");
    response["result"].as_array().cloned().unwrap_or_default()
}

fn signature_help(lsp: &mut LspHarness, uri: &str, line: u32, character: u32) -> Option<Value> {
    let id = lsp.send_request(
        "textDocument/signatureHelp",
        json!({
            "textDocument": {
                "uri": uri
            },
            "position": {
                "line": line,
                "character": character
            }
        }),
    );
    let response = lsp
        .recv_until(Duration::from_secs(5), |message| {
            message.get("id").and_then(Value::as_i64) == Some(id)
        })
        .expect("signatureHelp response");
    (!response["result"].is_null()).then(|| response["result"].clone())
}

fn synthetic_diagnostic(
    message: &str,
    start_line: u32,
    start_character: u32,
    end_line: u32,
    end_character: u32,
) -> Value {
    json!({
        "range": {
            "start": {
                "line": start_line,
                "character": start_character
            },
            "end": {
                "line": end_line,
                "character": end_character
            }
        },
        "severity": 1,
        "source": "saga",
        "message": message
    })
}

fn completion_labels(lsp: &mut LspHarness, uri: &str, line: u32, character: u32) -> Vec<String> {
    completion_items(lsp, uri, line, character)
        .iter()
        .filter_map(|item| item["label"].as_str().map(ToString::to_string))
        .collect()
}

fn formatting_edits(lsp: &mut LspHarness, uri: &str) -> Option<Vec<Value>> {
    let id = lsp.send_request(
        "textDocument/formatting",
        json!({
            "textDocument": {
                "uri": uri
            },
            "options": {
                "tabSize": 2,
                "insertSpaces": true
            }
        }),
    );
    let response = lsp
        .recv_until(Duration::from_secs(5), |message| {
            message.get("id").and_then(Value::as_i64) == Some(id)
        })
        .expect("formatting response");
    response["result"].as_array().cloned()
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
fn formatting_uses_current_document_text() {
    let mut lsp = LspHarness::start();
    lsp.initialize();
    let uri = saga_uri("formatting");
    let source = "main () = {\nlet x = 1\nprintln x\n}";

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

    let edits = formatting_edits(&mut lsp, &saga_uri("formatting"))
        .expect("formatting should return an edit list");
    assert_eq!(edits.len(), 1, "expected whole-document edit: {edits:?}");
    let edit = &edits[0];
    assert_eq!(
        edit["newText"].as_str(),
        Some("main () = {\n  let x = 1\n  println x\n}\n")
    );
    assert_eq!(edit["range"]["start"]["line"].as_u64(), Some(0));
    assert_eq!(edit["range"]["start"]["character"].as_u64(), Some(0));
    assert_eq!(edit["range"]["end"]["line"].as_u64(), Some(3));
    assert_eq!(edit["range"]["end"]["character"].as_u64(), Some(1));
}

#[test]
fn opening_empty_new_file_does_not_crash() {
    let mut lsp = LspHarness::start();
    lsp.initialize();
    let uri = saga_uri("empty-new-file");

    lsp.send_notification(
        "textDocument/didOpen",
        json!({
            "textDocument": {
                "uri": uri,
                "languageId": "saga",
                "version": 1,
                "text": ""
            }
        }),
    );

    let id = lsp.send_request(
        "textDocument/documentSymbol",
        json!({
            "textDocument": {
                "uri": saga_uri("empty-new-file")
            }
        }),
    );
    lsp.recv_until(Duration::from_secs(5), |message| {
        message.get("id").and_then(Value::as_i64) == Some(id)
    })
    .expect("document symbol response proves server stayed alive");
}

#[test]
fn code_actions_suggest_missing_imports_and_qualified_use() {
    let root = temp_project("code-actions-imports");
    let lib_path = root.join("src/Lib.saga");
    let main_path = root.join("src/Main.saga");
    let lib_source = "\
module Lib

pub trait Describe a {
  fun describe_it : a -> String
}

pub fun greet : Unit -> String
greet () = \"hi\"
";
    std::fs::write(&lib_path, lib_source).expect("write lib module");

    let imported_without_exposing = "\
module Main

import Lib

main () = greet ()
";
    std::fs::write(&main_path, imported_without_exposing).expect("write main module");

    let (
        bare_titles,
        bare_edit,
        trait_method_titles,
        trait_method_edit,
        qualified_titles,
        qualified_edit,
    ) = {
        let mut lsp = LspHarness::start();
        lsp.initialize();
        let lib_uri = file_uri(&lib_path);
        let main_uri = file_uri(&main_path);

        lsp.send_notification(
            "textDocument/didOpen",
            json!({
                "textDocument": {
                    "uri": lib_uri,
                    "languageId": "saga",
                    "version": 1,
                    "text": lib_source
                }
            }),
        );
        let _ = wait_for_diagnostics(&lsp, &file_uri(&lib_path), 1, 2);

        lsp.send_notification(
            "textDocument/didOpen",
            json!({
                "textDocument": {
                    "uri": main_uri,
                    "languageId": "saga",
                    "version": 1,
                    "text": imported_without_exposing
                }
            }),
        );
        let _ = wait_for_diagnostics(&lsp, &file_uri(&main_path), 1, 2);
        let bare_diagnostic = synthetic_diagnostic("undefined variable: greet", 4, 10, 4, 15);
        let bare_actions = code_actions(&mut lsp, &file_uri(&main_path), &bare_diagnostic);
        let bare_titles = action_titles(&bare_actions);
        let bare_edit = action_new_text(&bare_actions, "Expose `greet` from import Lib");

        let trait_method_source = "\
module Main

import Lib

main () = describe_it ()
";
        lsp.send_notification(
            "textDocument/didChange",
            json!({
                "textDocument": {
                    "uri": file_uri(&main_path),
                    "version": 2
                },
                "contentChanges": [{
                    "text": trait_method_source
                }]
            }),
        );
        let _ = wait_for_diagnostics(&lsp, &file_uri(&main_path), 2, 2);
        let trait_diagnostic =
            synthetic_diagnostic("undefined variable: describe_it", 4, 10, 4, 21);
        let trait_actions = code_actions(&mut lsp, &file_uri(&main_path), &trait_diagnostic);
        let trait_method_titles = action_titles(&trait_actions);
        let trait_method_edit =
            action_new_text(&trait_actions, "Expose `Describe` from import Lib");

        let qualified_source = "\
module Main

main () = Lib.greet ()
";
        lsp.send_notification(
            "textDocument/didChange",
            json!({
                "textDocument": {
                    "uri": file_uri(&main_path),
                    "version": 3
                },
                "contentChanges": [{
                    "text": qualified_source
                }]
            }),
        );
        let _ = wait_for_diagnostics(&lsp, &file_uri(&main_path), 3, 2);
        let qualified_diagnostic =
            synthetic_diagnostic("unknown qualified name 'Lib.greet'", 2, 10, 2, 19);
        let qualified_actions =
            code_actions(&mut lsp, &file_uri(&main_path), &qualified_diagnostic);
        let qualified_titles = action_titles(&qualified_actions);
        let qualified_edit = action_new_text(&qualified_actions, "Add `import Lib`");

        (
            bare_titles,
            bare_edit,
            trait_method_titles,
            trait_method_edit,
            qualified_titles,
            qualified_edit,
        )
    };

    let _ = std::fs::remove_dir_all(&root);

    assert!(
        bare_titles
            .iter()
            .any(|title| title == "Expose `greet` from import Lib"),
        "missing expose-function action: {bare_titles:?}"
    );
    assert!(
        bare_titles.iter().any(|title| title == "Use `Lib.greet`"),
        "missing qualify-function action: {bare_titles:?}"
    );
    assert_eq!(bare_edit.as_deref(), Some(" (greet)"));

    assert!(
        trait_method_titles
            .iter()
            .any(|title| title == "Expose `Describe` from import Lib"),
        "trait method should import owning trait, not method: {trait_method_titles:?}"
    );
    assert_eq!(trait_method_edit.as_deref(), Some(" (Describe)"));
    assert!(
        !trait_method_titles
            .iter()
            .any(|title| title.contains("describe_it` from import")),
        "trait method import action should not expose method directly: {trait_method_titles:?}"
    );

    assert!(
        qualified_titles
            .iter()
            .any(|title| title == "Add `import Lib`"),
        "missing qualified-prefix import action: {qualified_titles:?}"
    );
    assert_eq!(qualified_edit.as_deref(), Some("\nimport Lib\n\n"));
}

#[test]
fn signature_help_uses_local_labels_and_imported_schemes() {
    let root = temp_project("signature-help");
    let lib_path = root.join("src/Lib.saga");
    let main_path = root.join("src/Main.saga");
    let lib_source = "\
module Lib

pub fun join : (left: String) -> (right: String) -> String
join left right = left <> right
";
    let main_source = "\
module Main

import Lib

fun add : (x: Int) -> (y: Int) -> Int
add x y = x + y

main () = {
  let sum = add 1 2
  Lib.join \"a\" \"b\"
}
";
    std::fs::write(&lib_path, lib_source).expect("write lib module");
    std::fs::write(&main_path, main_source).expect("write main module");

    let (local_help, imported_help) = {
        let mut lsp = LspHarness::start();
        lsp.initialize();

        lsp.send_notification(
            "textDocument/didOpen",
            json!({
                "textDocument": {
                    "uri": file_uri(&lib_path),
                    "languageId": "saga",
                    "version": 1,
                    "text": lib_source
                }
            }),
        );
        let _ = wait_for_diagnostics(&lsp, &file_uri(&lib_path), 1, 2);

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
        let params = wait_for_diagnostics(&lsp, &file_uri(&main_path), 1, 2);
        assert_eq!(
            params["diagnostics"].as_array().map(|diagnostics| {
                diagnostics
                    .iter()
                    .filter(|diagnostic| diagnostic["severity"].as_i64() == Some(1))
                    .count()
            }),
            Some(0),
            "fixture must typecheck before signature help request, got {params:?}"
        );

        let local_help =
            signature_help(&mut lsp, &file_uri(&main_path), 8, 18).expect("local signature help");
        let imported_help = signature_help(&mut lsp, &file_uri(&main_path), 9, 17)
            .expect("imported signature help");
        (local_help, imported_help)
    };

    let _ = std::fs::remove_dir_all(&root);

    assert_eq!(
        local_help["signatures"][0]["label"].as_str(),
        Some("(x: Int) -> (y: Int) -> Int")
    );
    assert_eq!(
        local_help["signatures"][0]["activeParameter"].as_u64(),
        Some(1)
    );
    assert_eq!(
        local_help["signatures"][0]["parameters"][0]["label"].as_str(),
        Some("x: Int")
    );
    assert_eq!(
        local_help["signatures"][0]["parameters"][1]["label"].as_str(),
        Some("y: Int")
    );

    assert_eq!(
        imported_help["signatures"][0]["label"].as_str(),
        Some("String -> String -> String")
    );
    assert_eq!(
        imported_help["signatures"][0]["activeParameter"].as_u64(),
        Some(1)
    );
}

#[test]
fn signature_help_covers_trait_methods_and_effect_ops() {
    let root = temp_project("signature-help-traits-effects");
    let main_path = root.join("src/Main.saga");
    let source = "\
module Main

pub trait Describe a {
  fun describe_it : a -> String
}

pub effect Log {
  fun write : String -> Unit
}

pub handler ignore for Log {
  write _ = resume ()
}

impl Describe for String {
  describe_it s = s
}

main () = {
  let a = describe_it \"Dylan\"
  let b = Log.write! \"hello\"
  ()
} with ignore
";
    std::fs::write(&main_path, source).expect("write main module");

    let (trait_help, effect_help) = {
        let mut lsp = LspHarness::start();
        lsp.initialize();
        lsp.send_notification(
            "textDocument/didOpen",
            json!({
                "textDocument": {
                    "uri": file_uri(&main_path),
                    "languageId": "saga",
                    "version": 1,
                    "text": source
                }
            }),
        );
        let params = wait_for_diagnostics(&lsp, &file_uri(&main_path), 1, 2);
        assert_eq!(
            params["diagnostics"].as_array().map(|diagnostics| {
                diagnostics
                    .iter()
                    .filter(|diagnostic| diagnostic["severity"].as_i64() == Some(1))
                    .count()
            }),
            Some(0),
            "fixture must typecheck before signature help request, got {params:?}"
        );

        let trait_help =
            signature_help(&mut lsp, &file_uri(&main_path), 19, 24).expect("trait signature help");
        let effect_help =
            signature_help(&mut lsp, &file_uri(&main_path), 20, 23).expect("effect signature help");
        (trait_help, effect_help)
    };

    let _ = std::fs::remove_dir_all(&root);

    assert_eq!(
        trait_help["signatures"][0]["label"].as_str(),
        Some("Describe.describe_it : a -> String")
    );
    assert_eq!(
        trait_help["signatures"][0]["parameters"][0]["label"].as_str(),
        Some("a")
    );
    assert_eq!(
        trait_help["signatures"][0]["activeParameter"].as_u64(),
        Some(0)
    );

    assert_eq!(
        effect_help["signatures"][0]["label"].as_str(),
        Some("Log.write : String -> Unit")
    );
    assert_eq!(
        effect_help["signatures"][0]["parameters"][0]["label"].as_str(),
        Some("String")
    );
    assert_eq!(
        effect_help["signatures"][0]["activeParameter"].as_u64(),
        Some(0)
    );
}

fn action_titles(actions: &[Value]) -> Vec<String> {
    actions
        .iter()
        .filter_map(|action| action["title"].as_str().map(ToString::to_string))
        .collect()
}

fn action_new_text(actions: &[Value], title: &str) -> Option<String> {
    actions
        .iter()
        .find(|action| action["title"].as_str() == Some(title))
        .and_then(|action| {
            action["edit"]["changes"]
                .as_object()?
                .values()
                .next()?
                .as_array()?
                .first()?
                .get("newText")?
                .as_str()
                .map(ToString::to_string)
        })
}

#[test]
fn dirty_module_declaration_does_not_pollute_import_completions() {
    let root = temp_project("dirty-module-name-completion");
    let db_schema_path = root.join("src/DbSchema.saga");
    let database_path = root.join("src/Database.saga");
    let main_path = root.join("src/Main.saga");

    let db_schema_source = "\
module SeshImporter.DbSchema

pub fun schema : Unit -> Int
schema () = 1
";
    std::fs::write(&db_schema_path, db_schema_source).expect("write db schema module");
    std::fs::write(
        &database_path,
        "\
module SeshImporter.Database

pub fun value : Unit -> Int
value () = 1
",
    )
    .expect("write database module");
    let main_source = "\
module Main

import SeshImporter.D
";
    std::fs::write(&main_path, main_source).expect("write main module");

    let result = {
        let mut lsp = LspHarness::start();
        lsp.initialize();

        lsp.send_notification(
            "textDocument/didOpen",
            json!({
                "textDocument": {
                    "uri": file_uri(&db_schema_path),
                    "languageId": "saga",
                    "version": 1,
                    "text": db_schema_source
                }
            }),
        );
        let _ = wait_for_diagnostics(&lsp, &file_uri(&db_schema_path), 1, 2);

        lsp.send_notification(
            "textDocument/didChange",
            json!({
                "textDocument": {
                    "uri": file_uri(&db_schema_path),
                    "version": 2
                },
                "contentChanges": [{
                    "text": "module SeshImporter.D\n"
                }]
            }),
        );
        let _ = wait_for_diagnostics(&lsp, &file_uri(&db_schema_path), 2, 1);

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
        let _ = wait_for_diagnostics(&lsp, &file_uri(&main_path), 1, 1);
        completion_items(&mut lsp, &file_uri(&main_path), 2, 21)
    };

    let _ = std::fs::remove_dir_all(&root);

    let labels: Vec<_> = result
        .iter()
        .filter_map(|item| item["label"].as_str())
        .collect();
    assert!(
        labels.contains(&"SeshImporter.DbSchema"),
        "saved module should still complete: {result:?}"
    );
    assert!(
        labels.contains(&"SeshImporter.Database"),
        "other saved module should complete: {result:?}"
    );
    assert!(
        !labels.contains(&"SeshImporter.D"),
        "dirty partial module name should not complete: {result:?}"
    );
    let database = result
        .iter()
        .find(|item| item["label"].as_str() == Some("SeshImporter.Database"))
        .unwrap_or_else(|| panic!("missing database completion: {result:?}"));
    assert_eq!(
        database["textEdit"]["newText"].as_str(),
        Some("SeshImporter.Database"),
        "module completion should replace with the full module name: {database:?}"
    );
    assert_eq!(
        database["textEdit"]["range"]["start"]["character"].as_u64(),
        Some(7)
    );
    assert_eq!(
        database["textEdit"]["range"]["end"]["character"].as_u64(),
        Some(21)
    );
}

#[test]
fn completion_uses_context_and_semantic_project_data() {
    let root = temp_project("completion-contexts");
    let lib_path = root.join("src/Lib.saga");
    let other_dir = root.join("src/Other");
    let other_path = other_dir.join("Thing.saga");
    let main_path = root.join("src/Main.saga");

    let lib_source = "\
module Lib

pub record Person {
  name: String,
  age: Int,
}

pub trait Describe a {
  fun describe : a -> String
}

pub effect Log {
  fun write : String -> Unit
}

pub handler ignore for Log {
  write _ = resume ()
}

pub fun greet : Person -> String
greet p = p.name
";
    std::fs::write(&lib_path, lib_source).expect("write lib module");
    std::fs::create_dir_all(&other_dir).expect("create other module dir");
    std::fs::write(
        &other_path,
        "\
module Other.Thing

pub fun value : Unit -> Int
value () = 1
",
    )
    .expect("write other module");

    let main_source = "\
module Main

import Lib (Person, Describe, Log, ignore)

impl Describe for Person {
  describe p = p.name
}

fun make : Person -> String needs {Log}
make p = {
  let q = Person { name: \"Dylan\", age: 1 }
  let field = p.name
  let qualified = Lib.greet q
  Log.write! \"x\"
  p |> describe
} with ignore
";
    std::fs::write(&main_path, main_source).expect("write main module");

    let import_source = "\
module Main

import L
";
    let current_module_import_source = "\
module Main

import 
";
    let dotted_import_source = "\
module Main

import Other.
";
    let import_exposing_source = "\
module Main

import Lib (g
";
    let import_exposing_all_source = "\
module Main

import Lib (
";

    let result = {
        let mut lsp = LspHarness::start();
        lsp.initialize();
        let main_uri = file_uri(&main_path);

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
        let params = wait_for_diagnostics(&lsp, &file_uri(&main_path), 1, 2);
        assert_eq!(
            params["diagnostics"].as_array().map(|diagnostics| {
                diagnostics
                    .iter()
                    .filter(|diagnostic| diagnostic["severity"].as_i64() == Some(1))
                    .count()
            }),
            Some(0),
            "fixture must typecheck before completion request, got {params:?}"
        );

        let trait_labels = completion_labels(&mut lsp, &file_uri(&main_path), 4, 8);
        let type_labels = completion_labels(&mut lsp, &file_uri(&main_path), 8, 13);
        let effect_labels = completion_labels(&mut lsp, &file_uri(&main_path), 8, 38);
        let record_literal_labels = completion_labels(&mut lsp, &file_uri(&main_path), 10, 24);
        let record_dot_labels = completion_labels(&mut lsp, &file_uri(&main_path), 11, 20);
        let qualified_items = completion_items(&mut lsp, &file_uri(&main_path), 12, 22);
        let effect_op_labels = completion_labels(&mut lsp, &file_uri(&main_path), 13, 8);
        let local_labels = completion_labels(&mut lsp, &file_uri(&main_path), 14, 2);
        let handler_labels = completion_labels(&mut lsp, &file_uri(&main_path), 15, 10);

        lsp.send_notification(
            "textDocument/didChange",
            json!({
                "textDocument": {
                    "uri": file_uri(&main_path),
                    "version": 2
                },
                "contentChanges": [{
                    "text": import_source
                }]
            }),
        );
        let _ = wait_for_diagnostics(&lsp, &file_uri(&main_path), 2, 1);
        let import_labels = completion_labels(&mut lsp, &file_uri(&main_path), 2, 8);

        lsp.send_notification(
            "textDocument/didChange",
            json!({
                "textDocument": {
                    "uri": file_uri(&main_path),
                    "version": 3
                },
                "contentChanges": [{
                    "text": current_module_import_source
                }]
            }),
        );
        let _ = wait_for_diagnostics(&lsp, &file_uri(&main_path), 3, 1);
        let current_module_import_labels = completion_labels(&mut lsp, &file_uri(&main_path), 2, 7);

        lsp.send_notification(
            "textDocument/didChange",
            json!({
                "textDocument": {
                    "uri": file_uri(&main_path),
                    "version": 4
                },
                "contentChanges": [{
                    "text": dotted_import_source
                }]
            }),
        );
        let _ = wait_for_diagnostics(&lsp, &file_uri(&main_path), 4, 1);
        let dotted_import_labels = completion_labels(&mut lsp, &file_uri(&main_path), 2, 13);

        lsp.send_notification(
            "textDocument/didChange",
            json!({
                "textDocument": {
                    "uri": file_uri(&main_path),
                    "version": 5
                },
                "contentChanges": [{
                    "text": import_exposing_source
                }]
            }),
        );
        let _ = wait_for_diagnostics(&lsp, &file_uri(&main_path), 5, 1);
        let import_exposing_labels = completion_labels(&mut lsp, &file_uri(&main_path), 2, 13);

        lsp.send_notification(
            "textDocument/didChange",
            json!({
                "textDocument": {
                    "uri": file_uri(&main_path),
                    "version": 6
                },
                "contentChanges": [{
                    "text": import_exposing_all_source
                }]
            }),
        );
        let _ = wait_for_diagnostics(&lsp, &file_uri(&main_path), 6, 1);
        let import_exposing_all_labels = completion_labels(&mut lsp, &file_uri(&main_path), 2, 12);

        (
            trait_labels,
            type_labels,
            effect_labels,
            record_literal_labels,
            record_dot_labels,
            qualified_items,
            effect_op_labels,
            local_labels,
            handler_labels,
            import_labels,
            current_module_import_labels,
            dotted_import_labels,
            import_exposing_labels,
            import_exposing_all_labels,
        )
    };

    let _ = std::fs::remove_dir_all(&root);

    let (
        trait_labels,
        type_labels,
        effect_labels,
        record_literal_labels,
        record_dot_labels,
        qualified_items,
        effect_op_labels,
        local_labels,
        handler_labels,
        import_labels,
        current_module_import_labels,
        dotted_import_labels,
        import_exposing_labels,
        import_exposing_all_labels,
    ) = result;

    assert!(
        trait_labels.iter().any(|label| label == "Describe"),
        "missing trait completion: {trait_labels:?}"
    );
    assert!(
        type_labels.iter().any(|label| label == "Person"),
        "missing type completion: {type_labels:?}"
    );
    assert!(
        effect_labels.iter().any(|label| label == "Log"),
        "missing effect completion: {effect_labels:?}"
    );
    assert!(
        record_literal_labels.iter().any(|label| label == "name"),
        "missing record literal field completion: {record_literal_labels:?}"
    );
    assert!(
        record_dot_labels.iter().any(|label| label == "name"),
        "missing record dot field completion: {record_dot_labels:?}"
    );
    let greet = qualified_items
        .iter()
        .find(|item| item["label"].as_str() == Some("greet"))
        .unwrap_or_else(|| panic!("missing qualified function completion: {qualified_items:?}"));
    assert_eq!(
        greet["detail"].as_str(),
        Some("Person -> String"),
        "qualified function completion should show signature: {qualified_items:?}"
    );
    let person_ctor = qualified_items
        .iter()
        .find(|item| item["label"].as_str() == Some("Person"))
        .unwrap_or_else(|| panic!("missing qualified constructor completion: {qualified_items:?}"));
    assert_eq!(
        person_ctor["kind"].as_u64(),
        Some(4),
        "qualified record constructor should be classified as constructor: {qualified_items:?}"
    );
    assert!(
        effect_op_labels.iter().any(|label| label == "write"),
        "missing effect operation completion: {effect_op_labels:?}"
    );
    assert!(
        local_labels.iter().any(|label| label == "p")
            && local_labels.iter().any(|label| label == "q")
            && local_labels.iter().any(|label| label == "field"),
        "missing local semantic completions: {local_labels:?}"
    );
    assert!(
        handler_labels.iter().any(|label| label == "ignore"),
        "missing handler completion: {handler_labels:?}"
    );
    assert!(
        import_labels.iter().any(|label| label == "Lib"),
        "missing import module completion after syntax error: {import_labels:?}"
    );
    assert!(
        !current_module_import_labels
            .iter()
            .any(|label| label == "Main"),
        "import module completion should not suggest the current module: {current_module_import_labels:?}"
    );
    assert!(
        dotted_import_labels
            .iter()
            .any(|label| label == "Other.Thing"),
        "missing dotted project module completion: {dotted_import_labels:?}"
    );
    assert!(
        import_exposing_labels.iter().any(|label| label == "greet"),
        "missing import exposing value completion: {import_exposing_labels:?}"
    );
    assert!(
        !import_exposing_labels.iter().any(|label| label == "Lib"),
        "import exposing completion should list module exports, not modules: {import_exposing_labels:?}"
    );
    assert!(
        import_exposing_all_labels
            .iter()
            .any(|label| label == "Person")
            && import_exposing_all_labels
                .iter()
                .any(|label| label == "Describe")
            && import_exposing_all_labels
                .iter()
                .any(|label| label == "Log")
            && import_exposing_all_labels
                .iter()
                .any(|label| label == "ignore"),
        "missing import exposing exported type/trait/effect/handler completions: {import_exposing_all_labels:?}"
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
fn diagnostics_include_missing_imported_trait_impl_constraint() {
    let root = temp_project("missing-trait-impl-diagnostic");
    let db_path = root.join("src/Db.saga");
    let main_path = root.join("src/Main.saga");

    std::fs::write(
        &db_path,
        "\
module Db

pub type DbError = DbError
",
    )
    .expect("write db module");

    let main_source = r#"
module Main

import Db

fun render : Db.DbError -> String
render e = panic $"insert_records failed: {debug e}"
"#;
    std::fs::write(&main_path, main_source).expect("write main module");

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
    let messages: Vec<_> = params["diagnostics"]
        .as_array()
        .expect("diagnostics array")
        .iter()
        .filter_map(|diagnostic| diagnostic["message"].as_str())
        .collect();

    let _ = std::fs::remove_dir_all(&root);

    assert!(
        messages
            .iter()
            .any(|message| message.contains("Debug") && message.contains("DbError")),
        "expected missing Debug DbError diagnostic, got {messages:?}"
    );
}

#[test]
fn diagnostics_include_missing_dependency_trait_impl_constraint() {
    let root = temp_project("missing-dependency-trait-impl-diagnostic");
    let dep_root = root.join("deps/kraken");
    let dep_src = dep_root.join("src/Kraken");
    let main_path = root.join("src/Main.saga");
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
expose = [\"Kraken.Db\"]
",
    )
    .expect("write dependency project.toml");
    std::fs::write(
        dep_src.join("Db.saga"),
        "\
module Kraken.Db

pub type DbError = DbError

pub fun insert : Unit -> Result Unit DbError
insert () = Err DbError
",
    )
    .expect("write dependency db module");

    let main_source = r#"
module Main

import Kraken.Db

fun render : Unit -> Unit
render () = case Kraken.Db.insert () {
  Ok _ -> ()
  Err e -> panic $"insert_records failed: {debug e}"
}
"#;
    std::fs::write(&main_path, main_source).expect("write main module");

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
    let messages: Vec<_> = params["diagnostics"]
        .as_array()
        .expect("diagnostics array")
        .iter()
        .filter_map(|diagnostic| diagnostic["message"].as_str())
        .collect();

    let _ = std::fs::remove_dir_all(&root);

    assert!(
        messages
            .iter()
            .any(|message| message.contains("Debug") && message.contains("DbError")),
        "expected missing Debug DbError diagnostic, got {messages:?}"
    );
}

#[test]
fn diagnostics_forward_undefined_trait_errors_from_imported_modules() {
    let root = temp_project("imported-undefined-trait-diagnostic");
    let main_path = root.join("src/Main.saga");
    let database_path = root.join("src/Database.saga");
    let db_dir = root.join("src/Db");
    let sesh_path = db_dir.join("Sesh.saga");
    std::fs::create_dir_all(&db_dir).expect("create db module dir");

    std::fs::write(
        &sesh_path,
        "\
module SeshImporter.Db.Sesh

pub record Sesh {
  id: Int
}

impl PgType for Sesh {}
",
    )
    .expect("write sesh module");
    std::fs::write(
        &database_path,
        "\
module SeshImporter.Database

import SeshImporter.Db.Sesh

pub fun touch : Unit -> Unit
touch () = ()
",
    )
    .expect("write database module");
    let main_source = "\
module Main

import SeshImporter.Database

main () = ()
";
    std::fs::write(&main_path, main_source).expect("write main module");

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
    let messages: Vec<_> = params["diagnostics"]
        .as_array()
        .expect("diagnostics array")
        .iter()
        .filter_map(|diagnostic| diagnostic["message"].as_str())
        .collect();

    let _ = std::fs::remove_dir_all(&root);

    assert!(
        messages.iter().any(|message| message.contains(
            "type error in module 'SeshImporter.Database': type error in module 'SeshImporter.Db.Sesh': impl for undefined trait: PgType"
        )),
        "expected imported undefined trait diagnostic, got {messages:?}"
    );
}

#[test]
fn diagnostics_report_undefined_trait_in_open_module() {
    let root = temp_project("open-undefined-trait-diagnostic");
    let main_path = root.join("src/Main.saga");
    let source = "\
module Main

pub record Sesh {
  id: Int
}

impl PgType for Sesh {}
";
    std::fs::write(&main_path, source).expect("write main module");

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
                "text": source
            }
        }),
    );
    let params = wait_for_diagnostics(&lsp, &uri, 1, 2);
    let messages: Vec<_> = params["diagnostics"]
        .as_array()
        .expect("diagnostics array")
        .iter()
        .filter_map(|diagnostic| diagnostic["message"].as_str())
        .collect();

    let _ = std::fs::remove_dir_all(&root);

    assert!(
        messages
            .iter()
            .any(|message| message.contains("impl for undefined trait: PgType")),
        "expected undefined trait diagnostic, got {messages:?}"
    );
}

#[test]
fn diagnostics_do_not_treat_warmed_dependency_as_bare_trait_scope() {
    let root = temp_project("dependency-warmed-trait-scope-diagnostic");
    let dep_root = root.join("deps/kraken");
    let dep_src = dep_root.join("src/Kraken");
    let main_path = root.join("src/Main.saga");
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
        dep_src.join("Core.saga"),
        "\
module Kraken.Core

pub trait PgType a {}
",
    )
    .expect("write dependency module");

    let main_source = "\
module Main

pub record Sesh {
  id: Int
}

impl PgType for Sesh {}
";
    std::fs::write(&main_path, main_source).expect("write main module");

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
    let messages: Vec<_> = params["diagnostics"]
        .as_array()
        .expect("diagnostics array")
        .iter()
        .filter_map(|diagnostic| diagnostic["message"].as_str())
        .collect();

    let _ = std::fs::remove_dir_all(&root);

    assert!(
        messages
            .iter()
            .any(|message| message.contains("impl for undefined trait: PgType")),
        "expected warmed dependency not to expose bare trait, got {messages:?}"
    );
}

#[test]
fn dependency_import_exposing_completion_uses_warmed_exports() {
    let root = temp_project("dependency-import-exposing-completion");
    let dep_root = root.join("deps/kraken");
    let dep_src = dep_root.join("src/Kraken");
    let main_path = root.join("src/Main.saga");
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
        dep_src.join("Core.saga"),
        "\
module Kraken.Core

pub type ColumnSet = ColumnSet
",
    )
    .expect("write dependency module");

    let main_source = "\
module Main

import Kraken.Core (C
";
    std::fs::write(&main_path, main_source).expect("write main module");

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
    let _ = wait_for_diagnostics(&lsp, &uri, 1, 1);
    let labels = completion_labels(&mut lsp, &uri, 2, 21);

    let _ = std::fs::remove_dir_all(&root);

    assert!(
        labels.iter().any(|label| label == "ColumnSet"),
        "missing dependency import exposing completion: {labels:?}"
    );
}

#[test]
fn diagnostics_preserve_trait_defaults_through_barrel_reexport() {
    let root = temp_project("barrel-reexport-trait-default-diagnostic");
    let dep_root = root.join("deps/kraken");
    let dep_src = dep_root.join("src/Kraken");
    let main_path = root.join("src/Schema.saga");
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
expose = [\"Kraken.Db\", \"Kraken.Core\"]
",
    )
    .expect("write dependency project.toml");
    std::fs::write(
        dep_src.join("Core.saga"),
        "\
module Kraken.Core

pub trait ColumnSet cols {
  fun columns : String -> cols
  fun column_names : cols -> List (String, String)
  column_names _cols = []
}
",
    )
    .expect("write core module");
    std::fs::write(
        dep_src.join("Db.saga"),
        "\
module Kraken.Db

import Kraken.Core (pub ..)
",
    )
    .expect("write db barrel module");

    let source = "\
module Schema

import Kraken.Db (ColumnSet)

pub record Users {
  id: String
}

impl ColumnSet for Users {
  columns source = Users { id: source }
}
";
    std::fs::write(&main_path, source).expect("write schema module");

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
                "text": source
            }
        }),
    );
    let params = wait_for_diagnostics(&lsp, &uri, 1, 2);
    let errors: Vec<_> = params["diagnostics"]
        .as_array()
        .expect("diagnostics array")
        .iter()
        .filter(|diagnostic| diagnostic["severity"].as_i64() == Some(1))
        .filter_map(|diagnostic| diagnostic["message"].as_str())
        .collect();

    let _ = std::fs::remove_dir_all(&root);

    assert!(
        errors.is_empty(),
        "barrel re-exported trait default should satisfy omitted method, got {errors:?}"
    );
}

#[test]
fn diagnostics_accept_barrel_reexported_trait_impl_constraint() {
    let root = temp_project("barrel-reexported-trait-impl-diagnostic");
    let dep_root = root.join("deps/kraken");
    let dep_src = dep_root.join("src/Kraken");
    let main_path = root.join("src/Main.saga");
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
expose = [\"Kraken.Db\"]
",
    )
    .expect("write dependency project.toml");
    std::fs::write(
        dep_src.join("Query.saga"),
        "\
module Kraken.Query

pub type DbError = DbError deriving (Debug)

pub fun insert : Unit -> Result Unit DbError
insert () = Err DbError
",
    )
    .expect("write dependency query module");
    std::fs::write(
        dep_src.join("Db.saga"),
        "\
module Kraken.Db
import Kraken.Query (pub DbError, insert)

pub fun insert : Unit -> Result Unit DbError
insert () = Kraken.Query.insert ()
",
    )
    .expect("write dependency db module");

    let main_source = r#"
module Main

import Kraken.Db

fun render : Unit -> Unit
render () = case Kraken.Db.insert () {
  Ok _ -> ()
  Err e -> panic $"insert_records failed: {debug e}"
}
"#;
    std::fs::write(&main_path, main_source).expect("write main module");

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
    let errors = params["diagnostics"]
        .as_array()
        .expect("diagnostics array")
        .iter()
        .filter(|diagnostic| diagnostic["severity"].as_i64() == Some(1))
        .collect::<Vec<_>>();

    let _ = std::fs::remove_dir_all(&root);

    assert!(
        errors.is_empty(),
        "expected no LSP errors for barrel-reexported Debug impl, got {errors:?}"
    );
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
fn rename_uses_semantic_identity_and_skips_shadowed_locals() {
    let mut lsp = LspHarness::start();
    lsp.initialize();
    let uri = saga_uri("rename-shadowed");
    let source = "\
module Main

fun pick : Int -> Int
pick value = {
  let inner = (fun value -> value) 2
  value + inner
}
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
    let params = wait_for_diagnostics(&lsp, &saga_uri("rename-shadowed"), 1, 2);
    assert_eq!(
        params["diagnostics"].as_array().map(Vec::len),
        Some(0),
        "fixture must typecheck before rename request, got {params:?}"
    );

    let rename_id = lsp.send_request(
        "textDocument/rename",
        json!({
            "textDocument": {
                "uri": saga_uri("rename-shadowed")
            },
            "position": {
                "line": 3,
                "character": 5
            },
            "newName": "outer_value"
        }),
    );
    let result = lsp
        .recv_until(Duration::from_secs(5), |message| {
            message.get("id").and_then(Value::as_i64) == Some(rename_id)
        })
        .expect("rename response");

    let edits = result["result"]["changes"][saga_uri("rename-shadowed").as_str()]
        .as_array()
        .expect("rename edits for file");
    let edited_lines: Vec<_> = edits
        .iter()
        .map(|edit| edit["range"]["start"]["line"].as_u64().expect("line"))
        .collect();
    assert_eq!(
        edited_lines,
        vec![3, 5],
        "rename should touch only the outer binding and use: {result:?}"
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
fn goto_definition_on_import_uses_module_file_index() {
    let root = temp_project("module-import-definition");
    let helper_path = root.join("src/Helper.saga");
    let main_path = root.join("src/Main.saga");

    std::fs::write(
        &helper_path,
        "\
module Helper

pub fun answer : Unit -> Int
answer () = 42
",
    )
    .expect("write helper module");

    let main_source = "\
module Main

import Helper

fun main : Unit -> Int
main () = Helper.answer ()
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

        let definition_id = lsp.send_request(
            "textDocument/definition",
            json!({
                "textDocument": {
                    "uri": file_uri(&main_path)
                },
                "position": {
                    "line": 2,
                    "character": 8
                }
            }),
        );
        lsp.recv_until(Duration::from_secs(5), |message| {
            message.get("id").and_then(Value::as_i64) == Some(definition_id)
        })
        .expect("definition response")
    };

    let _ = std::fs::remove_dir_all(&root);

    assert_eq!(
        result["result"]["uri"].as_str(),
        Some(file_uri(&helper_path).as_str()),
        "expected module import to jump to module file: {result:?}"
    );
    assert_eq!(
        result["result"]["range"]["start"]["line"].as_u64(),
        Some(0),
        "expected module declaration range: {result:?}"
    );
}

#[test]
fn hover_uses_docs_by_semantic_type_key() {
    let root = temp_project("semantic-doc-hover");
    let types_path = root.join("src/Types.saga");
    let main_path = root.join("src/Main.saga");

    std::fs::write(
        &types_path,
        "\
module Types

#@ Board docs from the defining module.
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
            "fixture must typecheck before hover request, got {params:?}"
        );

        let hover_id = lsp.send_request(
            "textDocument/hover",
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
        lsp.recv_until(Duration::from_secs(5), |message| {
            message.get("id").and_then(Value::as_i64) == Some(hover_id)
        })
        .expect("hover response")
    };

    let _ = std::fs::remove_dir_all(&root);

    let value = result["result"]["contents"]["value"]
        .as_str()
        .expect("hover markdown value");
    assert!(
        value.contains("Board docs from the defining module."),
        "expected semantic-key docs hover: {result:?}"
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
fn semantic_symbol_references_include_importing_modules() {
    let root = temp_project("project-semantic-symbol-references");
    let lib_path = root.join("src/Lib.saga");
    let main_path = root.join("src/Main.saga");

    let lib_source = "\
module Lib

pub trait Label a {
  fun label : a -> String
}

pub effect Log {
  fun write : String -> Unit
}

pub handler ignore for Log {
  write _ = resume ()
}
";
    std::fs::write(&lib_path, lib_source).expect("write lib module");

    let main_source = "\
module Main

import Lib (Label, Log, ignore)

impl Label for Int {
  label _ = \"n\"
}

fun use_label : Int -> String
use_label n = n |> label

fun use_log : Unit -> Unit needs {Log}
use_log () = write! \"x\"

fun run : Unit -> Unit
run () = use_log () with ignore
";
    std::fs::write(&main_path, main_source).expect("write main module");

    let result = {
        let mut lsp = LspHarness::start();
        lsp.initialize();
        let main_uri = file_uri(&main_path);
        let lib_uri = file_uri(&lib_path);

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

        let label_method_definition_before_lib_open_id = lsp.send_request(
            "textDocument/definition",
            json!({
                "textDocument": {
                    "uri": file_uri(&main_path)
                },
                "position": {
                    "line": 9,
                    "character": 20
                }
            }),
        );
        let label_method_definition_before_lib_open = lsp
            .recv_until(Duration::from_secs(5), |message| {
                message.get("id").and_then(Value::as_i64)
                    == Some(label_method_definition_before_lib_open_id)
            })
            .expect("trait method definition response before lib open");

        let label_impl_hover_id = lsp.send_request(
            "textDocument/hover",
            json!({
                "textDocument": {
                    "uri": file_uri(&main_path)
                },
                "position": {
                    "line": 5,
                    "character": 3
                }
            }),
        );
        let label_impl_hover = lsp
            .recv_until(Duration::from_secs(5), |message| {
                message.get("id").and_then(Value::as_i64) == Some(label_impl_hover_id)
            })
            .expect("trait impl method hover response");

        lsp.send_notification(
            "textDocument/didOpen",
            json!({
                "textDocument": {
                    "uri": lib_uri,
                    "languageId": "saga",
                    "version": 1,
                    "text": lib_source
                }
            }),
        );
        let lib_params = wait_for_diagnostics(&lsp, &lib_uri, 1, 2);
        assert_eq!(
            lib_params["diagnostics"].as_array().map(Vec::len),
            Some(0),
            "lib fixture must typecheck before references request, got {lib_params:?}"
        );

        let label_id = lsp.send_request(
            "textDocument/references",
            json!({
                "textDocument": {
                    "uri": file_uri(&lib_path)
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
        let label_refs = lsp
            .recv_until(Duration::from_secs(5), |message| {
                message.get("id").and_then(Value::as_i64) == Some(label_id)
            })
            .expect("trait references response");

        let log_id = lsp.send_request(
            "textDocument/references",
            json!({
                "textDocument": {
                    "uri": file_uri(&lib_path)
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
        let log_refs = lsp
            .recv_until(Duration::from_secs(5), |message| {
                message.get("id").and_then(Value::as_i64) == Some(log_id)
            })
            .expect("effect references response");

        let label_method_definition_id = lsp.send_request(
            "textDocument/definition",
            json!({
                "textDocument": {
                    "uri": file_uri(&main_path)
                },
                "position": {
                    "line": 9,
                    "character": 20
                }
            }),
        );
        let label_method_definition = lsp
            .recv_until(Duration::from_secs(5), |message| {
                message.get("id").and_then(Value::as_i64) == Some(label_method_definition_id)
            })
            .expect("trait method definition response");

        let label_method_refs_id = lsp.send_request(
            "textDocument/references",
            json!({
                "textDocument": {
                    "uri": file_uri(&lib_path)
                },
                "position": {
                    "line": 3,
                    "character": 7
                },
                "context": {
                    "includeDeclaration": true
                }
            }),
        );
        let label_method_refs = lsp
            .recv_until(Duration::from_secs(5), |message| {
                message.get("id").and_then(Value::as_i64) == Some(label_method_refs_id)
            })
            .expect("trait method references response");

        let label_method_hover_id = lsp.send_request(
            "textDocument/hover",
            json!({
                "textDocument": {
                    "uri": file_uri(&main_path)
                },
                "position": {
                    "line": 9,
                    "character": 20
                }
            }),
        );
        let label_method_hover = lsp
            .recv_until(Duration::from_secs(5), |message| {
                message.get("id").and_then(Value::as_i64) == Some(label_method_hover_id)
            })
            .expect("trait method hover response");

        let write_definition_id = lsp.send_request(
            "textDocument/definition",
            json!({
                "textDocument": {
                    "uri": file_uri(&main_path)
                },
                "position": {
                    "line": 12,
                    "character": 15
                }
            }),
        );
        let write_definition = lsp
            .recv_until(Duration::from_secs(5), |message| {
                message.get("id").and_then(Value::as_i64) == Some(write_definition_id)
            })
            .expect("effect operation definition response");

        let write_refs_id = lsp.send_request(
            "textDocument/references",
            json!({
                "textDocument": {
                    "uri": file_uri(&lib_path)
                },
                "position": {
                    "line": 7,
                    "character": 7
                },
                "context": {
                    "includeDeclaration": true
                }
            }),
        );
        let write_refs = lsp
            .recv_until(Duration::from_secs(5), |message| {
                message.get("id").and_then(Value::as_i64) == Some(write_refs_id)
            })
            .expect("effect operation references response");

        let write_hover_id = lsp.send_request(
            "textDocument/hover",
            json!({
                "textDocument": {
                    "uri": file_uri(&main_path)
                },
                "position": {
                    "line": 12,
                    "character": 15
                }
            }),
        );
        let write_hover = lsp
            .recv_until(Duration::from_secs(5), |message| {
                message.get("id").and_then(Value::as_i64) == Some(write_hover_id)
            })
            .expect("effect operation hover response");

        let ignore_id = lsp.send_request(
            "textDocument/references",
            json!({
                "textDocument": {
                    "uri": file_uri(&lib_path)
                },
                "position": {
                    "line": 10,
                    "character": 12
                },
                "context": {
                    "includeDeclaration": true
                }
            }),
        );
        let ignore_refs = lsp
            .recv_until(Duration::from_secs(5), |message| {
                message.get("id").and_then(Value::as_i64) == Some(ignore_id)
            })
            .expect("handler references response");

        (
            label_refs,
            log_refs,
            label_method_definition_before_lib_open,
            label_impl_hover,
            label_method_definition,
            label_method_refs,
            label_method_hover,
            write_definition,
            write_refs,
            write_hover,
            ignore_refs,
        )
    };

    let _ = std::fs::remove_dir_all(&root);

    let (
        label_refs,
        log_refs,
        label_method_definition_before_lib_open,
        label_impl_hover,
        label_method_definition,
        label_method_refs,
        label_method_hover,
        write_definition,
        write_refs,
        write_hover,
        ignore_refs,
    ) = result;
    let label_refs = label_refs["result"]
        .as_array()
        .expect("trait references result array");
    assert!(
        label_refs.iter().any(|location| {
            location["uri"].as_str() == Some(file_uri(&lib_path).as_str())
                && location["range"]["start"]["line"].as_u64() == Some(2)
        }),
        "expected trait declaration location: {label_refs:?}"
    );
    assert!(
        label_refs.iter().any(|location| {
            location["uri"].as_str() == Some(file_uri(&main_path).as_str())
                && location["range"]["start"]["line"].as_u64() == Some(4)
        }),
        "expected importing module trait impl reference: {label_refs:?}"
    );

    let log_refs = log_refs["result"]
        .as_array()
        .expect("effect references result array");
    assert!(
        log_refs.iter().any(|location| {
            location["uri"].as_str() == Some(file_uri(&lib_path).as_str())
                && location["range"]["start"]["line"].as_u64() == Some(6)
        }),
        "expected effect declaration location: {log_refs:?}"
    );
    assert!(
        log_refs.iter().any(|location| {
            location["uri"].as_str() == Some(file_uri(&main_path).as_str())
                && location["range"]["start"]["line"].as_u64() == Some(11)
        }),
        "expected importing module effect reference: {log_refs:?}"
    );

    assert_eq!(
        label_method_definition_before_lib_open["result"]["uri"].as_str(),
        Some(file_uri(&lib_path).as_str()),
        "expected trait method definition before opening defining module: {label_method_definition_before_lib_open:?}"
    );
    assert_eq!(
        label_method_definition_before_lib_open["result"]["range"]["start"]["line"].as_u64(),
        Some(3),
        "expected trait method name span before opening defining module: {label_method_definition_before_lib_open:?}"
    );
    assert!(
        label_impl_hover["result"]["contents"]["value"]
            .as_str()
            .is_some_and(|value| value.contains("Label.label : a -> String")),
        "expected impl method hover signature: {label_impl_hover:?}"
    );

    assert_eq!(
        label_method_definition["result"]["uri"].as_str(),
        Some(file_uri(&lib_path).as_str()),
        "expected trait method definition: {label_method_definition:?}"
    );
    assert_eq!(
        label_method_definition["result"]["range"]["start"]["line"].as_u64(),
        Some(3),
        "expected trait method name span: {label_method_definition:?}"
    );

    let label_method_refs = label_method_refs["result"]
        .as_array()
        .expect("trait method references result array");
    assert!(
        label_method_refs.iter().any(|location| {
            location["uri"].as_str() == Some(file_uri(&lib_path).as_str())
                && location["range"]["start"]["line"].as_u64() == Some(3)
        }),
        "expected trait method declaration location: {label_method_refs:?}"
    );
    assert!(
        label_method_refs.iter().any(|location| {
            location["uri"].as_str() == Some(file_uri(&main_path).as_str())
                && location["range"]["start"]["line"].as_u64() == Some(5)
        }),
        "expected impl method reference: {label_method_refs:?}"
    );
    assert!(
        label_method_refs.iter().any(|location| {
            location["uri"].as_str() == Some(file_uri(&main_path).as_str())
                && location["range"]["start"]["line"].as_u64() == Some(9)
        }),
        "expected trait method call reference: {label_method_refs:?}"
    );
    assert!(
        label_method_hover["result"]["contents"]["value"]
            .as_str()
            .is_some_and(|value| value.contains("Label.label : a -> String")),
        "expected trait method hover signature: {label_method_hover:?}"
    );

    assert_eq!(
        write_definition["result"]["uri"].as_str(),
        Some(file_uri(&lib_path).as_str()),
        "expected effect operation definition: {write_definition:?}"
    );
    assert_eq!(
        write_definition["result"]["range"]["start"]["line"].as_u64(),
        Some(7),
        "expected effect operation name span: {write_definition:?}"
    );

    let write_refs = write_refs["result"]
        .as_array()
        .expect("effect operation references result array");
    assert!(
        write_refs.iter().any(|location| {
            location["uri"].as_str() == Some(file_uri(&lib_path).as_str())
                && location["range"]["start"]["line"].as_u64() == Some(7)
        }),
        "expected effect operation declaration location: {write_refs:?}"
    );
    assert!(
        write_refs.iter().any(|location| {
            location["uri"].as_str() == Some(file_uri(&lib_path).as_str())
                && location["range"]["start"]["line"].as_u64() == Some(11)
        }),
        "expected handler arm operation reference: {write_refs:?}"
    );
    assert!(
        write_refs.iter().any(|location| {
            location["uri"].as_str() == Some(file_uri(&main_path).as_str())
                && location["range"]["start"]["line"].as_u64() == Some(12)
        }),
        "expected effect operation call reference: {write_refs:?}"
    );
    assert!(
        write_hover["result"]["contents"]["value"]
            .as_str()
            .is_some_and(|value| value.contains("Log.write : String -> Unit")),
        "expected effect operation hover signature: {write_hover:?}"
    );

    let ignore_refs = ignore_refs["result"]
        .as_array()
        .expect("handler references result array");
    assert!(
        ignore_refs.iter().any(|location| {
            location["uri"].as_str() == Some(file_uri(&lib_path).as_str())
                && location["range"]["start"]["line"].as_u64() == Some(10)
        }),
        "expected handler declaration location: {ignore_refs:?}"
    );
    assert!(
        ignore_refs.iter().any(|location| {
            location["uri"].as_str() == Some(file_uri(&main_path).as_str())
                && location["range"]["start"]["line"].as_u64() == Some(15)
        }),
        "expected importing module handler reference: {ignore_refs:?}"
    );
}

#[test]
fn hover_trait_method_signature_uses_trait_definition_shape() {
    let mut lsp = LspHarness::start();
    lsp.initialize();
    let uri = saga_uri("trait-method-hover-shape");
    let source = "\
module Main

pub trait Describe a {
  fun describe_it : a -> String
}

pub record Person {
  name: String
}

impl Describe for Person {
  describe_it p = $\"Name is: {p.name}\"
}
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
    let params = wait_for_diagnostics(&lsp, &saga_uri("trait-method-hover-shape"), 1, 2);
    assert_eq!(
        params["diagnostics"].as_array().map(Vec::len),
        Some(0),
        "fixture must typecheck before hover request, got {params:?}"
    );

    let hover_id = lsp.send_request(
        "textDocument/hover",
        json!({
            "textDocument": {
                "uri": saga_uri("trait-method-hover-shape")
            },
            "position": {
                "line": 11,
                "character": 4
            }
        }),
    );
    let hover = lsp
        .recv_until(Duration::from_secs(5), |message| {
            message.get("id").and_then(Value::as_i64) == Some(hover_id)
        })
        .expect("hover response");

    assert!(
        hover["result"]["contents"]["value"]
            .as_str()
            .is_some_and(|value| value.contains("Describe.describe_it : a -> String")),
        "expected trait method hover to use trait method shape: {hover:?}"
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
fn watched_created_module_rechecks_open_importers_without_restart() {
    let root = temp_project("watched-module-map-refresh");
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
            "workspace/didChangeWatchedFiles",
            json!({
                "changes": [{
                    "uri": file_uri(&helper_path),
                    "type": 1
                }]
            }),
        );

        lsp.recv_until(Duration::from_secs(5), |message| {
            diagnostics_for_uri(message, &file_uri(&main_path)).is_some_and(|params| {
                params["version"].as_i64() == Some(1)
                    && params["diagnostics"].as_array().map(Vec::len) == Some(0)
            })
        })
        .expect("diagnostics to clear after watched file creation")
    };

    let _ = std::fs::remove_dir_all(&root);
    assert!(publish_diagnostics(&result).is_some());
}

#[test]
fn watched_deleted_module_invalidates_cached_import_without_restart() {
    let root = temp_project("watched-module-delete");
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
        wait_for_diagnostics(&lsp, &file_uri(&main_path), 1, 2);

        std::fs::remove_file(&helper_path).expect("delete helper module");
        lsp.send_notification(
            "workspace/didChangeWatchedFiles",
            json!({
                "changes": [{
                    "uri": file_uri(&helper_path),
                    "type": 3
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
        .expect("diagnostics after watched file deletion")
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
