use std::collections::HashMap;
use std::path::PathBuf;

use saga::{derive, desugar, lexer, parser, typechecker};

use super::analysis::{collect_module_interface_updates, module_interface_fingerprint};
use super::analysis_pipeline::{
    analyze_document, checker_base_for_project, prepare_checker_for_analysis,
};
use super::*;

fn uri() -> Url {
    Url::parse("file:///tmp/main.saga").unwrap()
}

fn valid_source() -> String {
    "module Main\n\nfun main : Unit -> Unit\nmain () = ()\n".to_string()
}

fn temp_project(name: &str) -> PathBuf {
    let unique = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .expect("clock before epoch")
        .as_nanos();
    let root = std::env::temp_dir().join(format!(
        "saga-lsp-unit-{name}-{}-{unique}",
        std::process::id()
    ));
    std::fs::create_dir_all(root.join("src")).expect("create temp project src");
    std::fs::write(root.join("project.toml"), "").expect("write project.toml");
    root
}

fn interface_update(module_name: &str, interface_fingerprint: u64) -> ModuleInterfaceUpdate {
    ModuleInterfaceUpdate {
        module_name: module_name.to_string(),
        path: Some(PathBuf::from(format!("/tmp/{module_name}.saga"))),
        source_fingerprint: 1,
        interface_fingerprint,
        exports: std::sync::Arc::new(typechecker::ModuleExports::default()),
        codegen_info: None,
        check_result: None,
        next_var: 0,
        is_current: true,
    }
}

#[test]
fn project_interface_apply_detects_current_interface_changes() {
    let mut store = ProjectSemanticStore::default();
    let root = Some(PathBuf::from("/tmp/project"));

    let first =
        store.apply_module_interface_updates(root.clone(), vec![interface_update("Helper", 10)]);
    assert!(first.saw_current);
    assert!(first.current_changed);

    let unchanged =
        store.apply_module_interface_updates(root.clone(), vec![interface_update("Helper", 10)]);
    assert!(unchanged.saw_current);
    assert!(!unchanged.current_changed);

    let changed = store.apply_module_interface_updates(root, vec![interface_update("Helper", 11)]);
    assert!(changed.saw_current);
    assert!(changed.current_changed);
}

#[test]
fn parse_failure_preserves_previous_parse_snapshot() {
    let shared = SharedState::default();
    let uri = uri();

    store_document(&shared, uri.clone(), 1, valid_source(), false);
    let applied = apply_parse_result(
        &shared,
        &uri,
        analyze_document(&shared, Some(&uri), 1, &valid_source(), None),
    )
    .expect("apply valid parse");
    assert!(applied.diagnostics.is_empty());

    store_document(
        &shared,
        uri.clone(),
        2,
        "module Main\n\nfun main : Unit -> Unit\nmain () = ".to_string(),
        true,
    );
    let applied = apply_parse_result(
        &shared,
        &uri,
        analyze_document(
            &shared,
            Some(&uri),
            2,
            "module Main\n\nfun main : Unit -> Unit\nmain () = ",
            None,
        ),
    )
    .expect("apply invalid parse");
    assert!(!applied.diagnostics.is_empty());

    let document = current_document(&shared, &uri).expect("document");
    let parse = document.parse.expect("previous parse is preserved");
    assert_eq!(parse.version, 1);
    assert_eq!(document.diagnostics.len(), 1);
}

#[test]
fn stale_parse_result_is_discarded() {
    let shared = SharedState::default();
    let uri = uri();

    store_document(&shared, uri.clone(), 2, valid_source(), false);
    let result = apply_parse_result(
        &shared,
        &uri,
        analyze_document(&shared, Some(&uri), 1, &valid_source(), None),
    );

    assert!(result.is_none());
    let document = current_document(&shared, &uri).expect("document");
    assert!(document.parse.is_none());
    assert!(document.diagnostics.is_empty());
}

#[test]
fn utf16_position_to_offset_handles_multibyte_text() {
    let source = "module Main\n\nlet smile = \"🙂\"\n";
    let index = LineIndex::new(source);
    let offset = index.position_to_offset(Position::new(2, 12), source);

    assert_eq!(&source[offset..offset + 1], "\"");
}

#[test]
fn completion_uses_preserved_parse_snapshot_on_broken_text() {
    let shared = SharedState::default();
    let uri = uri();

    store_document(&shared, uri.clone(), 1, valid_source(), false);
    apply_parse_result(
        &shared,
        &uri,
        analyze_document(&shared, Some(&uri), 1, &valid_source(), None),
    )
    .expect("apply valid parse");
    store_document(
        &shared,
        uri.clone(),
        2,
        "module Main\n\nm".to_string(),
        true,
    );

    let document = current_document(&shared, &uri).expect("document");
    let labels: Vec<_> = collect_completion_items(&document, Position::new(2, 1), None)
        .into_iter()
        .map(|item| item.label)
        .collect();

    assert!(labels.iter().any(|label| label == "main"));
    assert!(labels.iter().any(|label| label == "module"));
}

#[test]
fn hover_reads_exact_version_semantic_snapshot() {
    let source = "\
module Main

fun id : Unit -> Unit
id x = x

fun main : Unit -> Unit
main () = id ()
";
    let uri = uri();
    let shared = SharedState::default();
    let result = analyze_document(&shared, Some(&uri), 1, source, None);
    let semantic = result.semantic.expect("semantic snapshot");
    let hover = hover_type_at(&uri, &semantic, Position::new(6, 10), None).expect("hover");
    let HoverContents::Markup(markup) = hover.contents else {
        panic!("expected markup hover");
    };

    assert!(
        markup.value.contains("id: Unit -> Unit"),
        "{}",
        markup.value
    );
}

#[test]
fn local_definition_uses_semantic_references() {
    let uri = uri();
    let source = "\
module Main

fun id : Unit -> Unit
id x = x

fun main : Unit -> Unit
main () = id ()
";
    let shared = SharedState::default();
    let result = analyze_document(&shared, Some(&uri), 1, source, None);
    let semantic = result.semantic.expect("semantic snapshot");
    let location = local_definition_at(&uri, &semantic, Position::new(6, 10)).expect("definition");

    assert_eq!(location.uri, uri);
    assert!(
        location.range.start.line == 2 || location.range.start.line == 3,
        "unexpected definition line: {:?}",
        location.range
    );
}

#[test]
fn semantic_index_groups_references_by_definition_identity() {
    let uri = uri();
    let source = "\
module Main

fun id : Unit -> Unit
id x = x

fun main : Unit -> Unit
main () = id (id ())
";
    let shared = SharedState::default();
    let result = analyze_document(&shared, Some(&uri), 1, source, None);
    let semantic = result.semantic.expect("semantic snapshot");

    let outer_offset = source.find("id (").expect("outer id") + 1;
    let inner_offset = source.rfind("id ()").expect("inner id") + 1;
    let outer_position = semantic.line_index.offset_to_position(outer_offset, source);
    let inner_position = semantic.line_index.offset_to_position(inner_offset, source);

    let outer_refs = references_at(&uri, &semantic, outer_position, true);
    let inner_refs = references_at(&uri, &semantic, inner_position, true);

    assert_eq!(outer_refs, inner_refs);
    assert!(
        outer_refs.len() >= 3,
        "expected declaration and both call sites, got {outer_refs:?}"
    );
    assert!(
        outer_refs
            .iter()
            .any(|location| location.range.start.line == 2 || location.range.start.line == 3),
        "expected declaration location, got {outer_refs:?}"
    );
    assert!(
        outer_refs
            .iter()
            .filter(|location| location.range.start.line == 6)
            .count()
            >= 2,
        "expected both call sites, got {outer_refs:?}"
    );

    let usage_refs = references_at(&uri, &semantic, outer_position, false);
    assert!(
        usage_refs
            .iter()
            .filter(|location| location.range.start.line == 6)
            .count()
            >= 2,
        "expected both call sites without requiring declarations: {usage_refs:?}"
    );
    assert!(
        usage_refs
            .iter()
            .all(|location| location.range.start.line != 2 && location.range.start.line != 3),
        "declarations should be omitted when include_declaration is false: {usage_refs:?}"
    );
}

#[test]
fn semantic_index_keeps_shadowed_local_references_separate() {
    let uri = uri();
    let source = "\
module Main

fun main : Unit -> Int
main () = {
  let x = 1
  let y = {
    let x = 2
    x
  }
  x
}
";
    let shared = SharedState::default();
    let result = analyze_document(&shared, Some(&uri), 1, source, None);
    let semantic = result.semantic.expect("semantic snapshot");

    let inner_offset = source.find("    x\n").expect("inner x") + 4;
    let outer_offset = source.rfind("  x\n").expect("outer x") + 2;
    let inner_position = semantic.line_index.offset_to_position(inner_offset, source);
    let outer_position = semantic.line_index.offset_to_position(outer_offset, source);

    let inner_refs = references_at(&uri, &semantic, inner_position, false);
    let outer_refs = references_at(&uri, &semantic, outer_position, false);

    assert_ne!(inner_refs, outer_refs);
    assert_eq!(inner_refs.len(), 1, "inner references: {inner_refs:?}");
    assert_eq!(outer_refs.len(), 1, "outer references: {outer_refs:?}");
    assert_eq!(inner_refs[0].range.start.line, 7);
    assert_eq!(outer_refs[0].range.start.line, 9);
}

#[test]
fn semantic_index_resolves_type_names_before_value_fallback() {
    let uri = uri();
    let source = "\
module Main

type SeshType =
  | Spot
  | Downwinder

type BoardType =
  | Twintip
  | Hydrofoil

record Normalized {
  sesh_type: SeshType,
  board_type: BoardType,
}

fun parse_board_type : String -> BoardType
parse_board_type s = Twintip

fun from_row : Unit -> Normalized
from_row () = Normalized {
  sesh_type: Downwinder,
  board_type: Twintip,
}
";
    let shared = SharedState::default();
    let result = analyze_document(&shared, Some(&uri), 1, source, None);
    let semantic = result.semantic.expect("semantic snapshot");

    let sesh_usage = source
        .find("sesh_type: SeshType")
        .expect("SeshType field usage")
        + "sesh_type: ".len();
    let sesh_location = local_definition_at(
        &uri,
        &semantic,
        semantic.line_index.offset_to_position(sesh_usage, source),
    )
    .expect("SeshType definition");
    assert_eq!(sesh_location.range.start.line, 2);

    let board_usage = source
        .find("board_type: BoardType")
        .expect("BoardType field usage")
        + "board_type: ".len();
    let board_location = local_definition_at(
        &uri,
        &semantic,
        semantic.line_index.offset_to_position(board_usage, source),
    )
    .expect("BoardType definition");
    assert_eq!(board_location.range.start.line, 6);

    let normalized_constructor = source
        .rfind("Normalized {")
        .expect("Normalized constructor");
    let normalized_location = local_definition_at(
        &uri,
        &semantic,
        semantic
            .line_index
            .offset_to_position(normalized_constructor, source),
    )
    .expect("Normalized definition");
    assert_eq!(normalized_location.range.start.line, 10);

    let board_definition = source.find("BoardType\n").expect("BoardType definition");
    let board_refs = references_at(
        &uri,
        &semantic,
        semantic
            .line_index
            .offset_to_position(board_definition, source),
        false,
    );
    assert!(
        board_refs
            .iter()
            .all(|location| location.range.start.line != 6),
        "definition should be omitted: {board_refs:?}"
    );
    assert!(
        board_refs
            .iter()
            .any(|location| location.range.start.line == 12),
        "expected record field type reference: {board_refs:?}"
    );
    assert!(
        board_refs
            .iter()
            .any(|location| location.range.start.line == 15),
        "expected function return type reference: {board_refs:?}"
    );
}

#[test]
fn project_base_checker_resolves_dependency_modules_without_warming_exports() {
    let root = temp_project("dependency-map-only");
    let dep_root = root.join("deps/kraken");
    let dep_src = dep_root.join("src");
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

pub fun answer : Unit -> Int
answer () = 42
",
    )
    .expect("write dependency module");

    let checker = checker_base_for_project(Some(root.clone())).expect("base checker");
    let result = checker.to_result();
    let _ = std::fs::remove_dir_all(&root);

    assert!(
        checker
            .module_map()
            .is_some_and(|module_map| module_map.contains_key("Kraken.Core")),
        "dependency module map was not resolved"
    );
    assert!(
        !result.module_exports().contains_key("Kraken.Core"),
        "dependency exports should not be warmed by the LSP base checker"
    );
}

#[test]
fn interface_updates_cache_builtin_modules_without_paths() {
    let mut checker = typechecker::Checker::with_prelude(None).expect("checker");
    checker
        .try_typecheck_import_by_name("Std.DateTime")
        .expect("typecheck builtin module");
    let result = checker.to_lsp_result();

    let updates = collect_module_interface_updates(
        None,
        &Vec::new(),
        &checker,
        &result,
        &HashMap::new(),
        &HashMap::new(),
        false,
    );
    let date_time = updates
        .iter()
        .find(|update| update.module_name == "Std.DateTime")
        .expect("Std.DateTime interface update");

    assert!(date_time.path.is_none());
    assert!(date_time.source_fingerprint != 0);
}

#[test]
fn cleared_lsp_base_can_recheck_builtin_importing_std_base() {
    let mut checker = typechecker::Checker::with_prelude(None).expect("checker");
    checker.clear_module_semantic_caches();

    checker
        .try_typecheck_import_by_name("Std.String")
        .expect("typecheck builtin module after cache clear");
}

#[test]
fn cleared_lsp_base_can_load_dependency_importing_std_base() {
    let root = temp_project("dependency-std-base-import");
    let dep_root = root.join("deps/kraken");
    let dep_src = dep_root.join("src");
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

import Std.Base (Semigroup)

pub fun answer : Unit -> Int
answer () = 42
",
    )
    .expect("write dependency module");

    let mut base = checker_base_for_project(Some(root.clone())).expect("base checker");
    base.clear_module_semantic_caches();
    let mut checker =
        prepare_checker_for_analysis(base, Some(root.clone()), HashMap::new(), HashMap::new());
    let source = "\
module Main

import Kraken.Core

fun main : Unit -> Int
main () = Kraken.Core.answer ()
";
    let tokens = lexer::Lexer::new(source).lex().expect("lex main");
    let mut program = parser::Parser::new(tokens)
        .parse_program()
        .expect("parse main");
    let imported = derive::collect_imported_decls_with_sources(
        &program,
        checker.module_map(),
        &HashMap::new(),
    );
    derive::expand_derives(&mut program, &imported);
    desugar::desugar_program(&mut program);
    let check = checker.check_program_lsp(&mut program);
    let errors: Vec<_> = check
        .diagnostics
        .iter()
        .filter(|diagnostic| matches!(diagnostic.severity, typechecker::Severity::Error))
        .collect();
    let _ = std::fs::remove_dir_all(&root);

    assert!(
        errors.is_empty(),
        "expected dependency module to typecheck, got: {errors:?}"
    );
}

#[test]
fn module_interface_fingerprint_uses_stable_projection() {
    let int_scheme = typechecker::Scheme {
        forall: Vec::new(),
        constraints: Vec::new(),
        ty: typechecker::Type::Con("Int".to_string(), Vec::new()),
    };
    let bool_scheme = typechecker::Scheme {
        forall: Vec::new(),
        constraints: Vec::new(),
        ty: typechecker::Type::Con("Bool".to_string(), Vec::new()),
    };

    let mut left = typechecker::ModuleExports {
        bindings: vec![
            ("two".to_string(), int_scheme.clone()),
            ("one".to_string(), int_scheme.clone()),
        ],
        ..Default::default()
    };
    left.binding_origins
        .insert("one".to_string(), "Example.one".to_string());
    left.binding_origins
        .insert("two".to_string(), "Example.two".to_string());
    left.type_arity.insert("Pair".to_string(), 2);
    left.type_arity.insert("Box".to_string(), 1);
    left.doc_comments.insert(
        "one".to_string(),
        vec!["docs do not force recheck".to_string()],
    );

    let mut right = typechecker::ModuleExports {
        bindings: vec![
            ("one".to_string(), int_scheme.clone()),
            ("two".to_string(), int_scheme),
        ],
        ..Default::default()
    };
    right
        .binding_origins
        .insert("two".to_string(), "Example.two".to_string());
    right
        .binding_origins
        .insert("one".to_string(), "Example.one".to_string());
    right.type_arity.insert("Box".to_string(), 1);
    right.type_arity.insert("Pair".to_string(), 2);
    right
        .doc_comments
        .insert("one".to_string(), vec!["different docs".to_string()]);

    assert_eq!(
        module_interface_fingerprint(&left),
        module_interface_fingerprint(&right)
    );

    right.bindings[0].1 = bool_scheme;
    assert_ne!(
        module_interface_fingerprint(&left),
        module_interface_fingerprint(&right)
    );
}

// Regression: re-harvesting a dependency module's interface (as happens when
// the editor edits that file repeatedly) pushes its var ids higher each time.
// Seeding those interfaces into the cached base checker must advance the
// checker's fresh-var counter past them; otherwise a consumer's fresh vars
// collide with seeded ones and share substitution entries, which silently pins
// a polymorphic function to its first use. Symptom: a polymorphic decoder
// wrapper reports "expected Json -> String, got Json -> Float" all over a file
// that compiles cleanly.
#[test]
fn seeded_module_interfaces_do_not_pin_consumer_polymorphism() {
    let root = temp_project("seed-var-collision");
    let lib_dir = root.join("lib");
    std::fs::create_dir_all(&lib_dir).expect("create lib dir");
    std::fs::write(
        root.join("project.toml"),
        "[project]\nname = \"app\"\n\n[library]\nmodule = \"Lib\"\nexpose = [\"Lib\"]\n",
    )
    .expect("write project.toml");

    let lib_path = lib_dir.join("Lib.saga");
    let lib_text = "\
module Lib

pub fun run : (Int -> a) -> a
run g = g 0

pub fun s : Int -> String
s n = \"x\"

pub fun f : Int -> Float
f n = 1.5

pub fun b : Int -> Bool
b n = True
";
    std::fs::write(&lib_path, lib_text).expect("write Lib.saga");
    let lib_uri = Url::from_file_path(&lib_path).unwrap();

    // Consumer wraps the dependency's polymorphic combinator, then uses it at
    // several concrete types — exactly the saga_json `decode dec j = run dec j`
    // shape that surfaced the bug.
    let main_path = root.join("src").join("Main.saga");
    let main_text = "\
module Main

import Lib

fun apply : (Int -> a) -> a
apply g = Lib.run g

pub fun go : Unit -> Unit
go () = {
  let _ = apply Lib.s
  let _ = apply Lib.f
  let _ = apply Lib.b
  ()
}

";
    std::fs::write(&main_path, main_text).expect("write Main.saga");
    let main_uri = Url::from_file_path(&main_path).unwrap();

    let shared = SharedState::default();
    let apply = |shared: &SharedState, res: ParseJobResult| {
        shared
            .projects
            .lock()
            .unwrap()
            .apply_module_interface_updates(Some(root.clone()), res.module_interfaces);
    };

    // Prime: analyze Main so Lib's interface is harvested and cached.
    apply(
        &shared,
        analyze_document(&shared, Some(&main_uri), 1, main_text, Some(root.clone())),
    );

    // Edit the dependency repeatedly, re-checking the consumer each round. The
    // var-id watermark of Lib's interface climbs with every edit.
    let mut last = Vec::new();
    for version in 2..=6 {
        let edited = format!("{lib_text}\n# edit {version}\n");
        apply(
            &shared,
            analyze_document(
                &shared,
                Some(&lib_uri),
                version,
                &edited,
                Some(root.clone()),
            ),
        );
        let res = analyze_document(
            &shared,
            Some(&main_uri),
            version,
            main_text,
            Some(root.clone()),
        );
        last = res.diagnostics.clone();
        apply(&shared, res);
    }

    let _ = std::fs::remove_dir_all(&root);

    let mismatches: Vec<_> = last
        .iter()
        .filter(|d| d.message.contains("type mismatch"))
        .collect();
    for d in &mismatches {
        eprintln!("DIAG: {}", d.message);
    }
    assert!(
        mismatches.is_empty(),
        "{} spurious type-mismatch diagnostics from seeded var-id collision",
        mismatches.len()
    );
}
