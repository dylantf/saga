# Incremental Multi-File Checking

## Problem

Currently each `check_file` call creates a fresh `Checker`, re-parses all imports from source,
and re-typechecks everything. The results are stored per-file in `HashMap<Url, CheckSnapshot>`.
When file A changes, files that import A don't get re-checked and their stale diagnostics persist.

## Goal

Cache parsed ASTs and check results at the project level. When a file changes, only re-check
that file and its reverse dependents. Reuse cached results for everything else.

## Current Flow

```
did_change(file_A)
  -> get_checker()          # clone base checker (prelude only)
  -> check(checker, source) # lex, parse, typecheck file_A
    -> check_program()
      -> for each import:
           read source from disk
           lex + parse
           typecheck
           store in CheckResult.modules
  -> store CheckSnapshot keyed by file_A's URI
  -> publish diagnostics for file_A only
```

## Proposed Flow

```
did_change(file_A)
  -> project.invalidate(file_A)           # mark A dirty, look up reverse deps
  -> project.invalidate_dependents(file_A) # mark B, C dirty if they import A
  -> for each dirty file (in dependency order):
       if parsed AST is stale: re-lex, re-parse, cache AST
       build checker with cached CheckResults for clean dependencies
       typecheck, cache new CheckResult
  -> publish diagnostics for all re-checked files
```

## Data Structures

### ProjectState (new, replaces `HashMap<Url, CheckSnapshot>`)

Lives on the Backend behind `Arc<Mutex<...>>`.

```rust
struct ProjectState {
    /// Module name -> file path (already exists as ModuleMap)
    module_map: HashMap<String, PathBuf>,

    /// Per-file cached state
    files: HashMap<Url, FileState>,

    /// Reverse dependency graph: module_name -> set of modules that import it.
    /// Built incrementally as files are checked.
    reverse_deps: HashMap<String, HashSet<String>>,

    /// Base checker (prelude + stdlib), shared across checks
    base_checker: Checker,
}

struct FileState {
    source: String,
    line_index: LineIndex,
    program: Option<Program>,     // cached parse result
    check_result: Option<CheckResult>,  // cached typecheck result
    dirty: bool,
}
```

### Dependency Tracking

When `check_program` processes `import Foo`, record that the current file depends on Foo.
This can be extracted from the existing module resolution in `check_module.rs` -- it already
builds a ModuleMap. The reverse map just needs to be maintained at the project level instead
of being rebuilt each time.

### Snapshot Access

`snapshot()` stays mostly the same but reads from `ProjectState.files` instead of a
flat HashMap. Still returns `Arc<...>` for lock-free reads by LSP handlers.

## Changes by File

### src/lsp/main.rs
- Replace `last_check: Mutex<HashMap<Url, CheckSnapshot>>` with `Mutex<ProjectState>`
- `check_file` becomes `check_and_propagate`: invalidates the file, determines what
  else needs re-checking via `reverse_deps`, re-checks in dependency order
- `did_change` publishes diagnostics for all affected files, not just the changed one

### src/typechecker/mod.rs (or check_module.rs)
- `Checker` needs a way to accept pre-checked module results. Something like
  `checker.set_module_result(name, check_result)` so it skips re-checking that import.
- The existing `modules.check_results` cache on CheckResult is the right shape,
  it just needs to be populated from the outside rather than built internally.

### src/lsp/diagnostics.rs
- `check()` accepts optional pre-checked module results to pass to the checker

## Migration

This is not a rewrite. The typechecker logic stays the same. The change is:
1. Pull cached state up from CheckResult into ProjectState
2. Add reverse_deps tracking (small addition to check_module.rs)
3. Change the LSP's check_file to iterate dirty files instead of checking one

## What This Doesn't Cover

- Incremental parsing (reusing unchanged parts of the AST) -- not needed yet
- Parallel checking of independent modules -- the DAG makes this possible later
  but sequential re-checking of only dirty files is the bigger win
- File watching for changes outside the editor -- `did_change` only fires for open files,
  changes to closed files on disk won't trigger re-checking until they're opened
