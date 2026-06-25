# LSP Rebuild Plan

Status: draft living plan

## Why This Exists

The current Saga LSP grew as a thin wrapper around the batch compiler. That
worked while the language was smaller, but the language now has enough semantic
surface area -- modules, traits, effects, handlers, richer name resolution,
records, derives, and cross-file metadata -- that the server feels brittle:
slow checks, stale results, disappearing editor features while typing, and
navigation/completion logic that often reconstructs identity from names instead
of consuming compiler resolution.

This plan assumes we should rebuild the LSP bones in a small, clean project
first, then copy over only the pieces that still make sense.

Related docs:

- `docs/roadmap-lsp.md` records feature coverage in the current LSP.
- `docs/planning/incremental-checking.md` sketches project-level checking.
- `docs/compiler-overview.md` explains the modern compiler outputs the LSP
  should consume, especially `CheckResult` and `ResolutionResult`.

## North Star

Build the LSP as an editor-facing semantic database, not as "run the compiler on
this file and scrape whatever falls out."

The server should maintain explicit project and document state:

- latest editor text by document version
- recoverable parse snapshots, even when the file has syntax errors
- module map and import graph
- semantic snapshots keyed by document/project generation
- indexed definitions, references, docs, and completion surfaces

Feature handlers should be fast reads from immutable snapshots. Slow work should
happen in scheduled jobs whose results are discarded if stale.

## Step 0: Start Fresh

Create a new small LSP project or crate that can run beside the existing server.
The first goal is not feature parity. The first goal is a sane control loop.

Suggested shape:

```text
new saga-lsp
  -> initialize
  -> did_open / did_change / did_close
  -> versioned document store
  -> scheduled parse/check jobs
  -> publish diagnostics only if result version is current
  -> answer hover/completion from the latest valid snapshots
```

Keep the existing LSP untouched at first. It is the reference implementation and
the salvage yard.

Chosen placement:

- new server: `src/lsp/`
- old server: `src/lsp_legacy/`

The normal `saga-lsp` binary points at the rebuild. The old implementation stays
buildable as `saga-lsp-legacy` while we port behavior across deliberately.

## Design Principles

1. Version everything that crosses an async boundary.
   A check result for document version 12 must never replace version 14.

2. Separate syntax from semantics.
   Parse snapshots can exist when typechecking cannot. Completion, document
   symbols, and cheap navigation should continue working during invalid code.

3. Query handlers should not typecheck.
   Hover, completion, definition, references, rename, and code actions should
   read snapshots or return partial answers. They should not synchronously read
   and check other project files.

4. Use compiler semantic identity.
   Prefer `ResolutionResult`, `references`, `node_spans`, type maps, and module
   metadata over AST name scans and `scope_map` guessing.

5. Keep compiler and editor contracts explicit.
   If LSP needs a stable definition index, expose or build one deliberately
   instead of deriving it ad hoc in each feature.

6. Build graceful degradation first.
   It is better to return a partial completion list quickly than to freeze while
   attempting perfect semantic answers.

## Proposed Architecture

```rust
struct Workspace {
    projects: HashMap<ProjectRoot, ProjectState>,
    loose_files: HashMap<Url, DocumentState>,
}

struct ProjectState {
    root: PathBuf,
    documents: HashMap<Url, DocumentState>,
    module_map: ModuleMap,
    import_graph: ImportGraph,
    base_semantics: BaseSemantics,
    semantic_index: SemanticIndex,
    generation: u64,
}

struct DocumentState {
    uri: Url,
    version: i32,
    text: Arc<str>,
    line_index: LineIndex,
    parse: Option<Arc<ParseSnapshot>>,
    semantics: Option<Arc<SemanticSnapshot>>,
    diagnostics: Vec<Diagnostic>,
}

struct ParseSnapshot {
    version: i32,
    program: Option<Program>,
    partial_items: Vec<SyntaxItem>,
    diagnostics: Vec<Diagnostic>,
}

struct SemanticSnapshot {
    version: i32,
    project_generation: u64,
    check: CheckResult,
    program: Program,
    diagnostics: Vec<Diagnostic>,
}
```

Names are illustrative. The important split is:

- `DocumentState` is current editor truth.
- `ParseSnapshot` is resilient and cheap.
- `SemanticSnapshot` is authoritative but may lag.
- `SemanticIndex` is project-level, precomputed, and read-only during queries.

## Migration Phases

### Phase 1: Minimal Sane Server

Goal: prove the new control loop.

- [x] Implement initialize/shutdown.
- [x] Implement full document sync first; incremental sync can come later.
- [x] Store document text and version immediately on open/change.
- [x] Debounce parse jobs.
- [x] Publish diagnostics only when the job result matches the current version.
- [x] Add tracing/logging around job start, job finish, stale discard, and publish.
- [x] Add a subprocess JSON-RPC protocol harness for the real `saga-lsp`
  binary.

Done when:

- rapid typing cannot publish stale diagnostics
- invalid syntax produces diagnostics without breaking the server
- no query handler does blocking check work

### Phase 2: Syntax Layer

Goal: editor remains useful while the file is broken.

- [x] Keep the latest successful full parse.
- Add a lightweight syntax snapshot for top-level declarations/imports/module
  names even when full parse fails, if practical.
- [x] Port document symbols from the old LSP, but make them syntax-only.
- Add syntax-position helpers used by completion/hover.
- [x] Add syntax fallback completion from current text plus the last good parse
  snapshot.

Done when:

- document symbols still work for most partially typed files
- completion can offer keywords and local syntactic names without a semantic
  snapshot
- parse errors do not erase the last useful editor context

### Phase 3: Batch Semantic Snapshot

Goal: reintroduce compiler-backed diagnostics and hover without rebuilding all
features at once.

- [x] Wrap the current compiler pipeline behind a semantic analysis job.
- [x] Produce `SemanticSnapshot` from lex/parse/derive/desugar/typecheck.
- Preserve stale semantic snapshots until a newer semantic snapshot succeeds.
- [x] Return semantic hover only when the snapshot version is compatible enough with
  the current text; otherwise fall back to syntax/no answer.

Done when:

- hover on local values/types works on valid code
- diagnostics are compiler-backed
- failed typechecking does not poison the document store

### Phase 4: Project State and Imports

Goal: stop treating each file as an island.

- [x] Find the containing `project.toml` for an open file and run the semantic
  analysis job in project mode.
- [x] Track import edges for open files and recheck open dependents when a
  primary module changes.
- [x] Cache prelude-loaded base checkers per project root so every edit does not
  reload the prelude and stdlib surface.
- [x] Resolve path/git dependency module exports from `project.toml`, preserving
  dependency visibility/private-module metadata during local module refreshes.
- [x] Warm dependency module exports in the cached base checker so edit-time
  analysis clones do not repeatedly typecheck unchanged dependency packages.
- [x] Refresh the project module map for each semantic analysis clone, so added
  or removed modules do not require restarting the server.
- Watch project files so added/removed modules can trigger affected open files
  without waiting for the user to edit one of them.
- [x] Track import edges from parse snapshots.
- [x] Recheck changed open files plus reverse open dependents.
- [x] Add an open-document source overlay so unsaved edits in imported modules are
  used when checking dependents.
- [x] Cache clean dependency module interfaces at the project level.
- [x] Cache clean workspace module interfaces at the project level.
- [x] Use current-module interface changes to decide whether open reverse
  dependents need rechecking.
- [x] Coalesce analysis scheduling to one in-flight semantic job per file.
- [x] Skip starting typecheck work when an analysis job is already stale before
  the typechecker phase.
- [x] Keep base checker clones lighter by moving warmed dependency module
  interfaces into project state instead of storing them inside the base checker.
- [x] Skip repeated interface-cache updates for unchanged imported modules.
- [x] Seed only direct imports for the file being checked.
- [x] Replace the first conservative interface fingerprint with a stable sorted
  projection.

This phase should borrow from `docs/planning/incremental-checking.md`, but the
new server should own the project database rather than hiding it inside cloned
`Checker` values.

Done when:

- adding a module does not require restarting the LSP
- editing module A rechecks modules that import A
- unchanged dependencies are reused

### Phase 5: Semantic Navigation

Goal: rebuild definition first on semantic identity. References and rename are
explicitly deferred until project typechecking is solid and fast.

- [x] Create a `SemanticIndex` foundation from `CheckResult`:
  - [x] value definition id -> location
  - [x] value usage id -> definition id
  - [x] value definition id -> reference locations
  - [x] type/record definition name -> location
  - [x] type/record reference spans -> definition name
  - [x] effect/trait/handler references
  - [x] module name -> file
  - [x] docs by semantic key
- [x] Port local go-to-definition to use `CheckResult.references` and
  `node_spans` through `SemanticIndex`.
- [x] Port cross-module go-to-definition to use cached semantic definition
  locations built during analysis, not request-time file reads.
- [x] Port value find-references to query this index.
- [x] Add a project-level per-module `SemanticIndex` cache for type/record
  references across checked modules.
- [x] Add occurrence kinds before rename so binding declarations, definitions,
  and ordinary references can be filtered precisely.
- [x] Correct local value references with resolver lexical binding identity so
  shadowed locals stay separate.
- [x] Port rename only after references are trustworthy.

Avoid copying the old "search AST by name, then guess module" approach.

Done when:

- shadowed locals navigate correctly
- imported aliases navigate correctly
- trait/effect/type references use the same identity model as the compiler

### Interlude: Prelude Import Hygiene

Goal: make LSP project checking treat the prelude as a single shared semantic
surface, not as a module that can be reloaded or re-registered through multiple
paths during dependency/workspace analysis.

- [x] Audit how the LSP cached base checker, dependency module interface seeding,
  and workspace module checks each carry `Std.*` modules.
- [x] Reproduce the real-project failure:
  `type error in module 'Kraken.Core': type error in module 'Std.Base': duplicate impl: Std.Base.Semigroup is already implemented for String`.
- [x] Ensure prelude/std modules are loaded exactly once per project semantic
  generation, then reused as immutable compiler state by imported workspace and
  dependency checks.
- [x] Add a protocol or checker-level regression that opens a project importing
  dependency modules that themselves rely on stdlib/prelude impls.

Done when:

- opening/checking dependency-heavy projects does not re-register stdlib impls
- prelude/std diagnostics do not leak into unrelated workspace modules
- fixing ordinary project files never requires restarting the LSP to clear
  stale stdlib state

### Phase 6: Completion and Code Actions

Goal: make interactive features fast and context-aware.

- [x] Split completion into syntax fallback and semantic enrichment.
- [x] Add context detection: expression position, type position, import position,
  record field position, handler body, effect `needs`, etc.
- [x] Port module/import completions from project semantic state.
- [x] Port record field completions from explicit record metadata.
- [x] Add semantic completions for values, constructors, types, traits, effects,
  handlers, and effect operations from indexed/cache-backed semantic data.
- Port code actions one at a time, each with tests or fixtures.

Done when:

- completion never blocks on typechecking
- completion works acceptably during invalid code
- context filters prevent "everything everywhere" lists

### Phase 7: Polish and Parity

Goal: retire the old server.

- Formatter.
- Signature help.
- Missing-arm/missing-import/missing-impl code actions.
- Semantic tokens.
- Workspace/multi-root support if needed.
- Performance counters and debug command output.

Done when:

- the new server covers the common workflow better than the old one
- known gaps are documented
- editor integration launches the new binary by default

## Salvage List

Likely worth copying after cleaning boundaries:

- `LineIndex`, with tests around UTF-16 and char-boundary behavior.
- Diagnostic conversion helpers.
- Formatter request handler.
- Hover display/type formatting helpers, once backed by semantic keys.
- Document symbol rendering, if decoupled from full typechecking.
- Code action rendering/edit construction.

Treat carefully:

- Completion helpers that slice raw source offsets.
- Definition lookup.
- Symbol index.
- Rename.
- Any request path that reads files or typechecks synchronously.

Do not preserve as architecture:

- cached `Checker` clone as the unit of work
- request handlers doing compiler work
- semantic features keyed primarily by source spelling
- losing all snapshots on parse failure
- publishing diagnostics without document-version checks

## Immediate Audit Checklist

Before porting a feature from the old server, answer:

- Does it require semantic identity, or can it be syntax-only?
- What snapshot does it read?
- Is the snapshot version checked against current document state?
- Does it block on file I/O, project scanning, or typechecking?
- Does it use `ResolutionResult` or reconstruct identity by name?
- What should it return when semantic data is stale or absent?

## Testing Strategy

Start with fixture-style tests for the server core, even before full LSP
integration tests.

Core tests:

- stale check result is discarded
- syntax error keeps previous semantic snapshot
- document version increments and snapshots attach to the right version
- UTF-16 positions map safely to byte offsets
- project graph updates when imports change

Feature tests:

- hover local variable
- hover imported function
- go-to-definition through alias
- shadowed local references
- record field completion
- syntax-only keyword completion during parse error

Manual smoke tests:

- type quickly in a tiny project and watch diagnostics not flicker backward
- add a new module and import it without restart
- intentionally break syntax and confirm completion still responds
- open references/rename on a symbol in a multi-file project

## Open Questions

- Should the parser grow a recovery mode for top-level items, or should the LSP
  own a lighter pre-parser for module/import/declaration outlines?
- Should the current in-memory source overlay move out of the LSP and become a
  general compiler source-provider abstraction?
- What semantic key should become the public LSP identity: `NodeId`, a new
  stable `DefId`, or a `(module, namespace, name, span)` key derived at the
  `CheckResult` boundary?
- How much of project checking should live in the compiler crate versus the LSP
  project database?
- Do we want file watching for closed files in the first rebuild, or only after
  the basic open-file loop is stable?

## Decision Log

- 2026-06-24: Prefer a fresh LSP skeleton over incremental surgery on the
  current server. The current implementation remains as reference and salvage
  source.
- 2026-06-24: Use `src/lsp/` for the new server and move the old implementation
  to `src/lsp_legacy/`. Keep the normal binary name `saga-lsp` for the rebuild
  and add `saga-lsp-legacy` as an escape hatch.

## Current Next Step

Implement the first Phase 6 completion slice:

1. [x] add completion context detection for import, type, expression, record
   field, handler/effect positions
2. [x] use syntax fallback completions during parse/type errors
3. [x] add module/import completions from project module maps and cached module
   interfaces
4. [x] add record field completions from semantic record metadata
5. [x] add semantic completions for values, constructors, types, traits,
   effects, handlers, and effect operations
6. [x] add local parameter/let completions from the semantic definition index
7. [x] show qualified exported function signatures and classify qualified
   constructors/handlers accurately
8. [x] add protocol regressions for each context

Completion is ready to be treated as functionally complete for the rebuild.
Next: port code actions one at a time. Typechecking correctness and edit-time
performance stay the priority: interactive handlers must read snapshots only and
must not perform request-time project scans or typechecking.
