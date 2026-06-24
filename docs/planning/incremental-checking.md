# Incremental Project Checking

Status: draft living plan

## Why This Exists

Saga currently checks projects in a batch shape. A check starts with a checker,
loads project/dependency module maps, parses imports, typechecks imported
modules on demand, and returns one `CheckResult` for the entry module. The LSP
rebuild has already improved this with project-root base checkers, dependency
export warmup, source overlays for open files, and reverse-dependent rechecks,
but the core unit of reuse is still too coarse: clone a warmed `Checker`, run
the normal import machinery, and let module caches inside that checker do what
they can.

That is good enough as a stabilization step, but it will not be the long-term
shape. The next step is to make the project itself the semantic database.

This should serve two related clients:

- the LSP, which needs low-latency diagnostics, hover, completion, and
  navigation for open files
- future incremental `saga check` / `saga build`, which should avoid redoing
  unchanged front-end work and eventually unchanged codegen/BEAM artifact work

The LSP should be the first implementation client because it has the tightest
feedback loop and can prove the invalidation model without committing to all
build-artifact persistence up front.

Related docs:

- `docs/planning/lsp-rebuild.md`
- `docs/compiler-overview.md`
- `docs/typechecking.md`
- `docs/module-system.md`

## North Star

Build one project semantic database that knows:

- which module name maps to which source file
- which package exposes which modules, and which modules are private
- which source text is current, including unsaved editor overlays
- which modules import which other modules
- which modules are dirty
- which cached module interface can be reused
- which cached full check result can be reused
- which downstream modules must be rechecked when an interface changes

The compiler should still own the meaning of Saga programs. The project
database should own scheduling, caching, fingerprinting, invalidation, and
snapshot publication.

## Layering Decision

Treat incremental checking as a compiler feature with an LSP-first frontend.

The first implementation can live in `src/lsp/` while the APIs settle, but the
core concepts should be named and shaped so they can move into a compiler
project subsystem later. Avoid putting editor concepts such as `Url`, document
version, or LSP diagnostics into the reusable core.

Suggested split:

- `CompilerProjectState` or similar, eventually reusable by CLI/build:
  module maps, source providers, fingerprints, dependency graph, module
  interfaces, semantic caches, invalidation
- LSP wrapper:
  URL/path conversion, document versions, open-document source overlay,
  debounce scheduling, stale-result discard, diagnostic publication
- Future build wrapper:
  artifact fingerprints, codegen/lowering cache, `.core` and `.beam` outputs,
  package/dependency install metadata

## What To Cache

### Source Snapshot

Keyed by canonical source path.

Stores:

- source fingerprint
- source text origin: open overlay, disk, builtin, dependency package
- line index for editor-facing paths
- module declaration and import outline if available

This layer answers "did the text change?"

### Parse Snapshot

Keyed by source fingerprint.

Stores:

- parsed `Program` on success
- syntax diagnostics
- module name
- import list
- top-level declaration outline

This layer answers "did the parsed structure change?"

### Module Header / Interface

Keyed by source fingerprint plus relevant compiler version/config.

Stores enough information for importers to resolve names before the full body is
checked, especially for cycles:

- public types, constructors, records, traits, effects, handlers
- explicitly annotated public values where supported
- public re-export declarations that can be grounded from dependencies
- visibility/package ownership

This layer answers "what can another module see before body inference?"

This may initially be derived from existing `ModuleExports` after full
typechecking, but the long-term direction should match the circular import
architecture: split a cheap header surface from a full inferred interface.

### Full Module Interface

Keyed by:

- module source fingerprint
- imported module interface fingerprints
- compiler version/config
- package visibility context when relevant

Stores:

- `ModuleExports`
- `ModuleCodegenInfo`
- public docs
- import dependency set
- interface fingerprint

This layer answers "has anything visible to importers changed?"

The interface fingerprint is the important boundary. If a module body changes
but its exported types, schemes, impls, effects, handlers, and codegen metadata
do not change, importers should not need to recheck.

### Full Check Result

Keyed by:

- module source fingerprint
- imported module interface fingerprints
- compiler version/config

Stores:

- `CheckResult`
- semantic diagnostics
- `ResolutionResult`
- per-node types and spans for LSP features
- references and definition metadata
- imported module check summaries needed by downstream compiler phases

This layer answers "can this exact module body result be reused?"

For the LSP, this is the richest snapshot. For future builds, it is also the
front-end input to elaboration and lowering.

### Build Artifact

Not part of the first LSP slice, but the cache keys above should leave room for
it.

Potential future layers:

- elaborated program
- normalized program
- backend resolution / optimizer facts
- Core Erlang text fingerprint
- compiled `.beam` artifact fingerprint
- dependency package artifact metadata

This layer answers "does this module need codegen or BEAM compilation again?"

## Dependency Model

Track dependencies at module granularity.

```text
module -> direct imports
module -> reverse dependents
module -> SCC id
SCC -> member modules
package -> exposed modules
package -> private modules
```

Invalidation starts from changed source paths, maps them to modules, and walks
reverse dependents only when the changed module's interface fingerprint changes.

Body-only changes should recheck the changed module, publish its diagnostics,
and leave importers alone.

Interface changes should recheck direct dependents, then continue outward only
when those dependents' interfaces also change.

Cycles should be invalidated as SCC units. If any module in an SCC changes, the
whole SCC's header/interface/check cache is suspect until the SCC is rechecked.

## Source Providers

The project checker should not read files ad hoc from inside import resolution.
It should ask a source provider:

```text
SourceProvider::read(path) -> SourceSnapshot
```

Provider priority:

1. open-document overlay from the LSP
2. builtin module source
3. workspace/project file on disk
4. dependency package file on disk

This preserves the current LSP behavior where unsaved changes in an imported
open module affect dependents, but makes it a compiler-facing abstraction rather
than an LSP-only patch.

## Immediate LSP Slice

Goal: make edit-time typechecking reuse clean module work and avoid rechecking
importers when a changed module's public interface is unchanged.

Progress:

- [x] Timing/log instrumentation for the rebuilt LSP analysis path.
- [x] LSP-owned `ProjectSemanticState` skeleton.
- [x] Existing base-checker cache and open-file dependency graph moved under
  per-project state.
- [x] Fingerprint-guarded dependency module interface cache seeded into fresh
  checker clones.
- [x] Fingerprint-guarded workspace module interface cache for clean current
  modules.
- [x] Reverse-dependent rechecks gated by current-module interface changes.
- [x] One in-flight semantic analysis per file, coalescing edits to the newest
  pending version instead of running overlapping stale checks.
- [x] Stale-before-typecheck guard so a job that becomes obsolete during
  pre-typecheck work does not start the expensive checker.
- [x] Avoid repeated interface-cache updates for imported modules whose source
  fingerprint is unchanged.
- [x] Keep stored base checkers light by harvesting warmed dependency
  interfaces into project state, then clearing large module semantic caches
  before storing the base checker.
- [x] Seed only modules directly imported by the checked file instead of every
  cached module in the project.
- [ ] Replace the first conservative `ModuleExports` debug fingerprint with a
  stable sorted interface projection.

### Step 1: Measure Before Cutting

Add timing spans/counters around:

- project/dependency module-map refresh
- dependency export warmup
- parse/derive/desugar for the changed module
- import loading and cache hits/misses
- current module body typecheck
- dependent selection
- dependent rechecks
- diagnostic publication

Expose this through logs first. Later, add an LSP debug command or status output.

Done when a slow hover/check session can answer "where did the time go?"

### Step 2: Introduce Project Semantic State

Add an LSP-owned `ProjectSemanticState` that sits above cloned `Checker` values.

It should store:

- project root
- module map and visibility/private-module maps
- source snapshots by path
- parse snapshots by module
- import graph and reverse graph
- per-module semantic cache entries
- dependency package cache entries
- generation counter

Do not try to persist this cache to disk yet.

Done when the LSP has one obvious place to ask "what is the current state of
module X?"

### Step 3: Cache Parsed/Derived Programs

Avoid reparsing unchanged open/project modules while scheduling checks.

Cache:

- source fingerprint
- parsed program
- derived/desugared program if that is the stable typechecker input
- parse diagnostics
- import list

Done when repeated edits in `Main.saga` do not reparse unchanged imported
project modules.

### Step 4: Promote Module Interfaces To Cache Entries

Cache each module's `ModuleExports` and `ModuleCodegenInfo` outside a single
checker clone.

Add or expose a checker API that can seed imports from known module interfaces
instead of reloading/rechecking those modules through `load_module`.

The current `Checker` already has internal module caches. This step lifts the
clean cache boundary out to project state so new checker instances can be
seeded deliberately.

Done when checking module A can reuse cached exports for B without invoking
B's parse/typecheck path.

### Step 5: Interface Fingerprints

Compute a stable fingerprint for the public interface of a module.

Include at least:

- exported value schemes and origins
- exported type/constructor/record surfaces
- type aliases
- traits, impls, effects, handlers
- effectful function metadata
- codegen metadata required by importers/build
- public docs if documentation consumers should update on doc-only edits

Start with a conservative hash, even if it over-invalidates. It is better to
recheck too much than to keep stale type information.

Current first slice:

- [x] Compute a conservative interface fingerprint from `ModuleExports`.
- [ ] Replace debug-format hashing with a stable sorted projection.

Done when the LSP can distinguish "module changed" from "module interface
changed."

### Step 6: Invalidate By Interface Change

Current behavior rechecks open reverse dependents when a dependency changes.
Refine this:

1. recheck the changed module or SCC
2. publish diagnostics for changed open files
3. compare old vs new interface fingerprint
4. if unchanged, stop
5. if changed, enqueue reverse dependents
6. repeat in dependency order

At first, recheck only open dependents plus files needed to typecheck them. Once
file watching exists, extend this to closed workspace files too.

Current first slice:

- [x] Cache clean current-module interfaces.
- [x] Skip open reverse dependents when the current module interface is
  unchanged.
- [x] Force dependent rechecks when the current module has syntax/type errors or
  no usable interface, preserving existing cross-module diagnostics.

Done when editing a private helper body in `A` does not recheck open module `B`
that imports `A`, but changing an exported type or function signature does.

### Step 7: Dependency Package Cache Discipline

Dependency modules should be treated as mostly immutable within one LSP session.

Cache:

- exposed module maps from dependency `project.toml`
- private module maps per dependency package
- warmed dependency module exports
- dependency module interface fingerprints

Invalidate this cache only when dependency source paths or dependency manifests
change. For now, a manual/project refresh can be acceptable.

Done when importing `Kraken.Core` or similar dependency modules does not cause
repeated dependency package typechecking during normal editing.

## Future CLI/Build Slice

Once the LSP project semantic database is working, extract the compiler-facing
parts and reuse them for `saga check` and `saga build`.

### Incremental `saga check`

Use the same project graph and semantic cache, but with disk-only sources unless
the CLI later grows an explicit overlay/test hook.

Expected behavior:

- scan project once
- identify changed modules from fingerprints
- recheck affected SCCs/modules
- print diagnostics for affected files
- reuse unchanged dependency/project interfaces

### Incremental `saga build`

Add artifact cache layers after typechecking:

- elaboration result keyed by `CheckResult`/interface inputs
- lowering result keyed by front-end and backend metadata
- Core Erlang file content hash
- BEAM artifact hash and compiler flags
- dependency package artifact metadata

Expected behavior:

- body-only change in a private helper recompiles that module only
- interface change recompiles affected downstream modules
- unchanged dependencies are not rebuilt
- build outputs are invalidated by compiler version and relevant config

## Implementation Order

Recommended next milestones:

1. Instrument the current rebuilt LSP pipeline.
2. Add `ProjectSemanticState` without changing behavior.
3. Move parse/import graph/source overlay data into that state.
4. Cache parsed/derived programs by source fingerprint.
5. Seed checker clones from cached module interfaces.
6. Add interface fingerprints and interface-change invalidation.
7. Extract reusable project-state pieces out of `src/lsp/` once the shape stops
   moving.

## Testing Strategy

Keep using the subprocess LSP protocol harness for behavior tests.

Add cases for:

- body-only change in imported module does not recheck importer
- exported signature/type change rechecks importer
- exported docs-only change behaves according to the chosen doc fingerprint rule
- unsaved imported-module edit affects dependents
- adding/removing a module updates the module map without restart
- private dependency module remains inaccessible outside its package
- exposed dependency module import is cached across multiple checks
- cyclic modules invalidate and recheck as an SCC
- stale check result cannot publish after a newer edit

Add unit tests around pure project-state logic once it exists:

- reverse dependency walk
- SCC invalidation
- interface fingerprint comparison
- source-provider overlay precedence
- dependency package cache invalidation

## Open Questions

- What exact data belongs in the first interface fingerprint?
- Should doc-only edits change the interface fingerprint for LSP/docs consumers,
  or should docs have a separate fingerprint?
- How much of `ModuleExports` can be hashed directly, and how much needs a
  stable serialized/interface projection?
- Should parse snapshots store derived/desugared programs, or should derive and
  desugar be separate cache layers?
- What is the right public API for seeding a `Checker` from cached module
  interfaces?
- When do we move project-state code from `src/lsp/` into a reusable compiler
  module?
- Do CLI incremental caches start in-memory only, or do we design the disk cache
  at the same time as the first extraction?

## Non-Goals For The First Slice

- incremental parsing inside one file
- parallel checking
- disk-persistent semantic caches
- incremental codegen/lowering
- perfect minimal invalidation
- file watching for every closed file, unless it becomes necessary for the LSP
  feel test

## Current Next Step

Measured on `/home/dylan/projects/sesh-importer/saga/src/Database.saga`, a
derive/import-heavy file with current diagnostics:

- before cache cleanup: warm edit was about 2.55s analysis / 3.49s wall
- after skipping unchanged interface updates: about 1.67s analysis / 2.39s wall
- after light base checkers and direct-import seeding: about 1.22s analysis /
  1.83s wall
- after the LSP-specific light `CheckResult` snapshot: about 0.48s analysis /
  0.87s wall to diagnostics publication
- after export-only interface seeding plus a 100ms semantic debounce: about
  0.28s analysis / 0.41s wall to diagnostics publication
- after caching pathless builtin module interfaces such as `Std.DateTime`:
  about 0.13s analysis / 0.25s wall to diagnostics publication

The big cloned-result hotspot is gone: `to_result` dropped from roughly 517ms
to roughly 40ms for this file. The cached-interface seed hotspot is also gone:
seeding direct imports now takes roughly 1ms instead of roughly 147ms because
the checker receives only the exports it needs for typechecking, while
cross-module definition locations read cached `CheckResult` spans from the
project store. The remaining hidden import hotspot was uncached embedded stdlib
modules: `Std.DateTime` was being typechecked on every edit because interface
cache entries required filesystem paths. Builtin modules now use an
embedded-source fingerprint and pathless cache entry. The remaining warm-edit
cost is mostly the current file's own semantic pass at roughly 80ms plus the
100ms debounce. Next target the measured typechecker/body path, then replace
the temporary debug-format interface fingerprint with a stable sorted interface
projection.
