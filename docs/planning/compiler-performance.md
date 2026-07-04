# Compiler Performance Plan

Status: living plan, Phase 1 in progress

## Why This Exists

Saga's compiler has grown enough semantic machinery that build latency is now a
language-design problem, not just a command-line polish problem. Recent Generic
deriving, functional dependencies, trait specialization, and Generic folding
made generated programs much larger and pushed more work into typechecking and
lowering. A small but realistic project such as Kraken currently takes around
12 seconds for a warm full build with the debug compiler.

This plan records the current profiling facts and the intended sequence of
work. The bias is deliberate: make full builds efficient and well-instrumented
first, then build incremental rebuilds and watch mode on top of the same
phase-shaped units.

Related docs:

- `docs/compiler-overview.md`
- `docs/typechecking.md`
- `docs/trait-dict-passing.md`
- `docs/planning/incremental-checking.md`
- `docs/planning/lsp-rebuild.md`

## North Star

The compiler should have a fast, reliable full-build path and an incremental
path that is mostly a cache/invalidation layer over the same phases.

Concretely:

- no repeated whole-project analysis inside per-module work
- stdlib and dependency artifacts are reused by default and invalidated
  correctly
- "no source changed" `saga build` / `saga run` is near-instant in dev mode
- body-only changes rebuild only the changed module's artifacts
- interface changes rebuild only the affected reverse dependency slice
- watch mode is a thin UX layer over correct invalidation, not a separate
  compiler

## Current Measurements

Measured on Kraken with warm stdlib cache using the debug compiler and
`SAGA_BUILD_TRACE=1 SAGA_TYPECHECK_TRACE=1`.

Approximate warm build shape:

| Area                                        | Time   |
| ------------------------------------------- | ------ |
| total Saga-reported build                   | 11.46s |
| wall clock                                  | 12.13s |
| entry parse/typecheck/import walk           | 3.89s  |
| `checker.to_result()`                       | 0.37s  |
| redundant per-module rechecks in build loop | 1.58s  |
| user module emit/lower total                | 3.6s   |
| `erlc`                                      | 1.08s  |

Important finding: Generic fold itself is not the main Kraken compile-time
culprit. Local folds are mostly sub-3ms per module, and cross-module fold was
only about 12ms for the heaviest measured module (`Read`).

The biggest backend surprise is in lowering:

- `Lowerer::lower_module` populates call-effect metadata for the active module.
- Then it walks every compiled module in `ctx.modules` and repopulates their
  call-effect metadata for every module being emitted.
- On Kraken this repeated cross-module call-effect population costs roughly
  140-175ms per emitted user module, about 1.8s total.

The biggest DX surprise is build policy:

- `saga run --release` checks the project cache.
- dev `saga run` always calls `build_project("dev")`, which removes the build
  directory and rebuilds from scratch.

After the first call-effect precompute pass, the same warm Kraken build measured
`Built in 10.75s` with `real 11.54s`. The user-visible improvement is modest so
far, but the repeated cross-module call-effect walk is no longer the dominant
backend cost.

After reusing cached per-module `CheckResult`s during the build codegen loop,
warm Kraken measured `Built in 8.82s` with `real 9.52s`.

After preparing cross-module emit indexes once per build instead of once per
emitted module, warm Kraken measured `Built in 8.65s` with `real 9.34s`.

After changing the lowerer to borrow `CheckResult` instead of cloning it per
lowering/precompute pass, warm Kraken measured `Built in 6.66s` with
`real 7.34s`.

After the v2 content-fingerprint manifest work, warm Kraken full build measured
`Built in 6.78s` with `real 7.48s` using `time -p saga build`.

With a valid dev build manifest in place, hot `saga run` on Kraken skips the
compiler path entirely and goes straight to executing the generated BEAM files.
The measured run still took `real 32.28s` because Kraken's sample program waits
through Postgres-unavailable paths, but it printed no `Compiling ...` /
`Built in ...` output and only used `user 0.94s`, `sys 0.24s`.

After extracting cache helpers and upgrading manifests to version 3 with
expected output artifacts, `saga build` also consults the cache before
rebuilding. A hot Kraken `time -p saga build` now reports:

| Metric | Time  |
| ------ | ----- |
| real   | 0.01s |
| user   | 0.01s |
| sys    | 0.00s |

## Instrumentation

Keep hidden tracing available while doing this work.

Existing:

- `SAGA_TYPECHECK_TRACE=1`
- `SAGA_TYPECHECK_TRACE_FILE=/tmp/saga-typecheck.log`
- `SAGA_STATS=trait-spec`
- `SAGA_DEBUG_TRAIT_DISPATCH`

Added:

- `SAGA_BUILD_TRACE=1`
  - build orchestration spans
  - codegen spans
  - lowerer setup spans
  - call-effect population spans

Trace output should stay hidden behind env vars. Normal compiler output should
remain concise.

## Work Sequence

### Phase 1: Fast Full Builds

Goal: remove repeated work while preserving current full-build semantics.

- [x] Keep `SAGA_BUILD_TRACE` and typecheck trace in-tree.
- [x] Precompute or cache cross-module `CallEffectMap`s instead of repopulating
      all compiled modules inside every `lower_module` call.
- [x] Use the existing `CompiledModule.call_effects` field or replace it with a
      clearer precomputed analysis bundle.
- [x] Stop re-typechecking modules during the codegen loop when the project
      `CheckResult` already contains the module's checked program and result.
- [x] Reduce repeated per-module context cloning, especially `ctx.codegen_info()`
      and external Generic-fold source collection.
- [ ] Measure after each change on Kraken and at least one smaller fixture.

Done when:

- warm Kraken full build has a clear measured improvement
- call-effect population is O(project) per build, not O(project \* modules)
- the codegen loop does not redo front-end checking for already-checked modules

Progress:

- 2026-06-28: added hidden `SAGA_BUILD_TRACE` spans across build orchestration,
  codegen, and lowering.
- 2026-06-28: added a precompute path for module `CallEffectMap`s and a
  `CompiledModule.call_effects_ready` marker so empty-but-computed maps do not
  fall back to the old repeated AST walk. This reduced Kraken's repeated
  `populate_call_effects_cross_modules` work from roughly 140-175ms per emitted
  user module to low single-digit milliseconds per emitted module. The remaining
  cost is the one-time precompute pass, currently about 1s on Kraken with the
  debug compiler.
- 2026-06-28: changed project builds to reuse cached per-module programs and
  `CheckResult`s from the initial import walk. The old parse/check fallback is
  still retained for genuinely uncached modules, but cached modules no longer
  pay the redundant `recheck_module` cost.
- 2026-06-28: added a prepared emit context that builds `codegen_info`,
  cross-module Generic-fold externals, and merged module resolution once per
  emit batch. On Kraken, the per-module `collect_codegen_info` and
  `collect_external_*` trace spans disappeared and were replaced by a single
  roughly 5ms `prepare_emit_context` span.
- 2026-06-28: changed `Lowerer` to borrow `CheckResult` instead of cloning it
  for every lowerer instance. This reduced Kraken's project
  `precompute_call_effects` trace span from roughly 989ms to roughly 350ms and
  improved warm build time to `Built in 6.66s`.

### Phase 2: Cache Policy

Goal: make whole-project reuse correct enough to enable by default in dev.

- [x] Make dev `saga run` consult `check_project_cache` and `check_script_cache`
      just like release mode.
- [x] Make `saga build` consult the same validated cache before rebuilding.
- [x] Stop deleting `_build/dev` before deciding whether a cached build is valid.
- [x] Make the build manifest describe all inputs that can invalidate a whole
      build:
  - compiler build hash
  - stdlib fingerprint
  - `project.toml`
  - dependency metadata
  - all project source fingerprints
  - bridge `.erl` file fingerprints
  - profile and relevant compiler flags
- [x] Prefer content hashes over mtimes for correctness; mtimes can remain a
      cheap prefilter if useful.
- [x] Preserve a helpful reason when a cache misses, gated behind trace output.
- [x] Verify expected project/script output artifacts, not just the entry beam.

Done when:

- no-change `saga build` and `saga run` in dev mode are near-instant
- cache misses are explainable
- stale stdlib or project artifacts are not reused

Progress:

- 2026-06-28: changed dev `saga run` for scripts and projects to consult the
  existing dev build manifest before rebuilding. This does not yet harden the
  manifest format; it only stops ignoring a valid dev cache.
- 2026-06-28: validated the project cache path on Kraken itself. After a warm
  `saga build`, `saga run` reused the build artifacts without recompiling; the
  remaining wall time came from Kraken's runtime DB-unavailable work rather than
  compiler work.
- 2026-06-28: added `SAGA_BUILD_TRACE` cache hit/miss reasons for script and
  project cache checks. Normal CLI output stays unchanged, but trace runs now
  explain whether a miss came from the compiler hash, stdlib fingerprint,
  input fingerprints, missing entry beam, missing manifest, or incomplete
  stdlib cache.
- 2026-06-28: upgraded build manifests to version 2 with explicit content
  fingerprints for script inputs and project inputs. Project fingerprints now
  cover `project.toml`, `saga.lock`, project `src/` and `lib/` Saga sources,
  project bridge `.erl` files under `src/`, `lib/`, and `tests/`, and the same
  source/bridge metadata for direct non-Hex dependencies. Cache validation now
  compares these fingerprints instead of mtimes; touching a source file without
  changing content still hits the project cache. Manifest writes are now
  temp-file-plus-rename instead of direct writes.
- 2026-06-28: extracted the build-manifest and input-fingerprint machinery into
  `src/cli/cache.rs` with focused tests for added, removed, changed, and
  content-unchanged inputs.
- 2026-06-28: upgraded build manifests to version 3 with expected output
  artifacts. Cache validation now rejects manifests whose project/script Beam
  artifacts are missing, and `saga build` uses the same cache validation as
  `saga run`. A hot Kraken `time -p saga build` measured `real 0.01s`.
- 2026-06-28: upgraded build manifests to version 6 with an explicit profile
  field. The profile is still encoded by `_build/<profile>`, but manifests now
  reject accidental cross-profile reuse directly; future output-affecting
  compiler flags should be added to this same manifest boundary or force a
  manifest-version bump.

### Phase 3: Reliable Stdlib And Dependency Artifacts

Goal: stdlib and dependency builds are boring, persistent, and trustworthy.

- [x] Keep stdlib artifacts under `_build/.stdlib/<fingerprint>`.
- [x] Ensure the stdlib fingerprint includes embedded Saga sources, bridge
      files, compiler build identity, and any lowering/codegen ABI version.
- [x] Write manifests atomically via temp dirs and rename.
- [x] Verify expected `.beam` files, not just the manifest.
- [ ] Apply the same design to path/git/Hex dependencies where possible:
      dependency source fingerprint -> dependency artifact directory.

Done when:

- cold stdlib build is paid once per compiler/content fingerprint
- warm builds never compile stdlib
- dependency artifact reuse follows the same invalidation rules as project code

Progress:

- 2026-06-28: stdlib artifacts are stored under
  `_build/.stdlib/<fingerprint>` and finalized by building into a temporary
  directory before renaming it into place. Cache validation checks the stdlib
  manifest fingerprint, compiler build identity, embedded stdlib content hash,
  and every expected stdlib/bridge Beam file.
- 2026-06-28: added focused stdlib cache-completeness coverage so missing
  manifests, mismatched fingerprints, mismatched content hashes, and missing
  Beam artifacts all reject the cache.
- 2026-06-28: upgraded build manifests to version 7 with structured dependency
  fingerprints. Project cache validation and partial-rebuild planning now
  compare direct and transitive dependency fingerprints. Path/git dependencies
  include source metadata and local `ebin` / `priv` artifacts; Hex dependencies
  include lock metadata and installed `ebin` / `priv` artifacts. Dependency
  changes conservatively force a full project rebuild instead of reusing module
  artifacts across a changed dependency boundary.
- 2026-07-04: upgraded build manifests to version 8 with stricter output
  artifact validation. Project bridge `.erl` outputs are now part of expected
  output artifacts, and cache validation rejects unexpected stale `.beam` files
  left in `_build/<profile>`. The partial rebuild planner also falls back to a
  full clean rebuild when stale beams are present.
- Remaining gap: dependency artifacts are fingerprinted but not yet stored in a
  separate persistent artifact cache keyed by dependency source and package
  metadata.

### Phase 4: Incremental Build Manifest

Goal: introduce module-level cache keys without changing build behavior yet.

Build a richer manifest that records, per module:

- source path
- declared module name
- source content hash
- direct imports
- exported interface fingerprint
- implementation/check fingerprint
- generated Core file path
- generated Beam file path
- bridge file dependencies, if any

This should align with `docs/planning/incremental-checking.md`:

- source snapshot
- parse snapshot
- module interface
- full check result
- build artifact

Done when:

- a full build writes enough information to know what would be dirty next time
- no partial rebuilds are required yet
- the manifest format has a version field for future changes

Progress:

- 2026-06-28: upgraded build manifests to version 4 with per-emitted-module
  source hashes and `.core` / `.beam` artifact names. This gives the next build
  enough information to decide whether a source-only change can reuse the
  previous build directory instead of starting from a clean `_build/<profile>`.
- 2026-06-28: upgraded build manifests to version 5 with stable public
  interface fingerprints for emitted modules, matching the LSP's sorted
  `ModuleExports` projection. These fingerprints let source changes distinguish
  body-only edits from public surface changes.
- 2026-06-28: upgraded build manifests to version 7 with dependency
  fingerprints, so the incremental project manifest has a dependency-level
  invalidation boundary in addition to project source and emitted module
  artifact metadata.
- 2026-07-04: upgraded build manifests to version 8 so the manifest also owns
  stale-beam cleanup. If the previous build contains a Beam file that is not in
  the current expected output set, the next build takes the full clean path
  instead of preserving that artifact through a partial rebuild.

### Phase 5: Partial Rebuilds

Goal: reuse unchanged module artifacts.

- [x] Build the module dependency graph and reverse dependency graph.
- [x] On source change, recheck/rebuild the changed module.
- [x] If its exported interface fingerprint is unchanged, do not rebuild
      importers.
- [x] Conservatively walk reverse dependencies and rebuild the affected slice.
- [x] Refine reverse-dependency rebuilds to stop at unchanged interface
      fingerprints.
- [x] Treat cyclic SCCs as invalidation units.
- [x] Reuse unchanged `.beam` files and only call `erlc` on changed `.core`
      files for source-only module changes.
- [x] Reuse unchanged `.beam` files and only call `erlc` on changed `.core` and
      bridge files.

Done when:

- implementation-only changes rebuild one module plus any entry wrapper needed
- interface changes rebuild the affected slice
- full clean build remains available and is still the correctness reference

Progress:

- 2026-06-28: added a conservative artifact-level partial rebuild path for
  project builds. The front end still runs the full project check for
  correctness, but safe source-only changes no longer delete the build
  directory; the builder emits the changed module plus reverse import dependents
  and invokes `erlc` only for those emitted `.core` files. On a temp copy of the
  imported-pure example project, changing `Helper.saga` rebuilt `Helper` and
  `Main`, skipped stdlib, used the `erlc_partial` path, and finished in `0.40s`.
- 2026-06-28: added interface-fingerprint gating to the partial rebuild planner.
  Body-only changes emit only the changed module; public interface changes emit
  the changed module plus reverse import dependents. On a temp copy of the
  imported-pure example project, adding a private helper to `Helper.saga`
  rebuilt only `Helper` and reused `Main`; adding a public helper rebuilt both
  `Helper` and `Main`.
- 2026-06-28: added focused planner tests for same-interface changes,
  interface-change propagation, missing artifact repair, and structural input
  changes that must fall back to a full rebuild.
- 2026-06-28: changed source files in cyclic import groups now emit the full
  SCC even when the edited module's public interface fingerprint is unchanged.
  Downstream modules outside the cycle are still reused unless an interface
  change propagates to them.
- 2026-06-28: changed bridge `.erl` inputs now use the partial path too: the
  builder copies only the changed bridge files into `_build/<profile>` and adds
  them to the same `erlc` batch as changed `.core` files. Bridge add/remove
  remains a full rebuild so stale beams can be handled conservatively.

### Phase 6: Watch Mode

Goal: add ergonomic rebuild loops over the same invalidation engine.

Possible commands:

```text
saga check --watch
saga build --watch
saga run --watch
saga test --watch
```

Initial behavior:

- watch project source roots, `project.toml`, bridge files, and dependency paths
  when local
- debounce edits
- rebuild affected modules
- print concise diagnostics and timing
- for `run --watch`, restart the BEAM process after a successful rebuild

Done when:

- watch mode adds no separate compiler semantics
- failed rebuilds leave the last successful artifacts intact
- rebuild timing clearly reports what changed and what was reused

## Design Notes

### Optimize Before Incremental Builds

Do the full-build cleanup first. Incremental builds will be much easier if the
full-build pipeline already has explicit phase products and no hidden repeated
whole-world analysis. Otherwise partial rebuilds risk preserving the same
inefficiencies behind a more complicated invalidation system.

### Cache Correctness Comes Before Cache Granularity

A coarse whole-project cache that is always correct is better than a partial
cache that sometimes lies. The first cache milestone is "no-change dev run is
fast and trustworthy"; module-level rebuilds come after.

### Full Build Remains The Oracle

Every incremental step should be testable against a clean full build:

- same diagnostics
- same generated Core for rebuilt modules, modulo stable ordering
- same runtime result
- same public interface fingerprints

When in doubt, invalidate more and rebuild more. Tighten later with traces and
tests.

## Open Questions

- Should `CheckResult` own enough per-module data to eliminate the current
  codegen-loop recheck entirely, or should build create a separate
  `CheckedModule` product?
- Should call-effect maps be computed during `compile_module_from_result`, after
  cross-module Generic fold, or as a separate pre-lowering batch over all final
  programs?
- What is the smallest stable exported-interface fingerprint that is safe for
  skipping importer rebuilds?
- Should the first watch mode depend on an external watcher crate, or start with
  polling for fewer dependencies?
- How much should debug compiler timings guide optimization, versus adding a
  release-built compiler benchmark harness?
