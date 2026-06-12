# Circular Import Support

## Goal

Allow two modules to import types, constructors, and annotated functions from
each other. This is the common case: module A defines types that B uses, B
defines types that A uses.

This does not require solving mutually-recursive type inference across module
boundaries. We only need headers to carry what the parser already knows.

## Current State

When module A imports module B, the compiler fully typechecks B before
proceeding with A. If B also imports A, A is in the "currently loading" set
and the compiler rejects it with "circular import." The dependency graph is
built implicitly through recursive `typecheck_import` calls, not computed
upfront.

`ModuleExports` (cached after typechecking a module) contains fully-inferred
type schemes, complete record field types, elaborated trait impls, etc. It
cannot be built without running inference on the module's bodies.

The resolution refactor established the key precondition: name resolution no
longer depends on typechecked bodies. The resolver consumes `ScopeMap` (bare
names to canonical identities) and produces `ResolutionResult`. It does not
need inferred types, just "what names exist and where they live." If we can
build a `ScopeMap` from a module header instead of from fully-typechecked
`ModuleExports`, the resolver can resolve names in module A before module B's
bodies have been typechecked.

**Re-exports now exist** (see
[exposing-and-reexports.md](exposing-and-reexports.md)). A module's public
surface can include names that originate in *other* modules — `import M (pub c)`
and `import M (pub ..)`. This is good news for the header design: a re-export is
purely syntactic (the `import` decl names the origin module), so it is
extractable into the header without inference. But it adds an edge the header
and scope construction must follow: a re-exported name resolves not to a local
definition but to a name in another module's surface, which may itself be a
re-export. Re-export *cycles* (A re-exports from B, B re-exports from A) were
explicitly deferred to this work — they are an SCC concern, handled below.

## Background: SCCs

The standard approach for languages that allow mutual imports:

1. Parse all modules in the project (no typechecking yet).
2. Build the dependency graph from import declarations.
3. Compute strongly connected components (Tarjan's algorithm). An SCC is a
   group of modules that all transitively depend on each other. Two modules
   that import each other form an SCC of size 2.
4. Topologically sort the SCCs. SCCs with no external dependencies go first.
5. For each SCC: extract "module headers" from the parsed AST without running
   inference. Build scope maps for all modules in the SCC from those headers.
   Then resolve names and typecheck bodies.

Modules that don't form cycles (SCCs of size 1) can still use the current
recursive approach. The SCC machinery only matters for mutual-import groups.

## Implementation Steps

### 1. Module Header Type

Add a `ModuleHeader` that can be built from parsed+desugared declarations
without inference.

Contents:
- Type names, arities, and constructors
- Record names and field names (not necessarily inferred field types)
- Trait names and method signatures (from source annotations)
- Effect names and operation signatures
- Handler names and effect associations
- Declared function type annotations (not inferred types)
- Export/visibility information, including **re-export edges**: for each
  re-exported name, the surface name, the origin module, the origin name (may
  differ under `pub a as b`), and the visibility level carried forward (e.g.
  opaque). `(pub ..)` is recorded as a re-export-all edge to the origin. These
  come straight from the `Decl::Import` AST — no inference needed.

This is a subset of `ModuleExports` that only requires parsing, not
inference. The key test: can you build it by walking the AST without calling
`check_program_inner`?

Note: the header records that a re-export *edge* exists and where it points, not
the re-exported name's inferred scheme. The scheme is resolved later, from the
origin's full `ModuleExports`, once the SCC is typechecked. For name resolution,
"this name exists and its canonical identity lives in module M" is all the header
needs to supply.

### 2. Explicit Module Graph

Currently `process_imports` in `src/typechecker/check_decl.rs` walks imports
sequentially and triggers recursive typechecking on demand. Replace this with
an upfront scan of all modules' import declarations to build a dependency
graph before any typechecking starts.

For project builds (`saga build`, `saga test`), the compiler already scans
all `.saga` files to build a module map. Extend this to extract import lists
from each parsed module and construct an adjacency list.

For single-file runs (`saga run file.saga`), the graph can be built lazily or
the current recursive approach can remain as a fallback for non-cyclic
imports.

### 3. SCC Computation

Standard Tarjan's or Kosaraju's algorithm over the module graph. Each SCC is
a set of modules that must be processed together. Topologically sort the SCCs
so dependencies are processed first.

### 4. Header-Based Scope Construction

For modules in the same SCC:

1. Parse and desugar all modules in the SCC.
2. Build `ModuleHeader` for each.
3. Build `ScopeMap` entries for each module from the headers of the modules it
   imports (instead of from `ModuleExports`). When an imported header exposes a
   **re-export edge**, follow it: the surface name's canonical identity is the
   edge's origin, not the re-exporting module. Within an SCC the origin's header
   is already built (step 2), so the edge can be resolved without inference.
4. Run `resolve_names` for each module.
5. Typecheck bodies of all modules in the SCC.
6. Build full `ModuleExports` from the typechecked results.

For modules NOT in an SCC (or in an SCC of size 1), the current recursive
`typecheck_import` approach still works unchanged.

**Re-export edge resolution must terminate at a definition.** A re-export chain
is only valid if it eventually grounds in a real definition. Follow edges to
their ultimate origin (the defining module's header). If the chain returns to a
module already on the current follow-path without hitting a definition — A
re-exports `x` from B, B re-exports `x` from A, neither defines `x` — that is a
re-export cycle with no ground: report it as an error, do not loop. Note this is
distinct from a *module-level* import cycle (which is legal and is exactly what
the SCC machinery exists to support); it is specifically a re-export edge that
never resolves to a definition.

### 5. Split ModuleExports

`ModuleExports::collect()` in `src/typechecker/check_module.rs` currently
runs after full typechecking and bundles everything. Split it into:

- `ModuleHeader`: extractable before inference (step 1 above)
- `ModuleExports`: the full post-inference result, built on top of the header

The header feeds scope construction for cyclic imports. The full exports feed
downstream consumers (elaboration, codegen) as before.

### 6. Update Cycle Detection

Replace the current "if module is in loading set, reject" check with:

- If the module is in the same SCC, proceed with header-based resolution.
- If the module is NOT in the same SCC but is still loading, that indicates a
  bug in the SCC computation or graph construction. Reject with an internal
  error.
- Remove the blanket "circular import" rejection.

## Scope Limitations

This plan intentionally does not solve:

- Mutually recursive type inference (functions whose inferred types depend on
  each other across module boundaries)
- Circular trait impl dependencies
- Circular effect/handler dependencies that require body analysis

The practical scope is: share type/constructor definitions and call each
other's explicitly-annotated functions. Unannotated functions in a circular
import group would be an error ("add a type annotation to use this function
across a circular import boundary").

**Re-exports across a cycle** *are* in scope, since their headers are
inference-free: a module in an SCC may re-export names from another module in the
same SCC. The grounding rule above (a re-export chain must terminate at a real
definition) is what keeps this well-defined. The one thing still excluded is a
re-exported name whose *type* the importer needs before the origin's body is
inferred — but re-exports carry their signature from the origin's definition, and
definitions are exactly what the header tier captures, so this falls within the
"explicitly-annotated surface" scope rather than the excluded "mutually recursive
inference" case.

## Non-goal: on-disk interface files

`ModuleHeader` is the *concept* behind a Haskell `.hi` file — a module's
interface (what it exposes) split from its implementation (the bodies) — but it
deliberately does **not** adopt the *machinery*: no serialization to disk, no
versioned interface format, no fingerprint, no cross-build staleness/invalidation
protocol.

The reason: the header solves an *ordering* problem within a single build (let
A's names resolve before B's bodies are inferred), not a *caching* problem across
builds. `.hi` files earn their cost through separate compilation (ship a
library's interface so consumers skip re-checking its source) and recompilation
avoidance across compiler runs. Saga's build is whole-program and already
re-parses and re-checks every `.saga` file each run; cyclic imports introduces no
compilation boundary that would force an on-disk interface. Adding `.hi`
serialization here would be an orthogonal performance project, not part of making
cycles work.

So the header lives in memory for one build and is discarded.

**We will want incremental builds eventually** — and the header is the right
seed for it. One free design constraint pays that forward: build `ModuleHeader`
as clean, self-contained plain data — no borrows into the `Checker`'s mutable
state, no `NodeId`s or interned handles that only mean something mid-build. Kept
serializable *in principle*, the header becomes the natural unit to cache (or one
day write to disk) when incremental/separate compilation is actually worth
building. That work belongs in
[incremental-checking.md](incremental-checking.md) (today an in-memory,
reverse-dependency LSP cache — the same shape, one tier up), not here. Build the
data structure well now; defer every byte of persistence machinery until there's
a measured reason.

## Relevant Files

- `src/typechecker/check_module.rs`: `typecheck_import`, `ModuleExports`,
  `resolve_import`, module loading/caching
- `src/typechecker/check_decl.rs`: `process_imports`, `check_program_inner`
  pipeline
- `src/typechecker/resolve.rs`: `resolve_names`, `ScopeMap` consumption
- `src/typechecker/mod.rs`: `ScopeMap`, `ModuleCodegenInfo`
- `src/cli/build.rs`: build pipeline, module map construction
