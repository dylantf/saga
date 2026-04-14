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
- Export/visibility information

This is a subset of `ModuleExports` that only requires parsing, not
inference. The key test: can you build it by walking the AST without calling
`check_program_inner`?

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
   imports (instead of from `ModuleExports`).
4. Run `resolve_names` for each module.
5. Typecheck bodies of all modules in the SCC.
6. Build full `ModuleExports` from the typechecked results.

For modules NOT in an SCC (or in an SCC of size 1), the current recursive
`typecheck_import` approach still works unchanged.

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

## Relevant Files

- `src/typechecker/check_module.rs`: `typecheck_import`, `ModuleExports`,
  `resolve_import`, module loading/caching
- `src/typechecker/check_decl.rs`: `process_imports`, `check_program_inner`
  pipeline
- `src/typechecker/resolve.rs`: `resolve_names`, `ScopeMap` consumption
- `src/typechecker/mod.rs`: `ScopeMap`, `ModuleCodegenInfo`
- `src/cli/build.rs`: build pipeline, module map construction
