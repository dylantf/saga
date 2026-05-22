# Compiler Pipeline

## Overview

```text
Source (.saga)
  -> Lexer (src/lexer.rs)
  -> Parser (src/parser/)
  -> AST (src/ast.rs)
  -> Derive Expansion (src/derive.rs)
  -> Desugar (src/desugar.rs)
  -> Typecheck (src/typechecker/)
     includes: front-end Name Resolution (src/typechecker/resolve.rs)
  -> Elaborate (src/elaborate.rs)
  -> Normalize (src/codegen/normalize.rs)
  -> Backend Resolve (src/codegen/resolve.rs)
  -> Lower (src/codegen/lower/)
  -> Core Erlang AST (src/codegen/cerl.rs)
  -> Print -> .core file
  -> erlc -> .beam file
  -> erl (run)
```

## Phases

### Parse

Hand-written Pratt parser. Produces `Vec<Decl>` (the `Program` type). Each AST
node gets a stable `NodeId` at creation time.

### Derive Expansion

Generates trait impl declarations from `deriving` clauses such as
`deriving (Show, Debug, Eq)`.

### Desugar

Transforms surface sugar into core AST forms: pipes, composition, list
literals, string interpolation, comprehensions, and related conveniences.

### Typecheck

HM-style inference with traits, effects, exhaustiveness checking, and
multi-module import processing.

This phase includes a real front-end name-resolution pass in
`src/typechecker/resolve.rs`. The important current contract is:

- imports are processed first and global scope is built
- `resolve_names` records semantic identity in `ResolutionResult`
- type inference consumes that resolution result
- the AST stays mostly source-shaped; in-place canonical string rewriting is no
  longer the primary contract

So the typechecker does **not** primarily mean “rewrite the AST to canonical
names and hope later phases agree.” It means “produce explicit semantic
resolution keyed by source identity, then typecheck against that.”

For the typechecker pipeline in more detail, including rough pass counts, see
`docs/typechecking.md`.

For the resolver architecture specifically, see `docs/name-resolution.md`.

Key outputs:

- `CheckResult`
  - type environment
  - diagnostics
  - trait/effect/handler metadata
  - `ResolutionResult`
  - per-node type information
  - module codegen metadata
- per-module `CheckResult`s for imported modules
- `ModuleCodegenInfo` per module
- prelude imports used later by codegen

### Elaborate

Transforms trait method calls into explicit dictionary passing. Runs per module.
Takes the parsed program plus `CheckResult`, and produces a new program with:

- `DictConstructor` declarations replacing `ImplDef`
- `DictRef` and `DictMethodAccess` expressions replacing trait method calls
- `ForeignCall` expressions for `@external` functions
- explicit dictionary parameters on functions with `where` clauses

Elaboration now preserves source identity more carefully than before, so later
phases can keep using front-end semantic metadata where the expression is still
semantically the same source node.

### Normalize

Effect normalization pre-pass. Prepares the elaborated AST for the CPS-aware
lowerer.

### Backend Resolve (`src/codegen/resolve.rs`)

This phase is now a **backend-oriented projection layer**, not a second
general-purpose source resolver.

It produces:

- `ConstructorAtoms`
  - constructor name -> mangled Erlang atom
- `ResolutionMap`
  - `NodeId -> ResolvedName` for callable/backend dispatch decisions

The backend resolver uses front-end `ResolutionResult` and codegen metadata to
answer lowering-specific questions such as:

- is this callable local, imported, or external?
- what Erlang module/function should be called?
- what arity/effect metadata should lowering use?

What it is **not** supposed to do anymore:

- re-decide the meaning of ordinary source `Var` or `QualifiedName` nodes from
  raw spelling
- paper over missing front-end semantic resolution for ordinary source nodes

### Lower (`src/codegen/lower/`)

Converts the normalized AST into Core Erlang (`CModule`).

This phase is responsible for:

- CPS transformation for algebraic effects
- handler lowering and inlining
- saturated vs partial application detection
- handler parameter / return continuation threading
- runtime-specific data layout and call shaping

The lowerer consumes two different semantic layers:

- front-end `ResolutionResult`
  - source-level semantic identity
  - handlers, effect-call qualifiers, handler-arm qualifiers, record type
    identity, value identity
- backend `ResolutionMap`
  - callable/backend dispatch identity
  - local vs imported vs external fun decisions
  - arity/effect metadata needed for lowering

That split is intentional:

- front-end resolution answers “what source declaration does this node mean?”
- backend resolution answers “how should this callable lower on the BEAM side?”

### Emit

Pretty-prints Core Erlang to a `.core` file. Then `erlc` compiles it to `.beam`
and `erl` runs it.

## Data Flow: `CheckResult`

`CheckResult` is the main semantic product of the front end.

Important data used downstream includes:

- `env`
- `traits`
- `effects`
- `handlers`
- `type_at_node`
- `let_effect_bindings`
- `prelude_imports`
- `resolution`
- module codegen info and per-module check results

`scope_map` still exists, but it is now mainly:

- import/global scope construction state
- a diagnostics/tooling helper
- support for a few narrower specialized lookups

It is no longer the main semantic lookup path for lowering ordinary source
nodes.

## Data Flow: `CompiledModule`

Per-module codegen results are bundled into `CompiledModule`:

```rust
struct CompiledModule {
    codegen_info: ModuleCodegenInfo,
    elaborated: Program,
    resolution: ResolutionMap,
    front_resolution: ResolutionResult,
}
```

`CodegenContext` carries:

- `modules: HashMap<String, CompiledModule>`
- `prelude_imports`
- `let_effect_bindings`

This is the cross-module semantic bundle the lowerer uses for imported modules.

## Build Orchestration (`src/cli/build.rs`)

### Single file (`saga run file.saga`)

1. Parse + typecheck the entry file
2. Typecheck/load stdlib modules
3. Compile imported modules to `CompiledModule`
4. Elaborate + normalize the user module
5. Run backend resolve + lower + emit with `emit_module_with_context(...)`
6. Compile `.core` with `erlc` and run with `erl`

### Project (`saga build`)

Same general shape, but repeated across project modules plus `Main`. Modules are
typechecked first, then compiled into `CompiledModule` bundles that carry both
front-end and backend resolution data.

### Test (`saga test`)

Builds the project first, then compiles each test module through the same
checked pipeline, reusing compiled module context where possible.
