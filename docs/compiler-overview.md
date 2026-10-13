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
  -> Generic fold (src/codegen/generic_fold/)
  -> Backend Resolve (src/codegen/resolve.rs)
  -> Optimization Facts (src/codegen/optimize.rs)
  -> Lower (src/codegen/lower/)
     begins by populating CallEffectMap (src/codegen/call_effects.rs),
     then normalizes each body (src/codegen/normalize.rs)
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

For module loading, import surfaces, re-exports, and cyclic-import SCC handling,
see `docs/module-system.md`.

For the resolver architecture specifically, see `docs/name-resolution.md`.

Key outputs:

- `CheckResult`
  - type environment
  - diagnostics
  - trait/effect/handler metadata
  - `ResolutionResult`
  - per-node type information
  - module codegen metadata
  - trait method effect signatures and per-impl/per-method effect facts
- per-module `CheckResult`s for imported modules
- `ModuleCodegenInfo` per module
- prelude imports used later by codegen

Trait methods define their effect capability. A pure trait method admits only
pure impl methods; a closed `needs {Config}` method admits impl methods whose
body effects stay within that named row; an open `needs {..e}` method admits
impl-specific effects. For generic callers of open-row trait methods, the
constraint's unknown effects surface as the constrained type variable's row
tail, e.g. `needs {..a} where {a: Foo}`. Concrete trait dispatch can use the
selected impl's per-method effect facts.

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

Value-normal form. It runs inside lowering, once the call plan is frozen
(`normalize_body`, called from `src/codegen/lower/anf.rs` for each body the
lowerer starts on: function clauses and guards, dictionary methods, handler
arms and return clauses, `finally` blocks, inlined helpers and handler arms).
It is the only normalize run; the generic fold runs before it, on the
elaborated program.

After it every operand is a value: a name, literal, lambda, handler value or
operation reference, a projection out of a value, or data (tuple, record,
constructor or dictionary application) built only from values
(`effect_position::is_value`). Everything that computes is lifted out of
operand position into a `let` of its own, in evaluation order: every call
(pure ones too), operator, record update, bit string, `resume`, `with`, and
every `if`/`case`/block/`do`/`receive`. Such an expression is then the value
of a block-level `let`/statement or is in tail position, and nowhere else.
Record fields are lifted in the order written. The variable replacing a
lifted expression keeps the expression's `NodeId`, and an application chain
keeps its `App` nodes, so types and the call plan are still found.
Conditionally evaluated parts (`if`/`case` branches, lambda bodies, handler
arms) are separate scopes.

Two forms are special. `a && b` / `a || b` keeps its operator when the right
operand is a value and otherwise becomes an `if`, since the right operand may
not be evaluated ahead of the operator. A guard that is a BEAM guard
expression (`effect_position::is_guard_safe`: operators over variables and
literals) is left exactly as written, because it is emitted as a guard; any
other guard is a body of its own.

The rule and the check that it holds are in
`src/codegen/effect_position.rs`. A body that already satisfies the rule is
lowered untouched; a violation left after normalizing is an internal compiler
error, and so is a non-value operand met while lowering (`Lowerer::operand`,
the one place the back-end tree's operands are made).
Facts the lowerer used to read off the tree's shape (whether an untyped
lambda is a tagged closure, whether a dictionary method performs an operation
directly) are recorded in the plan before this runs.

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

### Optimization Facts (`src/codegen/optimize.rs`)

The optimizer is metadata-first. It runs after backend resolve and before
lowering, recording optional facts that the lowerer may use for narrow fast
paths. Missing facts must preserve the normal direct-first lowering behavior.

Current fact families include:

- handler-arm resumption analysis in `src/codegen/handler_analysis.rs`
- same-module/imported helper facts used for static handler variants
- direct higher-order-function specializations for externally-direct callbacks

Optimization facts are proof inputs, not a second lowered IR. The lowerer
remains the only Core Erlang emitter.

### Call Classification (`src/codegen/call_effects.rs`)

At the start of module lowering, the lowerer populates a `CallEffectMap` by
walking the elaborated program and writing one `CallEffectInfo` entry per `App`
node. This is the single place that decides the runtime call shape:

- `Pure` -- direct call, no evidence, no return continuation
- `StaticOps` -- closed-row CPS call with a known static effect set
- `RowForwarded` -- open-row CPS call that forwards caller evidence

A call to a known function is classified from the callee's declared ABI. Any
other call goes through a function value and is classified from the head's
own type: it is a CPS call when an arrow consumed by the supplied arguments
carries effects or an open row.

There is no default. A call is pure only by a rule that says so: an applied
operation (a perform, lowered separately), a constructor or dictionary
constructor, an intrinsic, a known function whose signature has no effects, a
dictionary method whose declared signature has none, a head whose recorded
type is a pure function, or a lambda made after typechecking whose body
performs nothing. A head none of the rules covers is an internal compiler
error naming the head, the function and the location; so is a call node the
lowerer meets that has no entry.

Types are read by `NodeId`. A node the generic fold copies has a fresh id;
the fold's `NodeOrigins` map takes it back to the node the typechecker saw,
in whichever module that was, and every node-keyed table is read through it
(`Populator::node_type`, `Lowerer::origin`). A variable the fold puts in
place of a parameter keeps the parameter occurrence's origin.

The rest of lowering consumes this map. It should not rediscover call effect
shape from raw syntax.

### Lower (`src/codegen/lower/`)

Converts the normalized AST into Core Erlang (`CModule`).

This phase is responsible for:

- consuming `CallEffectInfo` and optimizer facts
- CPS transformation for algebraic effects when the classified shape requires it
- handler lowering and inlining
- representing function values from their own type: a bare fun when pure, a
  tagged CPS closure `{'$saga_cps', Fun}` when effectful (`lower/tagged.rs`);
  there is no planning pass or adapter between the two
- saturated vs partial application detection
- handler parameter / return continuation threading, by two rules over
  effect-normal bodies: `lower_tail` (pass the continuation on) and
  `lower_block` (`let x = e; rest` gives `e` the continuation `fun x -> rest`).
  See "One rule for where effects go" in `docs/effect-implementation.md`
- direct fast paths proven by optimizer facts
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
- `type_at_node`, `expr_types`
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
- imported modules' optimization facts

This is the cross-module semantic bundle the lowerer uses for imported modules.

## Build Orchestration (`src/cli/build.rs`)

### Single file (`saga run file.saga`)

1. Parse + typecheck the entry file
2. Typecheck/load stdlib modules
3. Compile imported modules to `CompiledModule`
4. Elaborate + normalize the user module
5. Run backend resolve, collect optimizer facts, lower (including call
   classification), and emit with `emit_module_with_context(...)`
6. Compile `.core` with `erlc` and run with `erl`

### Project (`saga build`)

Same general shape, but repeated across project modules plus `Main`. Modules are
typechecked first, then compiled into `CompiledModule` bundles that carry both
front-end and backend resolution data.

### Test (`saga test`)

Builds the project first, then compiles each test module through the same
checked pipeline, reusing compiled module context where possible.
