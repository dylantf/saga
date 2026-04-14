# Imported Handler Origin Context

## Status

Step 1 from the refactor path below is done: `current_handler_source_module` and
`HandlerInfo.source_module` now carry source-module identity through imported
handler lowering, and local function calls and constructor lookups route through
that. The original bug (imported handlers losing source-module identity) is fixed
and tested.

Steps 2 and 3 are still open. Constructor atoms are still handled by
`push_source_module_ctor_aliases` / `pop_source_module_ctor_aliases`, which
temporarily mutates the shared `constructor_atoms` map and restores it afterward.
That is the save/restore-of-shared-mutable-state pattern that this doc proposes
replacing with origin-aware helpers like `ctor_atom_for(name, origin_module)`.

The current approach works and is tested, but the underlying design smell remains:
if another dimension of cross-module lowering is added, the same class of bug
could recur.

## Summary

We hit a subtle lowering bug when a handler defined in one module was imported and inlined into another.

The short version:

- same-file handler code worked
- the same handler moved into stdlib broke
- local helper functions and private constructors inside the imported handler body were lowered as if they belonged to the destination module instead of the source module

This showed up most clearly in `Std.AtomicRef.atomic_ref`, where:

- `lock_server` is a top-level helper defined in `Std.AtomicRef`
- `Acquire`, `Acquired`, `AtomicMutRef`, `Release`, and `Stop` are private constructors from `Std.AtomicRef`
- when the handler was imported into user code, those references partially lost source-module identity during lowering

That produced failures like:

- wrong arity/effect lookup for imported local function refs
- cross-module calls to private helpers
- constructor tag mismatches like sending `{'Acquire', ...}` to a process expecting `{'std_atomicref_Acquire', ...}`
- pattern mismatches like constructing `{'std_atomicref_AtomicMutRef', ...}` but matching on `{'AtomicMutRef', ...}`

## What This Suggests

The direct bug was subtle, but it exposed a real code smell:

- imported code is lowered out-of-module
- source-module identity is preserved through several separate mechanisms
- those mechanisms can drift apart

Today, module-sensitive lowering depends on a mix of:

- resolved function metadata
- handler source-module tracking
- constructor atom tables
- canonical name lookup
- temporary contextual overrides

That is workable, but fragile. It lets one dimension stay source-aware while another silently falls back to the current emitted module.

## Concrete Symptom Pattern

The compiler effectively had two notions of "current module":

1. the module currently being emitted as Core Erlang / BEAM
2. the module the current AST fragment semantically belongs to

Those are the same for normal module-local lowering, but not for imported handler bodies.

For imported handlers, we were missing a single first-class representation of:

- "this code is being emitted inside module `User.Main`"
- "but this code fragment originates from `Std.AtomicRef`"

Without that explicit distinction, the lowerer had to reconstruct origin ad hoc.

## Suggested Direction

Introduce an explicit origin-aware lowering context.

For example:

- `current_emit_module`: the Erlang module being generated
- `current_origin_module`: the Saga module this AST fragment belongs to

Then route all module-sensitive lowering decisions through that context.

That includes at least:

- local function refs/calls
- constructor atom lookup
- pattern constructor lowering
- imported handler body lowering
- imported handler return-clause lowering
- any other canonical/source-module lookup done during lowering

## Why This Is Better

It replaces:

- "lowering mostly assumes the current module, with special cases"

with:

- "lowering always knows the semantic origin of the code fragment it is lowering"

That should make imported handlers behave like source-module code by construction rather than by patching separate tables.

## Small Practical Refactor Path

### Step 1

Create a small origin context and thread it through imported handler lowering.

Something like:

```rust
struct OriginContext {
    saga_module: String,
}
```

Use it first in:

- `build_op_handler_fun`
- `build_return_lambda`
- constructor lookup helpers
- local function target lookup helpers

### Step 2

Replace temporary constructor alias patching with origin-aware helper methods.

For example:

- `ctor_atom_for(name, origin_module)`
- `local_fun_target(name, origin_module)`

so `lower_ctor` and `lower_pat` no longer depend on mutating a shared global constructor map.

### Step 3

Keep pushing canonical/source identity into resolved forms.

`ResolvedName::LocalFun` already benefits from carrying:

- source module
- canonical name

That same principle should apply anywhere lowering might otherwise need to guess where a node came from.

## Design Smell, Not Design Failure

This does not necessarily mean the compiler architecture is bad.

It means there is one concept that deserves to be first-class and currently is not:

- the semantic origin module of the code currently being lowered

Once that becomes explicit, imported handler lowering should get simpler and much less bug-prone.

## Good Test Cases

Any future refactor here should keep regression coverage for:

- same-file handler with local helper function
- imported handler with local helper function
- imported handler using private constructors in expressions
- imported handler using private constructors in parameter patterns
- imported handler with effectful local helper function
- imported handler spawning a local helper function
- imported handler using return clauses and `finally`

`Std.AtomicRef` is a strong real-world regression target because it exercises:

- imported handler inlining
- helper-function calls
- private constructors
- actor/process effects
- nested `with beam_actor`
- pattern matching and message passing
