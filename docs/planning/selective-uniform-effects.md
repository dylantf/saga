# Selective-Uniform Effects

Status: **experiment charter / next-branch plan**.

This document sketches the next backend experiment after the
`uniform-effect-translation` branch.

Working name: **selective-uniform**.

Implementation state and session handoff notes live in
`docs/planning/selective-uniform-implementation-log.md`.

## Thesis

The old selective-CPS backend failed because runtime call-shape knowledge was
distributed and incomplete. Too many lowering paths guessed whether a callable
needed ordinary arguments or ordinary arguments plus hidden evidence and return
continuation parameters.

The uniform rewrite fixed that bug class by giving every Saga function one
runtime shape:

```text
(user_args..., _Evidence, _ReturnK)
```

That was correct, but too expensive on the BEAM. It also made trait and handler
specialization much harder because every optimization had to work after the
program had already been turned into effect-shaped control plumbing.

The next experiment should make the **metadata uniform**, not the **runtime
ABI**.

In other words:

- every callable has one authoritative runtime-shape classification;
- every call site must use that classification;
- closed pure code stays direct BEAM code;
- trait/dictionary specialization has its own phase before effect lowering;
- only effectful, effect-polymorphic, or handler-control code enters the
  CPS/evidence path;
- monadic IR is an implementation tool for CPS-shaped regions, not the
  whole-program backend language;
- adapters are explicit at boundaries where runtime shapes differ.

## Updated Diagnosis

The benchmark data does not say that every part of the uniform branch is
catastrophic.

It suggests two separate costs:

| Comparison | Result |
| --- | ---: |
| `main` options argument -> uniform options argument | roughly `1.45x` slower |
| `main` fast string path -> uniform fast string path | roughly `1.55x` slower |
| `main` effect options -> uniform effect options | roughly `13-15x` slower |
| uniform options argument -> uniform effect options | roughly `10x` slower |

So the uniform ABI creates a real baseline tax, but the branch-killing failure
is narrower: simple effect-scoped configuration reads go through the full
general handler/evidence/resume protocol.

On `main`, passing JSON encode options through an effect is only modestly slower
than passing the options as an ordinary argument. There is no large optimizer
there; the old selective-CPS code is simply a much smaller CPS island.

On the uniform branch, the optimizer can reduce syntactic `Yield` counts, but
the emitted code can still retain expensive surrounding machinery:

- CPS-shaped function and dictionary calls;
- continuation closures;
- marked value-result and abort routing tuples;
- result delimiter reconstruction;
- evidence lookup and handler tuple dispatch;
- generated variants and cloned helpers.

This means residual `Yield` count is not enough. A successful next design must
avoid making simple code complicated in the first place.

## Core Principle: Shape Is The Safety Blanket

The correctness blanket from the uniform branch should not be "everything is
CPS-shaped." It should be "no call site decides arity locally."

Introduce one backend-facing runtime-shape API, built from existing
typechecker, elaboration, and resolution metadata.

Sketch:

```rust
enum RuntimeCallShape {
    Direct {
        arity: usize,
    },
    Cps {
        user_arity: usize,
        effects: Vec<String>,
        open_row: bool,
    },
    External {
        arity: usize,
        callback_adapters: Vec<CallbackShape>,
    },
    Intrinsic {
        arity: usize,
    },
    DictConstructor {
        user_arity: usize,
        result_shape: DictShape,
    },
    DictMethod {
        user_arity: usize,
        method_shape: Box<RuntimeCallShape>,
    },
}
```

This does not need to be the final spelling. The invariant is the important
part: lowering does not rediscover call shape from names, source arity, or
one-off type lookups.

Sources of truth should include:

- `ResolvedCodegenKind::{BeamFunction, ExternalFunction, Intrinsic}`;
- `ModuleCodegenInfo::fun_effects`;
- `EffectInfo::type_at_node`;
- `EffectInfo::let_effect_bindings`;
- trait and dictionary metadata from elaboration;
- handler/effect metadata for dynamic handler values;
- external function signatures for callback adapter generation.

Any missing, unknown, or contradictory shape should be a compiler error or
backend panic with a useful diagnostic. It should not silently guess and produce
runtime arity mismatches.

## Proposed Pipeline

The next backend experiment should be direct-first:

```text
Parse
-> Typecheck
-> Elaborate traits to explicit dictionaries
-> Backend resolution
-> Runtime shape classification
-> Trait/dictionary specialization
-> Lower:
     direct path for direct code
     monadic/CPS path for CPS-shaped code
-> small cleanup passes only after correctness works
-> Core Erlang
```

The architecture to avoid is:

```text
Parse
-> Typecheck / Elaborate
-> uniform monadic CPS for everything
-> large optimizer tries to rediscover direct code
-> Core Erlang
```

The first goal is boring code for boring programs. A closed empty-effect
function should not enter monadic IR just because the compiler supports effects
elsewhere.

## Shape-Directed Calls

Every call is emitted through one shape-aware helper. Raw Core Erlang apply/call
construction should be private to that helper or a very small set of helpers.

Call behavior is shape-directed:

- `Direct -> Direct`: ordinary call.
- `Cps -> Cps`: pass evidence and return continuation.
- `Cps -> Direct`: ordinary call, then continue with the direct result.
- `Direct -> Cps`: require an explicit boundary adapter or an enclosing context
  that can provide evidence and a continuation.
- `External` with function-typed parameters: wrap Saga callback values into
  native-arity Erlang callbacks where needed.
- `Intrinsic`: lower through the intrinsic path.

The old arity-mismatch bug class should be caught here. If a lowering path has
only a source name and a source argument count, it does not have enough
information to emit a call.

## Trait Specialization Has Its Own Slot

Traits make Saga harder than languages without typeclasses. The uniform branch
made trait specialization especially painful because dictionary calls were
optimized after they had already been wrapped in effect-shaped IR.

Trait specialization should be separate from effect optimization.

After elaboration, trait calls are explicit dictionary operations:

```text
fun f : a -> String where {a: Show}
f x = show x

-- conceptual elaboration
f __dict_Show_a x =
  element(Show.show_index, __dict_Show_a)(x)
```

The trait/dictionary specialization phase should run while the program still
looks like ordinary calls, dictionary constructors, method accesses, tuples, and
lambdas. It should not have to understand handler evidence, result markers, or
continuation routing.

Initial specialization targets:

- inline known zero-argument dictionary constructors;
- inline known method lambdas from concrete dictionaries;
- specialize generic functions by statically known dictionary arguments;
- drop dictionary parameters that become unused after specialization;
- specialize parameterized dictionary constructors when all required sub-dicts
  are known;
- keep unknown dictionary parameters as normal runtime values.

Dictionary constructors and dictionary methods have runtime shapes too. A trait
method should not be treated as an arbitrary function value when the compiler
knows which trait slot it came from and what shape that method has.

The desired ordering is:

```text
trait elaboration
-> runtime shape classification
-> dictionary partial evaluation / specialization
-> update/recheck shapes for generated specialized callables
-> direct or CPS lowering
```

This gives trait performance a clean place to live and keeps the monadic IR
focused on effect control.

## Lowering Strategy

Default to direct style.

- Closed empty-effect functions lower as ordinary BEAM functions of arity `N`.
- Intrinsics lower through their intrinsic path.
- Externals lower directly or through wrappers only when needed.
- Effectful or open-row functions lower as CPS/evidence functions of arity
  `N + 2`.
- Handler bodies and resumptions may use monadic/CPS machinery internally, but
  that does not force unrelated functions into CPS shape.

Direct functions can still be called from CPS functions. The CPS lowerer calls
the direct function normally, binds the result, and resumes the current
continuation.

The reverse direction must be explicit. A direct function calling a CPS function
needs a boundary adapter, a handler context, or a compile-time error. There
should be no silent "maybe add two hidden args" fallback.

## Role Of Monadic IR

Keep a monadic IR, but make it smaller and later.

The monadic IR is useful for code that truly has effect-control semantics:

- effectful function bodies;
- effect-polymorphic function bodies;
- handler bodies and resumptions;
- value-producing `resume`;
- aborting handlers;
- handler `return` clauses;
- `finally` cleanup;
- dynamic handler values;
- multishot continuations.

It should not be the compiler's universal assembly language. Pure functions and
closed pure helpers should bypass it.

A small starting shape is enough:

```rust
enum MExpr {
    Pure(Atom),
    Let(String, Atom, Box<MExpr>),
    Bind(Box<MExpr>, String, Box<MExpr>),
    App {
        callee: Atom,
        args: Vec<Atom>,
    },
    Yield {
        effect: EffectId,
        op: OpId,
        args: Vec<Atom>,
    },
    With {
        body: Box<MExpr>,
        handler: HandlerExpr,
    },
    Resume(Atom),
}
```

`Pure(Atom)` means the effectful computation has produced an ordinary value. It
does not mean the enclosing Saga function is direct; it is the "return this
value to the current continuation" node inside CPS-shaped lowering.

The first monadic path can be slow. It is a correctness baseline for genuinely
effectful code, not the performance story for pure code.

## Final Pipeline Shape: Analysis Facts, Then Selective Lowering

The finished architecture should separate **analysis order** from **rewrite
order**.

Trait specialization wants effect facts: a dictionary method body may become
direct only after known handlers erase its effects. Static handler
specialization wants ordinary call/dictionary facts: an effect operation may be
inside a known impl method or helper. If either phase must globally rewrite the
program before the other can run, the pipeline becomes circular.

The intended shape is:

```text
elaborated / ANF program
  |
  |-- monadic/effect analysis side-chain
  |     - handler-arm resume classification
  |     - static tail-resumptive operation facts
  |     - net-direct / net-pure function facts under known handlers
  |     - handler factory / config-handler facts where bounded and static
  |     - optional stats/debug snapshots
  |
  `-- selective lowering and specialization
        - direct lowering for closed pure code
        - trait/dictionary specialization at known call sites
        - CPS islands only where effect control is actually required
        - local static-handler direct-call inside those islands
        - explicit adapters at direct/CPS boundaries
```

In this model, monadic IR is allowed to exist as an **analysis substrate** even
when it is not the final program being lowered wholesale. The compiler can
translate a body or region to monadic form, run bounded analyses or rewrites on
a clone, and cache facts for the selective lowerer.

Examples of facts the selective lowerer can consume:

```text
Function f is operationally direct under handler set H.
Effect op E.read is statically handled by tail-resumptive arm A at this site.
Dictionary method ToJson.to_json for concrete impl I is net-direct here.
Handler factory make_options_handler arg produces static handler H.
```

Those facts guide call-site choices, but the slow/correct fallback remains the
runtime shape classification. If no fact exists, the lowerer emits the generic
direct or CPS shape dictated by the type and runtime-shape metadata.

For the first implementation, do not build the full fact engine. Start with a
local version inside selective CPS islands: when lowering `With`, keep a static
handler frame stack; when lowering `Yield`, use the existing handler analysis to
direct-call a matching tail-resumptive arm if the rewrite is conservative. This
proves the effect-specialization path without committing to whole-program
trait specialization yet.

## Static Handler Specialization Comes After Baseline

Static tail-resumptive handlers are important, especially Reader/config-style
handlers:

```saga
get_json_options () = resume options
```

Eventually, a statically matched operation under this handler should compile to
the captured value, or to the smallest equivalent direct continuation step:

```saga
get_json_options! ()  ==>  options
```

But this should not be the first effect implementation. First build:

1. direct pure lowering;
2. runtime shape classification;
3. shape-directed calls;
4. a minimal slow CPS/evidence path for effectful code.

Then add static tail-resumptive handler specialization as the first performance
rewrite. That keeps it optional and testable against the slow path.

This specialization is not valid for every handler. For example:

```saga
get () = fun s -> (resume s) s
```

is value-producing/state-threading resume and still needs proper delimited
continuation semantics. Multishot, non-tail resume, `finally`, dynamic handler
values, aborting handlers, and unknown handler factories should stay on the
general path until a specific safe rewrite exists.

## Reuse From The Uniform Branch

Keep or port these pieces where practical:

- `RuntimeFunctionShape` / `runtime_shape.rs`, expanded into the authoritative
  call-shape layer;
- imported effect-op metadata (`EffectInfo::effect_ops`);
- dynamic handler metadata for handler values and handler refs;
- `@external` wrapper/callback adapter design;
- value-producing resume tests and semantics;
- abort/result marker routing lessons;
- finally/cleanup regression tests;
- anonymous-record structural metadata fixes;
- monadic/stat inspection tooling;
- real-package shakedown fixtures and habits.

Do not port the full uniform ABI by default. Do not port the uniform optimizer
as a prerequisite for basic performance.

## Initial Spike Scope

This is a timeboxed experiment, not a second full rewrite.

Target duration: **1-2 focused days** for the first vertical slice.

Fixtures:

1. Pure function calls pure function.
2. Pure caller invokes an effectful function under a handler.
3. Effectful caller invokes a pure helper.
4. Higher-order callback through a stdlib/external function.
5. One trait/dictionary method call.
6. Statically known reader/config handler:
   `get () = resume captured_value`.

Recommended order:

1. Start a new lowerer and freeze the old one as salvage/reference material.
2. Rebuild the direct-style lowerer for pure Saga.
3. Add runtime shape classification and make all calls go through it.
4. Add minimal trait/dictionary support in the direct path.
5. Add a minimal slow CPS/evidence path for one simple effect.
6. Add static tail-resumptive specialization after the slow path works.

Do not port the uniform optimizer for the first spike. The point is to measure
whether direct-first lowering produces reasonable baseline code before
interprocedural heroics.

## Success Criteria

Continue only if the spike shows clear promise:

- pure/options-argument style code is close to `main` performance;
- effect-options code is not an order of magnitude slower before large
  optimization;
- the old arity-mismatch class is caught by call-shape assertions;
- trait method calls have a clean specialization slot outside effect lowering;
- the implementation delta stays in the low thousands of lines, not tens of
  thousands;
- fixtures and at least one real-package shakedown pass.

Stop or redesign if basic cases require:

- large interprocedural partial evaluation;
- cross-module dictionary cloning just to recover normal direct calls;
- dynamic handler specialization to make ordinary code acceptable;
- widespread name-based or arity-guessing fallbacks;
- making the whole program monadic before simple code runs.

## Questions To Answer Early

1. Can direct and CPS function values coexist without making partial application
   fragile?
2. Where should shape metadata live for let-bound function values and lambdas?
3. Do trait dictionaries store direct method closures, CPS method closures, or
   shape-tagged method entries?
4. How should dictionary specialization key generated functions without
   recreating the uniform branch's generated-variant machinery?
5. How do open effect rows appear after elaboration, and can they be made
   explicit enough for lowering?
6. What is the minimal adapter set needed for higher-order functions?
7. Can imported module metadata provide enough shape information without
   recompiling or specializing the callee module?

## Relationship To Main And Uniform Branch

`main` remains the stable working compiler.

The `uniform-effect-translation` branch is a research branch and source of
salvageable fixes/tests/docs.

The selective-uniform experiment should branch from the uniform branch if the
goal is to reuse the learned machinery quickly. If the goal is a clean final PR,
the successful pieces can later be replayed onto `main` in smaller commits.

## Non-Goals For The First Spike

- Full optimizer parity with the uniform branch.
- Whole-program trait specialization.
- Dynamic handler performance work.
- Cross-module generated variants.
- Perfect Core Erlang output.
- Removing every old selective-CPS mechanism on day one.

The first question is simpler: can the backend have uniform call-shape knowledge
while preserving direct BEAM code for the common case?
