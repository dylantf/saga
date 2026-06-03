# Selective-Uniform Implementation Log

This is the durable working memory for the selective-uniform backend
experiment. Update it at the end of every session that changes the design,
code, tests, or known state.

The charter is `docs/planning/selective-uniform-effects.md`.

The CPS callable value checklist is
`docs/planning/selective-cps-value-matrix.md`.

## Current Frontier

Re-establish a direct-first lowerer without trusting the old uniform CPS ABI as
the runtime default.

The first implementation slice is:

1. keep the existing uniform lowerer frozen as reference/salvage material;
2. use or replace the existing experimental `src/codegen/lower_selective.rs`
   only after auditing it;
3. get a tiny pure program lowering through `saga inspect --stage
   selective-core`;
4. make all direct call emission go through runtime-shape checks before adding
   more language features;
5. decide whether pure direct lowering should continue using monadic IR as a
   temporary scaffold or move earlier to elaborated/ANF AST.

## Hard Invariants

- No call site may decide runtime arity from source arity alone.
- Closed pure functions should lower as direct BEAM functions of arity `N`.
- CPS/evidence shape is for effectful, effect-polymorphic, or handler-control
  code, not for the whole program.
- Trait/dictionary specialization belongs before effect lowering, while the
  program still looks like calls, dictionaries, tuples, and lambdas.
- Monadic IR is allowed inside CPS-shaped regions. It is not the universal
  backend language.
- Current `selective-core` tests still build monadic IR before calling
  `lower_selective`. That is a scaffold, not the intended final architecture.
  The eventual split should point monadic IR only at CPS-shaped bodies/regions.
- Static tail-resumptive handler specialization is a later performance rewrite,
  tested against a slow correctness path.
- Direct HOF specialization should run before pure-to-CPS adapter fallback:
  an effectful callback parameter is a capability bound, not a demand that the
  actual callback leaks effects. Pure or fully-handled callbacks should be able
  to pick a direct/pure specialization when the call is statically net-pure.
- Reader/config-like effects are the same specialization family. A static
  handler such as `read_options () = resume options` should eventually lower to
  an explicit config argument or be inlined, rather than permanently paying the
  generic CPS/evidence path.

## Salvage Candidates

- `src/codegen/runtime_shape.rs`: existing `RuntimeFunctionShape` /
  `CpsShape` extraction. Needs expansion from `Pure/Cps/Intrinsic` into the
  authoritative call-shape layer described by the charter.
- `src/codegen/lower_selective.rs`: existing experimental direct lowerer wired
  to `inspect --stage selective-core`. Treat as scratch until audited.
- `src/codegen/monadic/stats.rs`: useful structural counters for binds, yields,
  apps, handlers, generated declarations, and reachable roots. Port or adapt
  once the new path has its own IR/stats boundary.
- `src/cli/commands.rs`: `monadic-stats` and `selective-core` inspect stages
  already exist.
- Uniform branch tests for value-producing resume, abort/result markers,
  finally cleanup, external callback adapters, dynamic handler metadata, and
  anonymous-record metadata.

## Latest Working Fixtures

- `examples/optimization/selective-uniform/01-pure-direct.saga`
  - Command:
    `cargo run --bin saga -- inspect examples/optimization/selective-uniform/01-pure-direct.saga --stage selective-core`
  - Current result: emits direct Core Erlang for `add1/1`, `twice/1`, and
    `main/1`.
  - This proves only the tiny direct subset: variable params, `Unit` param,
    integer literal, binary `+`, local direct function calls, ANF bind.
- `examples/optimization/selective-uniform/02-recursive-if.saga`
  - Current result: emits direct Core Erlang for a recursive pure function with
    `if`, comparison, subtraction, addition, and recursive self-call.
- `examples/optimization/selective-uniform/03-pure-val.saga`
  - Current result: emits direct Core Erlang for a pure top-level `val`, a pure
    function, and a call that passes the val to the function.
- `examples/optimization/selective-uniform/04-print-stdout.saga`
  - Current result: emits direct Core Erlang for `Std.IO.Unsafe.print_stdout`
    by lowering to `io:format` and returning `unit`.
- `examples/optimization/selective-uniform/05-trait-show.saga`
  - Current result: emits direct Core Erlang for `show 42` as:
    imported `Show Int` dictionary constructor call, `erlang:element(1, dict)`,
    and direct method closure application.
- `examples/optimization/selective-uniform/06-dbg.saga`
  - Current result: emits direct Core Erlang for `dbg 42` as:
    imported `Debug Int` dictionary constructor call, method extraction,
    direct method closure application, stderr `io:format`, and `unit`.
- `examples/optimization/selective-uniform/07-record-field.saga`
  - Current result: emits direct Core Erlang for named record construction and
    field access via `erlang:element`.
- `examples/optimization/selective-uniform/08-tuple-param.saga`
  - Current result: emits a direct `/1` function whose non-variable source
    parameter is checked with an internal `case`, preserving direct arity while
    supporting tuple destructuring.
- `examples/optimization/selective-uniform/09-constructor-case.saga`
  - Current result: emits direct Core Erlang for local ADT construction and
    constructor-pattern case arms.
- `examples/optimization/selective-uniform/10-imported-pure.saga`
  - Current result: emits a remote direct call to imported pure stdlib
    functions such as `Std.Maybe.is_just`.
- `examples/optimization/selective-uniform/imported-pure-project/`
  - Created with `saga new` and stripped of its nested `.git`.
  - Current result: running `saga inspect src/Main.saga --stage selective-core`
    from the project root typechecks a user-module import and emits remote
    direct calls to `helper:inc/1` and `helper:pick/1`.
- `examples/optimization/selective-uniform/11-effect-boundary.saga`
  - Current result: emits the first tiny CPS island shape for public
    `do_log/3`: source params plus `_Evidence` and `_ReturnK`, evidence lookup
    through `std_evidence_bridge:find_evidence`, operation selection through
    `erlang:element`, and a tail call to the selected operation closure.
- `examples/optimization/selective-uniform/12-effect-row-direct-body.saga`
  - Current result: emits compiler-private direct entries
    `__saga_direct_may_log/1` / `__saga_direct_use_may_log/1` plus source-name
    CPS adapters `may_log/3` / `use_may_log/3` for functions whose types declare
    `needs {Log}` but whose implementations are operationally direct. Direct
    code calls the compiler-private direct entry, while CPS-compatible entries
    stay under the source name for future island calls. Public direct-body
    CPS-typed functions currently export both entries so future cross-module
    direct code has a callable direct ABI. The typechecker correctly warns when
    a declared effect is entirely unused.
- `examples/optimization/selective-uniform/imported-effect-row-project/`
  - Current result: inspecting `src/Effects.saga` emits a public CPS adapter
    export (`may_log/3`) plus the compiler-private direct entry
    `__saga_direct_may_log/1`. Inspecting `src/Main.saga` lowers
    `call_may_log/1` as a direct-body effect-row function that calls the
    imported direct entry `effects:__saga_direct_may_log/1`, plus its own
    `call_may_log/3` adapter. This is still a shape check rather than a
    cross-module BEAM check because `inspect` prints source module names for
    the provider module while resolved remote calls use runtime Erlang module
    atoms.
- `examples/optimization/selective-uniform/13-simple-yield-cps-island.saga`
  - Current result: pins the same minimal effect-operation island in a focused
    fixture. `do_log/3` is emitted under the source name with no
    `__saga_direct_do_log` entry because its body is operationally CPS, not
    direct.
- `examples/optimization/selective-uniform/14-yield-then-return-cps-island.saga`
  - Current result: emits a CPS island that performs `log! "hello"`, passes a
    generated continuation closure to the operation, binds the resumed result,
    and then calls `_ReturnK(42)`.
- `examples/optimization/selective-uniform/15-yield-result-used-cps-island.saga`
  - Current result: emits a CPS island where the operation result is bound and
    used in direct computation before returning:
    `read! ()` resumes into `value + 1`, then `_ReturnK(...)`.
- `examples/optimization/selective-uniform/16-cps-helper-call-island.saga`
  - Current result: emits a local CPS helper `read_value/3` and a public CPS
    island `read_plus_two/3` that calls the helper's adapter with source args
    plus `_Evidence` and a generated continuation.
- `examples/optimization/selective-uniform/17-cps-if-island.saga`
  - Current result: emits CPS island `if` control flow. Each branch lowers with
    the same current continuation; effectful branches pass `_ReturnK` to the
    operation while direct branches apply `_ReturnK` to their value.
- `examples/optimization/selective-uniform/18-cps-case-island.saga`
  - Current result: emits CPS island `case` control flow over the supported
    direct pattern subset. Arms lower with the current continuation and may mix
    effectful and direct-return bodies.
- `examples/optimization/selective-uniform/imported-cps-island-project/`
  - Current result: inspecting `src/Main.saga` emits a remote CPS adapter call
    to `effects:read_value/3`, passing `_Evidence` and a generated
    continuation that binds the result and returns `value + 2`.
- `examples/optimization/selective-uniform/19-static-handler-with-cps-island.saga`
  - Current result: emits a pure direct entry `read_plus_one_handled/1` whose
    body contains an internal CPS island. The direct wrapper starts with empty
    evidence and an identity continuation, `with forty_one` installs a
    canonical `ReadInt` evidence entry via
    `std_evidence_bridge:insert_canonical/2`, and `read! ()` finds that entry
    and calls the handler arm closure. The arm supports the narrow
    tail-resume shape `resume 41`, applying the captured operation
    continuation so the surrounding `let value = ...; value + 1` still runs.
  - This is the focused tail-resumptive fixture; broader handler limits are
    tracked in the active design decisions below.
- `examples/optimization/selective-uniform/20-static-handler-return-clause.saga`
  - Current result: emits a pure direct entry `read_with_return/1` whose
    internal CPS island binds a generated return continuation before installing
    handler evidence. The operation arm resumes with `41`; the handled body
    returns through `_ReturnClauseK`, whose closure runs
    `return value = value + 1` under the outer evidence and outer continuation.
  - Current limits: return clauses support zero or one direct-supported
    pattern parameter and a body in the existing direct/CPS-island subset.
    They still do not support `finally`, full abort/result marker routing, or
    broader handler forms.
- `examples/optimization/selective-uniform/21-static-handler-abort-arm.saga`
  - Current result: emits a pure direct entry `abort_to_zero/1` whose handler
    operation arm returns `0` directly from the op closure instead of applying
    the captured `_ArmK`. This skips the return-clause continuation and models
    the narrow `Fail`-style abort path.
- `examples/optimization/selective-uniform/22-static-handler-abort-skips-body.saga`
  - Current result: pins the key abort-control property. The handled body
    contains `let value = fail! (); value + 1` and a `return value = value +
    100` clause, but the abort arm returns `0` without invoking `_ArmK`, so the
    body continuation and return clause are both skipped.
- `examples/optimization/selective-uniform/28-handler-finally-resume-e2e.saga`
  - Current result: static handler operation-arm `finally` cleanup runs after a
    resumed continuation but before the outer continuation of the `with`
    expression. Runtime output under `--selective-codegen` is:
    `body`, `cleanup`, `after`.
- `examples/optimization/selective-uniform/29-handler-finally-abort-e2e.saga`
  - Current result: static handler operation-arm `finally` cleanup runs after a
    direct abort-style arm body and the skipped handled-body continuation does
    not run. Runtime output under `--selective-codegen` is:
    `cleanup`, `after`.
- `examples/optimization/selective-uniform/30-higher-order-direct-callback.saga`
  - Current result: emits a higher-order direct callback call without arity
    guessing. Function-typed parameters are tagged as callable only from their
    typed use site, so `apply_it f = f 1` lowers to `apply F(1)` and
    `main` passes the direct function ref `'inc'/1`.
- `examples/optimization/selective-uniform/31-higher-order-effectful-callback-unsupported.saga`
  - Historical boundary fixture name. This was originally negative; later CPS
    callable-value slices now support `apply_eff/3` and explicit CPS/pure
    callback adapters in CPS islands.
- `examples/optimization/selective-uniform/32-higher-order-direct-callback-e2e.saga`
  - Current result: runtime fixture for the direct callback slice. It calls
    `apply_it inc` under `--selective-codegen` and prints `ok`.
- `examples/optimization/selective-uniform/imported-direct-callback-project/`
  - Current result: project-mode runtime fixture for imported direct callback
    values. `Main` passes imported `Helper.inc` through `apply_it`; value
    lowering emits `erlang:make_fun('helper', 'inc', 1)`, and the project
    prints `ok` under `--selective-codegen`.
- `examples/optimization/selective-uniform/imported-cps-callback-project/`
  - Current result: project-mode runtime fixture for imported CPS/effectful
    callback values inside a handled CPS island. The monadic IR contains
    `let f = read_value; let g = f; apply_eff g`; selective lowering keeps
    named CPS function aliases metadata-only, passes an explicit CPS adapter
    closure to `effects:apply_eff/3`, and the imported `apply_eff/3` aliases
    its runtime closure parameter before applying it with the current evidence
    and continuation. No raw `make_fun`/BEAM fun value is emitted for the
    effectful imported function. Runtime output under `--selective-codegen` is
    `ok`.
- `examples/optimization/selective-uniform/23-local-pure-lambda-call.saga`
  - Current result: emits a direct local lambda value as a Core `fun`, records
    its proven source arity in local shape metadata, and applies it via
    `CallShape::LocalCallable`.
- `examples/optimization/selective-uniform/24-cps-island-local-pure-lambda.saga`
  - Current result: emits a CPS island that binds a direct local lambda before
    `read! ()`; the resumed continuation applies the lambda to the operation
    result and then calls `_ReturnK`. This pins that proven direct callable
    values can survive inside CPS island continuations without guessing arity.
- `examples/optimization/selective-uniform/25-handled-effect-e2e.saga`
  - Current result: first handled-effect selective backend end-to-end run.
    `answer/1` is a direct-ABI function with an internal handled `ReadInt`
    island; `main/1` calls it, checks for `42`, and prints `ok`.
  - Command:
    `cargo run --bin saga -- run examples/optimization/selective-uniform/25-handled-effect-e2e.saga --selective-codegen`
  - Current runtime result: prints `ok`.
- `examples/optimization/selective-uniform/27-cps-island-main-e2e.saga`
  - Current result: a direct `main/1` contains a handled CPS island directly,
    proving the selective entry export can bootstrap a supported island inside
    the entrypoint body.
  - Command:
    `cargo run --bin saga -- run examples/optimization/selective-uniform/27-cps-island-main-e2e.saga --selective-codegen`
  - Current runtime result: prints `ok`.
- `examples/optimization/selective-uniform/imported-handled-effect-project/`
  - Current result: project-mode selective backend run with imported user
    effect definition, imported effectful helper, and imported static handler.
    `Main.answer/1` installs `Effects.forty_one`, calls the remote CPS adapter
    `effects:read_value/3`, resumes through the generated continuation, and
    `main/1` prints `ok`.
  - Command:
    `cargo run --bin saga -- run --selective-codegen` from the project root.
  - Current runtime result: prints `ok`.

## Active Design Decisions

- Pair through the implementation in vertical slices.
- Keep this file as the compaction-resistant brain dump.
- Use directed external/other-agent reviews only for narrow audits, not as
  independent implementers of backend pieces.
- Start with direct pure lowering and runtime shape checks before implementing
  effect specialization.
- Do not port the uniform optimizer as a prerequisite for basic performance.
- The existing monadic IR can be reused later, but only after runtime shape
  classification decides a function or region is CPS-shaped.
- Direct `Unit` parameters can lower as ignored Core Erlang variables for the
  initial one-clause direct subset. Non-variable parameters in the currently
  supported pattern subset lower as direct Core params plus an internal `case`
  over the argument tuple.
- A function classified as direct/pure must not silently disappear from
  `selective-core`. If it is outside the current direct subset, the experimental
  lowerer should fail loudly with the function name.
- `Std.IO.Unsafe.print_stdout` / `print_stderr` are acceptable first direct
  intrinsic cases because they do not require trait dictionaries. `dbg` is not
  in this category because it takes an explicit `Debug` dictionary after
  elaboration.
- Minimal monomorphic trait support now exists in `lower_selective`, with a
  narrow first-class method-local shape. A local method closure extracted from a
  dictionary is tagged as a pure callable using typed node metadata when
  present, trait method metadata when ANF synthesized an untyped node, or a
  typed use-site fallback only for that already-tagged value.
- Local pure lambda values are callable only after shape classification proves
  their parameter count and direct-lowerable body. Callback parameters and
  other untagged function-valued locals remain uncallable until they get
  explicit function-value shape metadata; no arity guessing.
- Direct app lowering now goes through a single `CallShape` classifier in
  `lower_selective`: intrinsic, direct BEAM callable, or tagged local callable.
  Adding new app shapes should go through that classifier.
- Imported pure `BeamFunction`s may lower as remote direct calls when backend
  resolution reports an empty effect row. Local functions still require the
  direct subset/fixed-point classification before they can be called directly.
- `CallShape` now has an explicit `Cps` case for resolved function heads with
  non-empty effect rows. Public/source-`pub` CPS-shaped functions fail loudly in
  `selective-core` only when their implementation body cannot lower direct;
  private CPS helpers may be skipped until the selective CPS island path exists.
- Function type shape and implementation body shape are separate. A function
  whose annotation carries an effect row can still lower to a direct
  implementation if its body is operationally direct. If its callable type is
  CPS-shaped, `selective-core` emits a direct body plus a CPS adapter entry with
  arity `N + 2`.
- Within direct-lowered code, local direct implementations win over their
  CPS-shaped callable type. This lets one direct-lowerable effect-row function
  call another through the direct entry; CPS islands will use the adapter entry.
- Source-level `pub` is honored by `lower_selective` even when `inspect` has a
  partial/empty `ModuleCodegenInfo` for the current file. This keeps adapter
  exports visible in project fixtures.
- `inspect --stage selective-core` now fills imported user modules from
  `compile_module_from_result` when the typechecker has their cached
  program/result. The current direct lowerer does not consume imported body
  shape yet, but the context now has the real elaborated/resolved module data
  needed for cross-module entry metadata later.
- `lower_selective` now uses a single `FunctionLoweringPlan` per function body:
  `DirectBody`, `DirectBodyWithCpsIsland`, or `CpsBody`. Entry metadata is
  derived from that plan plus the declared callable type shape. This keeps the
  implementation-body decision separate from emitted ABI details such as direct
  entry arity and CPS adapter arity. Imported user-module entry metadata is
  now consumed by the inspect path; a durable serialized metadata format for
  separately compiled dependencies still does not exist.
- The main local classifier names are now intentionally split:
  `callable_type_shapes` is declared/runtime type shape, `function_plans` is
  the per-function implementation lowering decision, `local_function_entries`
  is the emitted entry summary, and `direct_candidate_function` is the
  temporary recursion allowance during direct-body fixed-point analysis.
- `CallShape::Cps` carries both source arity and adapter arity. This keeps the
  N vs N+2 convention visible at the boundary where a future CPS island will
  choose an adapter call.
- Public direct-body functions with CPS-shaped callable types export both the
  direct entry and CPS adapter entry. The adapter is the source-level callable
  ABI; the direct entry is an optimization ABI needed for future cross-module
  direct calls once imported entry metadata exists.
- Direct entries for CPS-typed functions use compiler-private names such as
  `__saga_direct_may_log/1`. The source name is reserved for the CPS adapter
  ABI (`may_log/3`), which avoids making `may_log/1` look like a source-level
  public ABI.
- The first CPS island subset now supports `MExpr::Yield`, `MExpr::Bind`, and
  direct-return expressions. `Yield` receives the current continuation, `Bind`
  builds a generated continuation closure that binds the resumed value, and a
  direct expression returns by applying the current `_ReturnK`. CPS islands can
  now call local and imported CPS adapter entries by passing source args plus
  `_Evidence` and the current continuation. They also support `if` and `case`
  control flow over the currently supported direct atom/pattern subset.
- Pure functions can now have a direct ABI even when their body contains a
  supported CPS island. `FunctionLoweringPlan::DirectBodyWithCpsIsland` emits a
  direct source-arity entry whose body runs the island with empty evidence plus
  an identity continuation. This is the first explicit island boundary inside
  an otherwise direct function.
- The first handler/evidence slice supports `MExpr::With` for narrow static
  handlers whose operation arms are tail-resumptive. `With` extends the current
  evidence vector for the handled body, while handler arm closures close over
  the outer evidence so re-performs do not recurse into the just-installed
  handler. Handler arm `Resume` applies the captured operation continuation.
  Static return clauses are supported as generated continuation closures: the
  handled body returns through the return-clause K, and the return-clause body
  lowers under the outer evidence/continuation. Direct abort arms are supported
  in the narrow `Fail` shape by returning the arm body directly from the op
  closure and ignoring the captured continuation. Static operation-arm
  `finally` is supported only when the cleanup is in the direct subset; cleanup
  is sequenced after resumed continuations and after direct abort-style arm
  bodies. Full abort/result-marker routing, dynamic/native/composite handlers,
  effectful cleanup, and handler values remain unsupported in
  `lower_selective`.
- CPS islands support proven direct local lambda values, CPS callable values,
  runtime CPS callback parameters, and pure-to-CPS callback fallback adapters.
- Higher-order direct callbacks are supported when the call-head value has a
  closed pure function type at the use site. Variable-pattern binders are
  marked as callable-from-use-type, but a call only succeeds if typed metadata
  proves the source arity and empty effect row. Named same-module pure
  functions passed as values lower as direct Core function references such as
  `'inc'/1`. Imported pure function values lower through `erlang:make_fun/3`
  using the resolved remote BEAM module/name/arity. CPS/effectful callback
  values are handled by the later CPS callable-value slice inside CPS islands.
- CPS/effectful callable values are supported only inside CPS islands, and only
  as local call heads whose adapter metadata is known. Binding
  `let f = imported_effectful_fun` records `LocalValueShape::CpsCallable`
  instead of emitting a raw runtime function value; `f(args...)` lowers to the
  local/remote CPS adapter with current `_Evidence` and current continuation.
  Using that local as an ordinary direct atom/value remains unsupported.
- `lower_selective` computes imported entry metadata for already-compiled
  non-stdlib user modules. Remote effect-row calls may lower to direct remote
  calls only when that imported metadata proves a direct entry exists; otherwise
  they remain `CallShape::Cps` boundaries.
- Imported effect-row `BeamFunction` arity from backend resolution may be the
  source arity or the adapter arity depending on where the resolved symbol came
  from. Remote direct-entry matching accepts only imported metadata-proven
  direct arities, checking both the resolved arity and `resolved_arity - 2`.
- `emit`, `inspect`, `build`, and `run` should all build comparable
  cross-module `CodegenContext`s. Single-file `emit` inside a project used to
  carry only stdlib plus the current file, which made imported handlers/effect
  helpers look missing to the selective path even though project build/run
  worked.

## Pipeline Integration Milestones

Current mode is **inspect-driven Core shape work plus an experimental
build/run toggle**:

```text
parse/typecheck/elaborate
-> ANF
-> whole-module monadic translation
-> lower_selective
-> print Core via inspect --stage selective-core
   or emit/build/run with --selective-codegen
```

This is intentionally not the final architecture. It lets us prove direct/CPS
entry shapes without replacing the production build pipeline. Normal `saga
build` / `saga run` still go through the existing monadic/uniform lowerer.
Only commands passed `--selective-codegen` route `emit_module_with_context`
through `lower_selective`.

Temporary monadic-IR use:

- It is acceptable for `selective-core` inspect/tests to build monadic IR for
  the whole module while the selective lowerer is being proven.
- Do not mistake that scaffold for the target architecture. The final split
  should build/use monadic IR only for bodies or regions classified as
  CPS-shaped.

Planned integration sequence:

1. **Handler/evidence slice.** Add the first `With` lowering for a simple
   static handler so an operation can run under installed evidence in
   `selective-core`. Status: first narrow static tail-resume case and static
   return-clause continuation case are working; narrow direct abort arms and
   direct-cleanup `finally` arms are working; broader handler semantics are
   still open.
2. **Selective entrypoint/bootstrap slice.** Add the minimal wrapper/evidence
   setup needed for a normal `main` entry to call direct or CPS-shaped code
   correctly. Status: supported direct-ABI entrypoints can now be exported for
   opt-in selective builds; CPS-ABI entrypoint bootstrap is still open.
3. **Experimental build/run toggle.** Add an explicit compiler option or flag
   that routes normal `emit_module_with_context` through `lower_selective` for
   supported modules. Keep the default production path unchanged. Status:
   `--selective-codegen` is wired for `emit`, `build`, `run`, and `test`.
4. **First pure/direct end-to-end run.** Use the experimental toggle to run a
   boring direct program through parse -> emit -> erlc -> erl, e.g.
   `main () = 42` or `main () = { print_stdout "ok"; () }`. Status:
   `04-print-stdout.saga` runs and prints `hello` with `saga run
   --selective-codegen`.
5. **First handled-effect end-to-end run.** Run a trivial handled effect, e.g.
   `read! () with forty_two`, through the same parse -> emit -> erlc -> erl
   path. Status: single-file handled-effect fixtures
   `25-handled-effect-e2e.saga` and `27-cps-island-main-e2e.saga` run and print
   `ok` with `saga run --selective-codegen`. The project fixture
   `imported-handled-effect-project/` also runs and prints `ok`, proving the
   first imported handler/effect-helper E2E path.
6. **Move direct lowering earlier.** Once runtime integration is real, start
   moving proven pure/direct lowering before whole-module monadic translation
   so monadic IR is only built for CPS-shaped regions.

E2E should be tracked explicitly after milestone 3, but it should not become
the main development workflow before the handler/evidence and entrypoint
boundaries exist.

## Next Session Checklist

1. Read this log and `docs/planning/selective-uniform-effects.md`.
2. Check `git status --short`.
3. Decide the next vertical slice:
   - continue milestone 1 beyond the first static tail-resume handler slice,
     or
   - if blocked on handlers, support higher-order CPS callable values at
     island boundaries.
4. Keep updating focused fixtures/tests as each tiny subset starts working.

## Session Notes

### 2026-06-01

- Rewrote `docs/planning/selective-uniform-effects.md` around the direct-first
  plan:
  - uniform runtime shape metadata, not uniform CPS ABI;
  - shape-directed calls as the arity safety blanket;
  - trait/dictionary specialization before effect lowering;
  - monadic IR only for CPS-shaped regions;
  - static Reader/tail-resume specialization after a slow baseline.
- User deleted the old `docs/planning/selective-uniform-direct-shape.md`.
- Created this implementation log.
- Discovered existing selective-uniform scratch code:
  - `src/codegen/lower_selective.rs`;
  - `src/codegen/runtime_shape.rs`;
  - `inspect --stage selective-core`;
  - monadic stats inspect stages.
- Important note from the user: the existing stats tooling that counts
  binds/yields/etc. is worth pulling forward eventually, but not before the
  first direct path is stable.
- Added `examples/optimization/selective-uniform/01-pure-direct.saga`.
- Audited the first failure of `selective-core` on that fixture:
  - `add1/1` and `twice/1` lowered directly;
  - `main/1` was missing because `main ()` arrives as a `Pat::Lit(Unit)`
    parameter and the scratch direct lowerer only accepted variable params.
- Updated `src/codegen/lower_selective.rs` to accept `Unit` literal parameters
  for the initial direct subset, lowering them as ignored Core Erlang params.
- Changed local direct call emission to validate against backend-resolved arity
  and `RuntimeFunctionShape::Pure` before constructing `FunRef`. The first
  direct helper no longer uses source argument count as the function reference
  arity.
- Added a validation step so functions classified as direct/pure but not
  lowerable by the current direct subset panic instead of being silently
  omitted from `selective-core`.
- Added:
  - `examples/optimization/selective-uniform/02-recursive-if.saga`;
  - `examples/optimization/selective-uniform/03-pure-val.saga`.
- Added focused Rust tests for the current `selective-core` scaffold:
  - pure direct local calls;
  - recursive pure `if`;
  - pure top-level `val`;
  - loud failure for unsupported direct tuple-parameter lowering.
- Investigated `dbg 42` / `show 42` as possible next fixtures. Both require
  trait dictionary support before they are meaningfully "intrinsic" or direct:
  - `dbg 42` translates to a `Debug Int` dictionary constructor plus `dbg`
    applied to the dict and value;
  - `show 42` translates to `DictRef(Show Int)`, `DictMethodAccess`, and then
    a method call.
  Do not treat `dbg` as a small intrinsic-only slice; it belongs after the
  first trait/dictionary direct slice.
- Added `examples/optimization/selective-uniform/04-print-stdout.saga`.
- Added direct lowering for `IntrinsicId::PrintStdout` and
  `IntrinsicId::PrintStderr` in `src/codegen/lower_selective.rs`. The direct
  path emits `io:format(...)` and returns `unit`, matching the builtin wrapper
  behavior without invoking the uniform lowerer.
- Added a focused Rust test for direct `print_stdout` lowering.
- Added minimal monomorphic trait/dictionary direct lowering:
  - `Atom::DictRef` dictionary constructors can lower as direct local/remote
    calls when resolution says they are closed-effect `BeamFunction`s;
  - `MExpr::DictMethodAccess` lowers to `erlang:element(method_index + 1,
    dict)`;
  - local closure application is allowed for the extracted method value.
- Added direct `dbg` intrinsic lowering for the direct-dictionary world:
  extract debug method, call it directly with the value, print to stderr, return
  `unit`.
- Added:
  - `examples/optimization/selective-uniform/05-trait-show.saga`;
  - `examples/optimization/selective-uniform/06-dbg.saga`.
- Added focused Rust tests for `show 42` and `dbg 42`.
- Narrowed local function-value application: only bindings known to come from
  `DictMethodAccess` may be applied. Added a panic test proving ordinary
  function-valued locals such as callback parameters do not get shape-guessed.
- Added direct named-record field access:
  - field order comes from `EffectInfo.records` for named records;
  - anonymous records can use the `anon_fields` metadata already carried on the
    monadic IR node;
  - field reads lower to `erlang:element(index, record)`.
- Added `examples/optimization/selective-uniform/07-record-field.saga`.
- Added a focused Rust test for named record field access.
- Replaced the temporary `method_values` set with explicit local value shape
  metadata:
  - `DictMethodAccess` locals are tagged as pure callable values;
  - arity/effect shape comes from typed node metadata when available, otherwise
    from `TraitInfo` method metadata because ANF may synthesize untyped
    `DictMethodAccess` NodeIds;
  - the use-site type fallback is allowed only for those already-tagged
    dict-method locals.
- Added `TraitInfo` to the narrowed monadic `EffectInfo` view so selective
  lowering can recover trait method shape without depending on source arity.
- Added direct parameter pattern matching for the supported pattern subset
  (`var`, wildcard, literals, tuples). The emitted function keeps source arity
  and wraps the body in a Core `case` when any parameter needs destructuring or
  literal checking.
- Added `examples/optimization/selective-uniform/08-tuple-param.saga` and
  changed the old tuple-parameter panic test into a success test.
- Added constructor-pattern support for direct params and `case` arms, including
  `Cons`/`Nil`/`True`/`False` special cases and normal tagged-tuple ADTs.
- Added `examples/optimization/selective-uniform/09-constructor-case.saga` and
  a focused test for direct ADT construction plus constructor-pattern case
  matching.
- Centralized `lower_selective` app dispatch behind `CallShape` and routed
  intrinsics, direct BEAM calls, and tagged local callables through it.
- Added imported pure direct calls:
  - stdlib fixture `10-imported-pure.saga` lowers `Maybe.is_just (Just 1)` to
    `call 'std_maybe':'is_just'(...)`;
  - generated project fixture `imported-pure-project` lowers cross-user-module
    calls to `helper:inc/1` and `helper:pick/1`.
- Made `inspect` project-aware for file stages by passing the discovered
  `project.toml` root into `make_checker` and preserving `CodegenContext`
  codegen metadata for all typechecked modules, not only stdlib/current module.
- Added the first explicit CPS boundary:
  - resolved call heads with non-empty effect rows classify as `CallShape::Cps`;
  - public/source-`pub` CPS-shaped functions whose bodies are not direct-lowerable
    fail with a targeted TODO instead of disappearing from the emitted module;
  - fixture `11-effect-boundary.saga` originally proved that boundary before
    the simple-yield island existed.
- Split type shape from implementation shape for direct-lowerable bodies:
  - `can_lower_fun_binding` now asks whether the body fits the direct subset,
    regardless of whether the declared function type has an effect row;
  - fixture `12-effect-row-direct-body.saga` proves `needs {Log}` plus a pure
    body emits direct Core Erlang while retaining the future CPS-call shape.
- Added the first CPS adapter:
  - direct-lowerable functions with CPS-shaped callable types emit a direct
    implementation at arity `N`;
  - the same name also gets an adapter at arity `N + 2`:
    `fun(args..., _Evidence, _ReturnK) -> apply _ReturnK(apply f/N(args...))`;
  - public exports use the adapter arity for those CPS-shaped callable types.
- Updated direct call classification so a local direct implementation is chosen
  before `CallShape::Cps`. Fixture `12-effect-row-direct-body.saga` now proves
  `__saga_direct_use_may_log/1` calls `__saga_direct_may_log/1` directly while
  both source functions still expose `/3` adapters.
- Tightened project-mode inspect plumbing:
  - imported user modules are compiled into `CodegenContext` with real
    elaborated ASTs and backend resolution when available, instead of always
    being placeholder metadata-only modules;
  - source-level `pub` functions in `lower_selective` export even when the
    current file has no useful `ModuleCodegenInfo` in the inspect context.
- Added `imported-effect-row-project` fixture to pin the next cross-module
  effect-row question: the provider module emits its adapter, while a consumer
  public wrapper still fails at the CPS boundary until imported direct-entry
  metadata exists.
- Refactored `lower_selective` to compute explicit local `FunctionEntryInfo`
  after direct-body classification. Export arity, CPS adapter emission, and
  "unlowered direct/CPS" assertions now read from that entry metadata.
- Made `CallShape::Cps` store `source_arity` and `adapter_arity` separately
  instead of a single ambiguous arity field.
- Exported both arities for public direct-body CPS-typed functions, e.g.
  `__saga_direct_may_log/1` and `may_log/3`.
- Renamed the main selective-lowering bookkeeping fields so they describe their
  roles:
  `direct_shapes` -> `callable_type_shapes`,
  `direct_functions` -> `direct_body_functions`,
  `function_entries` -> `local_function_entries`,
  `supporting_fun` -> `direct_candidate_function`.
- Moved CPS-typed direct implementations behind compiler-private
  `__saga_direct_*` names. The source name now remains the adapter ABI.
- Added an automated selective runtime smoke test that compiles selective Core
  with `erlc` and calls the CPS adapter on BEAM when `erlc`/`erl` are present.
- Added imported user-module entry analysis in `lower_selective`. The
  `imported-effect-row-project` consumer now lowers:
  `call 'effects':'__saga_direct_may_log'('unit')`.
- Corrected CPS resolved arity handling for imported effect-row functions:
  remote resolution can report the adapter arity (`N + 2`), so selective entry
  matching checks imported metadata against both the resolved arity and the
  derived direct source arity.
- Added the first tiny selective CPS island:
  - `cps_body_functions` tracks CPS-typed bodies that match the current island
    subset;
  - the subset currently accepts only a bare `MExpr::Yield` with direct atom
    arguments;
  - `lower_cps_fun_binding` emits the source-name adapter ABI directly:
    `fun(args..., _Evidence, _ReturnK) -> ...`;
  - `lower_cps_yield` emits the open-row uniform evidence lookup through
    `std_evidence_bridge:find_evidence`, selects the operation closure with
    `erlang:element`, then tail-applies it to source args plus `_Evidence` and
    `_ReturnK`.
- Added `examples/optimization/selective-uniform/13-simple-yield-cps-island.saga`
  and changed the simple-yield `selective_core` test from expected panic to
  successful Core emission plus `erlc +from_core` compilation when Erlang is
  available.
- Extended selective CPS islands from bare `Yield` to continuation-driven
  `Bind`/`Yield`/direct-return sequencing:
  - `lower_cps_expr` now receives an explicit current continuation expression;
  - direct leaf expressions lower by applying that continuation;
  - `Yield` tail-applies the selected operation closure with the current
    continuation;
  - `Bind` either lowers direct values as Core `let`s or passes a generated
    continuation closure into the nested CPS value.
- Added:
  - `examples/optimization/selective-uniform/14-yield-then-return-cps-island.saga`;
  - `examples/optimization/selective-uniform/15-yield-result-used-cps-island.saga`.
- Added focused `selective_core` tests for effect-then-return and
  effect-result-used islands, both with `erlc +from_core` compilation checks
  when Erlang is available.
- Added CPS adapter calls from inside CPS islands:
  - `CallShape::Cps` now carries the optional remote module;
  - local CPS calls use explicit local runtime-shape metadata during
    classification, because resolution may not carry the effect row there yet;
  - imported CPS calls use imported entry metadata when available;
  - `lower_cps_app` appends `_Evidence` and the current continuation and emits
    either local `apply 'name'/N(...)` or remote `call 'module':'name'(...)`.
- Added:
  - `examples/optimization/selective-uniform/16-cps-helper-call-island.saga`;
  - `examples/optimization/selective-uniform/imported-cps-island-project/`.
- Added a same-module `selective_core` unit test for calling a local CPS helper
  and a CLI integration test for project-mode imported CPS adapter calls.
- Started module discipline for `lower_selective` by moving entry/call-shape
  metadata and leaf helper functions into `src/codegen/lower_selective/support.rs`.
  The main file still owns classification and lowering behavior; future splits
  should move whole responsibility groups such as classification, direct
  lowering, and CPS island lowering.
- Added CPS island `if` and `case` support:
  - `if` lowers to a Core `case` over the direct condition atom, with both
    branches lowered under the current continuation;
  - `case` lowers each arm under the current continuation, preserving direct
    guard lowering and supported pattern scopes;
  - added fixtures `17-cps-if-island.saga` and `18-cps-case-island.saga` plus
    focused `selective_core` tests.
- Split `lower_selective` into responsibility modules:
  - root `lower_selective.rs`: orchestration, classification, entry metadata
    computation, call-shape resolution, subset analysis, and shared state;
  - `lower_selective/direct.rs`: direct expression/app/intrinsic/atom/pattern
    lowering;
  - `lower_selective/cps.rs`: CPS island lowering;
  - `lower_selective/support.rs`: small data types and helper functions.
- Verification:
  - `cargo run --bin saga -- inspect examples/optimization/selective-uniform/01-pure-direct.saga --stage selective-core`
    emits direct `add1/1`, `twice/1`, and `main/1`.
  - The same `selective-core` command succeeds for `02-recursive-if.saga` and
    `03-pure-val.saga`.
  - `cargo test -p saga runtime_shape` passed.
  - `cargo test -p saga selective_core` passed.
  - `cargo fmt` run.
  - Manual BEAM smoke checks for selective output:
    - `selective-core` output for `01-pure-direct.saga` compiles with `erlc`
      when saved as `_script.core`;
    - `selective-core` output for `12-effect-row-direct-body.saga` compiles
      with `erlc`, and calling the exported adapter
      `'_script':may_log(unit, [], fun(X) -> X end)` returns `42`.
    - `cargo run --bin saga -- inspect src/Main.saga --stage selective-core`
      from `imported-effect-row-project` emits a direct remote call to
      `effects:__saga_direct_may_log/1`.
    - `cargo run --bin saga --quiet -- inspect examples/optimization/selective-uniform/13-simple-yield-cps-island.saga --stage selective-core`
      emits `do_log/3` with `_Evidence`, `_ReturnK`, `find_evidence`, and
      `erlang:element`.
    - `cargo run --bin saga --quiet -- inspect examples/optimization/selective-uniform/14-yield-then-return-cps-island.saga --stage selective-core`
      emits a generated `_CpsBindArg0` continuation ending in
      `apply _ReturnK(42)`.
    - `cargo run --bin saga --quiet -- inspect examples/optimization/selective-uniform/15-yield-result-used-cps-island.saga --stage selective-core`
      emits a generated `_CpsBindArg0` continuation that binds `Value` and
      returns `Value + 1`.
    - `cargo run --bin saga --quiet -- inspect examples/optimization/selective-uniform/16-cps-helper-call-island.saga --stage selective-core`
      emits `apply 'read_value'/3('unit', _Evidence, fun (_CpsBindArg0) -> ...)`.
    - `cargo run --bin saga --quiet -- inspect examples/optimization/selective-uniform/17-cps-if-island.saga --stage selective-core`
      emits `if` as a Core `case` whose effect branch passes `_ReturnK` and
      whose direct branch applies `_ReturnK(0)`.
    - `cargo run --bin saga --quiet -- inspect examples/optimization/selective-uniform/18-cps-case-island.saga --stage selective-core`
      emits `case` arms that mix an effectful arm with a direct `_ReturnK(0)`
      arm.
    - `cargo run --bin saga --quiet -- inspect src/Main.saga --stage selective-core`
      from `imported-cps-island-project` emits
      `call 'effects':'read_value'('unit', _Evidence, fun (_CpsBindArg0) -> ...)`.

### 2026-06-02

- Added `examples/optimization/selective-uniform/27-cps-island-main-e2e.saga`.
  This pins a direct `main/1` whose body contains the handled `ReadInt` CPS
  island itself, instead of delegating to a separate `answer/1` helper.
- Added
  `examples/optimization/selective-uniform/imported-handled-effect-project/`.
  This is the first project-mode selective runtime fixture with:
  - imported user effect definition;
  - imported effectful helper that exports/uses the CPS adapter ABI;
  - imported static handler installed in the consumer module;
  - direct `Main.answer/1` and `Main.main/1` entries.
- Fixed `cmd_emit` to build the same kind of cross-module `CodegenContext`
  used by `inspect`/project build paths. Before this, `saga emit
  src/Main.saga --selective-codegen` from the imported handled-effect project
  panicked in selective lowering because the imported handler/helper module was
  absent from the context even though `saga run --selective-codegen` worked.
- Shared the checked-module context construction between `emit` and `inspect`
  so single-file/project diagnostics do not quietly drift apart again.
- Verification:
  - `cargo run --bin saga --quiet -- emit src/Main.saga --selective-codegen`
    from `imported-handled-effect-project` now emits Core successfully and
    includes the remote CPS adapter call `effects:read_value/3`.
  - `cargo run --bin saga --quiet -- run --selective-codegen` from
    `imported-handled-effect-project` builds `Effects` and `Main` and prints
    `ok`.
  - `cargo run --bin saga --quiet -- run examples/optimization/selective-uniform/27-cps-island-main-e2e.saga --selective-codegen`
    prints `ok`.
- Added narrow selective support for static operation-arm `finally` cleanup:
  - the cleanup expression must be direct-lowerable;
  - resume arms sequence cleanup after the captured operation continuation;
  - direct abort-style arms sequence cleanup after the arm body result;
  - return-clause `finally` remains unsupported/unreachable for current syntax.
- The first `finally` fixture exposed a real delimiter bug in the selective
  `with` lowering. Before the fix, the handler body used the outer continuation
  directly, so cleanup after `resume` ran after the continuation outside the
  `with`. `lower_cps_with` now lowers the handled body to a local
  `_WithResult` first and applies the outer continuation only after handler
  return/finally processing.
- Added:
  - `examples/optimization/selective-uniform/28-handler-finally-resume-e2e.saga`;
  - `examples/optimization/selective-uniform/29-handler-finally-abort-e2e.saga`.
- Added selective tests for the new cleanup shapes:
  - unit-level Core shape/compile checks for resume cleanup and abort cleanup;
  - CLI runtime integration coverage that runs both fixtures with
    `--selective-codegen` and checks output order.
- Added the first higher-order direct callback slice:
  - variable-pattern binders are now marked as `PureCallableFromUseType`;
  - `LocalCallable` classification still requires the call-head NodeId to have
    a closed pure function type, so non-function locals and effectful function
    values do not become callable by guesswork;
  - same-module pure function values can flow to direct callback parameters as
    Core function references.
- Added:
  - `examples/optimization/selective-uniform/30-higher-order-direct-callback.saga`;
  - `examples/optimization/selective-uniform/31-higher-order-effectful-callback-unsupported.saga`;
  - `examples/optimization/selective-uniform/32-higher-order-direct-callback-e2e.saga`.
- Added selective tests for higher-order direct callbacks, including a negative
  effectful-callback test and a CLI runtime check for the E2E fixture.
- Extended the higher-order direct callback slice to imported pure function
  values:
  - same-module pure function values still lower as local `FunRef`s;
  - imported pure function values lower as `erlang:make_fun(Module, Name,
    Arity)`;
  - effectful/CPS function values still do not get eta-expanded or adapted.
- Added `examples/optimization/selective-uniform/imported-direct-callback-project/`
  and CLI coverage that checks both the emitted `make_fun` shape and the
  project runtime output under `--selective-codegen`.
- Added the first CPS callable-value slice inside CPS islands:
  - `LocalValueShape::CpsCallable` carries module/name/source arity/adapter
    arity/effects;
  - named CPS function values use `CpsCallable`: aliases such as
    `let f = read_value; let g = f` stay metadata-only until a value position
    needs an explicit adapter closure;
  - runtime CPS closure parameters and aliases use `RuntimeCpsCallable`, carry
    arity directly, and emit real Core variables/bindings;
  - `let f = read_value; let g = f; apply_eff g` in a handled island lowers the
    argument to an explicit CPS adapter closure that calls
    `effects:read_value/3` with the closure's evidence and continuation;
  - `apply_eff f = { let g = f; g () }` lowers to a real `let <G> = F` followed
    by `apply G('unit', _Evidence, _ReturnK)`;
  - branch-shaped CPS callable values now materialize runtime closures:
    `let f = if choose then read_value else read_again` lowers to a Core
    `case` whose arms each return an explicit CPS adapter closure, and the
    bound `f` is tracked as `RuntimeCpsCallable`;
  - case-shaped CPS callable values follow the same rule:
    `let f = case choose { True -> read_value; False -> read_again }`
    materializes a Core `case` of CPS adapter closures;
  - pure callbacks in CPS callback slots now use an explicit fallback adapter:
    `fun args _Ev K -> K(pure(args...))`;
  - mixed CPS/pure callback branches/cases now materialize CPS runtime
    closures for both arms: effectful arms use the CPS adapter closure, pure
    arms use the pure-to-CPS fallback adapter;
  - CPS callable values are now explicitly rejected as raw effect-operation
    arguments until operation parameter metadata can choose the correct adapter
    representation;
  - effectful imported functions still never lower as raw BEAM fun refs.
- Added `examples/optimization/selective-uniform/imported-cps-callback-project/`
  and CLI coverage that checks the monadic case/bind/app shape, the generated
  selective Core adapter closures for imported effectful and pure functions,
  the imported `apply_eff/3` runtime closure alias/application, and project
  runtime output.
- Added `--selective-no-fallback` plumbing for compile commands:
  - the flag implies `--selective-codegen`;
  - `run`, `build`, `emit`, `test`, and `inspect --stage selective-core`
    all thread it through `CompileOptions`;
  - the selective lowerer exposes `LoweringOptions::require_all_functions`;
  - when enabled, every function/value declaration in the lowered module must
    have a selective lowering plan instead of being skipped as private or left
    for a future generic fallback.
- Current meaning: this is a matrix-audit/debug flag. It does **not** yet route
  unsupported shapes to the old uniform monadic backend, because that whole
  fallback handoff has not been connected. Once that exists, this flag should
  become the switch that disables the handoff and makes the missing selective
  cells fail loudly.
- Added `examples/optimization/selective-uniform/33-no-fallback-private-unplanned.saga`
  and CLI coverage proving normal `selective-core` inspection can ignore the
  private unsupported helper, while `--selective-no-fallback` reports the
  missing selective plan.
- Added CPS callable-value guardrail coverage for storage and handler value
  positions:
  - tuples containing CPS callable values;
  - records containing CPS callable values;
  - constructors containing CPS callable values;
  - handler arm `resume read_value`;
  - handler return clauses whose result is a CPS callable value.
- These remain intentionally unsupported until we choose a concrete runtime
  representation. The important property is that they fail during selective
  planning/lowering instead of emitting a raw BEAM function reference with the
  wrong arity.
- Added the first CPS lambda slice:
  - `fun ... -> effectful body` can lower as a runtime CPS closure with user
    args followed by evidence and continuation;
  - effectful lambdas can be passed directly to CPS callback parameters;
  - let-bound effectful lambdas materialize once and are tracked as
    `RuntimeCpsCallable`;
  - lambda-headed CPS calls such as `(fun () -> read! ()) ()` lower by applying
    the generated runtime CPS closure immediately;
  - the selective runtime test helper now compiles `std_evidence_bridge` when
    generated Core uses handler evidence.
- Added the first effectful trait method slice:
  - local monomorphic `MDictConstructor`s lower as direct tuple-producing
    functions;
  - effectful dict methods lower their method lambdas with the CPS callback
    ABI, while pure methods stay direct;
  - effectful `DictMethodAccess` is classified as `RuntimeCpsCallable` using
    the method-access type first and trait metadata as fallback;
  - effectful trait method calls in CPS islands apply the extracted method
    closure with evidence/continuation;
  - effectful trait method values can flow into CPS callback positions.
- Added `examples/optimization/selective-uniform/34-effectful-trait-method.saga`
  as a manual fixture for the new local monomorphic trait path.
- Extended the effectful trait method slice to local generic dictionary
  constructors:
  - `MDictConstructor`s with `dict_params` now lower as direct tuple-producing
    functions whose arity is the number of sub-dictionaries;
  - the constructor itself stays direct, while effectful methods inside the
    tuple still lower as CPS closures;
  - method closures can close over constructor dictionary parameters, so nested
    dispatch like `impl Readable for Box a where {a: Readable}` can extract the
    inner method from `__dict_Readable_a` and apply it with the current evidence
    and continuation;
  - `examples/optimization/selective-uniform/35-generic-effectful-trait-method.saga`
    covers the manual fixture, and the unit test evaluates the nested dispatch
    path to `43`.
- Extended the effectful trait method slice to imported dictionary
  constructors:
  - selective-emitted dict constructors are exported at their direct
    constructor arity when the module's codegen info exposes the trait impl;
  - imported `DictRef`s already resolve through `trait_impl_dicts` to remote
    `BeamFunction`s with no effect extras, so the existing direct-call path can
    call remote dict constructors without a new ABI;
  - `Main` can now call an imported effectful trait method whose concrete impl
    and generic wrapper impl both live in `Lib`;
  - `examples/optimization/selective-uniform/imported-effectful-trait-project/`
    covers this path end to end and prints `ok`.
- Current trait status: the local/imported effectful trait method ABI is now
  covered for direct dict constructors, including generic dictionary
  parameters. The next trait work should be specialization, not more ABI
  plumbing: monomorphic call-site specialization, net-pure trait dispatch, and
  known constructor/output-shape specialization.
- Started the specialization track with local direct HOF specialization:
  - CPS-bodied higher-order functions can now get a private
    `__saga_direct_hof_*` entry when their body becomes direct if selected
    callback parameters are treated as pure callables;
  - the generic CPS entry remains emitted and remains the correctness fallback;
  - CPS call lowering selects the private direct entry only when the actual
    callback arguments are statically pure and match the expected source arity;
  - `apply_eff pure_value with handler` now calls
    `__saga_direct_hof_apply_eff/1` with `'pure_value'/1` instead of allocating
    a `fun (_PureCpsArg, _Ev, _K) -> ...` adapter;
  - named callbacks whose bodies use effects internally but expose a pure type
    follow the same path: `apply_eff handled_value with handler` calls the
    direct HOF specialization with `'handled_value'/1`;
  - mixed/dynamic callback cases still use the CPS runtime representation and
    pure-to-CPS wrapper.
- At this point the local named-HOF path is covered for statically pure
  callbacks, including named callbacks that handle their own effects internally.
  Alias-shaped HOF values and inline handled callback expressions remain future
  specialization candidates.
- Extended direct HOF specialization to imported named HOFs in full project
  builds:
  - imported re-analysis now overlays exported function effect metadata from
    `ModuleCodegenInfo`, so public CPS HOFs can be recognized even when the
    caller's `EffectInfo` is for another module;
  - when the imported body is present, the lowerer computes the same
    `__saga_direct_hof_*` specialization metadata and caches it under the
    imported BEAM module name;
  - public HOF specializations are exported from the defining module;
  - calls like `Effects.apply_eff Effects.pure_value` lower to
    `effects:__saga_direct_hof_apply_eff(make_fun(effects, pure_value, 1))`
    instead of `effects:apply_eff/3` with a pure-to-CPS wrapper;
  - `examples/optimization/selective-uniform/imported-pure-callback-specialization-project/`
    covers the full project build and emitted Core shape.
- Current imported-HOF caveat: single-module `inspect src/Main.saga --stage
  selective-core` can still have incomplete imported bodies in its convenience
  context, so this optimization is asserted through project `run/build` output.
  The production project build path has the full imported body and specializes.
- Finished the first HOF specialization cleanup by preserving direct-HOF
  specialization metadata on `LocalValueShape::CpsCallable`:
  - `let hof = apply_eff; hof pure_value` now selects
    `__saga_direct_hof_apply_eff/1` instead of losing the optimization when the
    HOF is used as a local value;
  - imported HOF aliases follow the same path, so the imported pure-callback
    specialization project now aliases `apply_eff` before calling it;
  - if a branch/case produces the exact same known CPS callable shape on every
    arm, the known shape is preserved; genuinely dynamic choices still fall
    back to runtime CPS callable values;
  - this keeps the correctness fallback intact while avoiding a performance
    cliff for ordinary `let hof = SomeModule.apply_eff` code.
- Finished inline handled callback specialization without adding a separate
  escaping-yield analysis:
  - deferred lambda arguments in function application now record their inferred
    type in `type_at_node`, so selective lowering can see when an inline
    callback is net-pure even if it appears in an effect-capable HOF slot;
  - inline handled callbacks such as
    `apply_eff (fun () -> read! () with handler)` now call the direct HOF
    specialization with a direct lambda whose body is lowered as a CPS island;
  - leaking inline callbacks such as `fun () -> read! () + 1` remain CPS-shaped
    and do not select the direct HOF specialization.
- Added the first local static-handler direct-call slice inside selective CPS
  islands:
  - selective lowering now receives `HandlerAnalysis` and carries a static
    handler-frame stack while lowering `With` bodies;
  - `Yield` lowering first tries an innermost matching static arm before falling
    back to evidence lookup;
  - the rewrite is deliberately conservative: exactly one matching arm,
    `TailResumptive`, no `finally`, supported op param patterns only, and no
    nested `Yield` in the inlined arm body;
  - `read! () with { read () = resume 41 }` now direct-calls the arm and avoids
    `std_evidence_bridge:find_evidence` for the operation;
  - captured lexical values are supported in this local shape too:
    compute a value first, then use `db_url () = resume config` in an inline
    handler around a body that performs `db_url! ()`; the direct call sees the
    outer local and still avoids evidence lookup;
  - this does not yet optimize through a separate helper body like
    `Postgres.query ... with { db_url () = resume config }`, because the
    `db_url!` operation is lowered inside `Postgres.query` rather than in the
    caller's current static-handler frame. That needs static-handler facts plus
    function/HOF specialization, not just the local direct-call rewrite;
  - static handler evidence/closure construction is still emitted around the
    `With` for now. Removing unused handler installation is the next
    measurement-driven cleanup, not part of this first direct-call slice.
- Added the first cross-function static-handler specialization slice for local
  helpers:
  - while a static handler frame is active, a call to a known local CPS helper
    can be inline-specialized under that frame instead of calling the helper's
    normal `arity + 2` CPS entry;
  - this is deliberately a call-site optimization, not a new ABI: if the callee
    is unsupported, recursive, has unsupported parameter patterns, has effects
    not covered by the active static handlers, or has a body outside the current
    CPS-island subset, lowering falls back to the normal CPS call;
  - captured handler-arm values keep working because the callee body is lowered
    in the caller's lexical/static-handler context;
  - the local `query () needs {DbConfig}` pattern now specializes under
    `query () with { db_url () = resume config }`, so the caller path avoids
    applying `query/3` and direct-calls the static arm;
  - the emitted fallback helper definition still exists and may still contain
    `find_evidence`; dead-code cleanup and handler-install elision are separate
    follow-up optimizations;
  - imported `Postgres.query`-style specialization remains future work because
    imported bodies must be lowered with their own resolution metadata while
    still seeing caller-provided static-handler facts.
- Added conservative handler-install elision for the local static-handler
  slices:
  - if a static `With` has no return clause, no `finally`, only
    tail-resumptive arms in the current direct-call subset, and the body can run
    without any CPS call observing the newly-installed evidence, selective
    lowering skips `std_evidence_bridge:insert_canonical`;
  - the elision scanner allows direct-called `Yield`s for handled operations and
    local CPS helper calls only when those helpers can also be inline-specialized
    under the same static handler facts;
  - direct `read () = resume 41`, captured-value
    `db_url () = resume config`, and local `query () with { db_url () = ... }`
    now avoid both evidence lookup on the optimized path and handler evidence
    installation;
  - handlers with `finally` still install evidence and use the generic handler
    path, preserving cleanup semantics;
  - opaque local CPS callables, including current trait method closures, are
    treated as possibly observing the elided handler evidence. They force the
    generic install path until trait/dict specialization can provide concrete
    method-effect facts;
  - fallback helper definitions can still be emitted and may still contain
    `find_evidence`; removing unused fallback definitions is a later Core
    cleanup/dead-code problem, not part of this elision pass.
- Added the first imported static-handler helper specialization:
  - remote CPS calls under an active static handler can now be specialized by
    re-lowering the imported callee body with its own resolution metadata while
    carrying the caller's local scopes and static-handler facts;
  - this covers the `Postgres.query ... with { db_url () = resume config }`
    shape for direct imported helpers: the caller path avoids both the remote
    `query/3` call and handler evidence installation when the imported body is
    proven safe;
  - the implementation remains call-site-only and fallback-preserving: if the
    imported body is unavailable, unsupported, recursive through the same
    specialization key, or has effects not covered by active static handlers,
    lowering keeps the normal remote CPS call;
  - imported monadic candidate collection is now scoped to modules explicitly
    imported by the current source module. This avoids translating unrelated
    modules with the wrong per-entry `EffectInfo` table during project builds;
  - `examples/optimization/selective-uniform/imported-static-handler-specialization-project/`
    covers the full project path and prints `ok`.
- Added the first trait/dict effect-fact cleanup for selective decisions:
  - `LocalValueShape::RuntimeCpsCallable` and `CallShape::LocalCpsCallable`
    now carry known static effects when type metadata or trait method metadata
    provides them;
  - branch-shaped runtime CPS callable values merge their effect rows
    conservatively;
  - handler-install elision now treats local runtime CPS callables as blockers
    only when their known effects intersect the handler being elided;
  - this lets a `DbConfig` static handler elide around a trait method call that
    needs only an outer `ReadInt` handler, while still preserving evidence for
    trait calls whose effects intersect the elided handler.
- Added the first Reader/config direct-result bind optimization:
  - a bind whose value is a statically direct-called `Yield` with a simple
    `resume atom` arm lowers as an ordinary `let` of the resumed value;
  - `let value = db_url! ()` under `db_url () = resume config` now emits
    `let <Value> = Config` instead of allocating/applying a one-shot
    continuation closure;
  - this currently targets the simplest `resume atom` shape. Handler arm bodies
    with direct lets/cases still use the existing direct-call path and can be
    specialized further later.
- Started the proof/decision cleanup without introducing a separate proof
  framework:
  - `lower_cps_app` now classifies call lowering through a `CpsCallDecision`
    enum before emitting Core;
  - the explicit decision order is HOF direct specialization, local static
    handler specialization, imported static handler specialization, CPS lambda,
    normal CPS call, direct fallback, unsupported;
  - this keeps the current behavior but makes the priority order visible and
    gives future trace/proof records a natural insertion point.
- Started trait/dict specialization in selective lowering:
  - local nullary dict constructors are recorded as known dict values when the
    constructor body is a tuple of method lambdas;
  - a bind that extracts a method from such a known dict records the concrete
    method lambda and also binds a normal CPS lambda value, preserving callback
    value use;
  - calling that known local CPS lambda now inlines the method body at the call
    site, so existing static-handler direct-call and Reader/config bind
    specializations can see through concrete trait methods;
  - direct calls can therefore leave an unused method-closure binding on the
    optimized path; removing that is a later dead-let cleanup or a more precise
    call-head-only bind analysis;
  - the generic dict constructor fallback is still emitted, and parameterized,
    imported, and branch-shaped dictionaries still use the normal dict-passing
    path for now.
- Added the parameterized-dict specialization canary:
  - known dict values now carry constructor dict params and the actual dict
    arguments used to build them;
  - known method lambdas carry those captured dict bindings, so inlining a
    parameterized method body can bind `__dict_Trait_a` to the concrete dict
    argument from the call site;
  - local static-handler helper specialization now aliases known dict arguments
    onto helper parameters, which lets a generic helper like `serialize` expose
    the concrete dict it was called with;
  - the `Box a` over `Int` shape now specializes through the outer dict method
    and then through the inner dict method, allowing the inner effect operation
    to use the existing direct Reader/config-style optimization;
  - this is intentionally still a canary: it does not handle imported dict
    constructors, branch-shaped dict values, dead closure lets, or handler
    install elision for the new parameterized facts yet.
- Runtime ABI note from trying the selective backend end-to-end:
  - selective app code currently expects selectively lowered stdlib dict
    constructors, e.g. a nullary `std_string:__dict_Debug_String/0`;
  - the stdlib cache is still built with the uniform/monadic backend, which
    exports the same dict constructor with the uniform CPS ABI, e.g. `/2`;
  - this mixed-backend boundary causes runtime missing-function errors for
    selective app code that calls imported stdlib dictionaries directly;
  - we backed out the partial backend-aware stdlib-cache experiment for now.
    The final fallback/module-boundary design needs one consistent ABI or
    explicit adapters for fallback/public dict constructors and functions.
- Reduced known trait specialization artifact lets:
  - known method extraction now scans the continuation to distinguish
    call-head-only uses from value uses;
  - if the method local is only used as a call head, selective lowering records
    the known lambda fact but skips materializing the fallback CPS closure;
  - if the method local is passed as a callback, stored, captured, returned, or
    otherwise used as a value, the fallback closure is still emitted;
  - the parameterized `Box a` canary no longer emits direct-path method-closure
    lets before immediately inlining through the known method call.
- Extended parameterized trait facts into handler-install elision:
  - the elision dry-run now records known dict values and known method lambdas
    for supported binds, not only during final lowering;
  - local static-handler helper elision aliases known dict arguments onto the
    helper's parameters, matching the final static-handler specialization path;
  - this lets the generic `Box a -> Int` trait canary prove that a static
    handler install is unnecessary on the optimized path, because the concrete
    inner `read!` operation is visible during the elision proof;
  - fallback dict constructor definitions may still mention `find_evidence` and
    the effect name. The optimized handler body avoids `insert_canonical`;
    deleting unused fallback definitions remains a separate cleanup.
- Added the narrow branch-shaped known-dict canary:
  - `known_dict_value_for_expr` now composes through `if` only when both branches
    produce the same known dict value;
  - this covers the internal shape `let d = if cond then int_dict else int_dict`
    without introducing a runtime conditional-dict representation;
  - different branch dictionaries still fall back to the normal dynamic/CPS
    path until the fallback ABI is wired.
- Imported concrete dict specialization was intentionally left for the ABI
  cutover:
  - existing imported effectful trait coverage already proves remote dict
    constructors are exported and callable in selective Core;
  - specializing through a remote concrete dict would require importing or
    re-translating the remote dict constructor body for selective facts;
  - that overlaps the unresolved module-boundary fallback ABI, especially for
    stdlib dictionaries, so it should be done after the monadic fallback and
    public adapter story are connected.
- Started the selective ABI cutover behind `--selective-codegen`:
  - selective mode now builds the old optimized monadic Core module as a
    fallback, builds the direct-first selective Core module as an overlay, and
    merges them by `(name, arity)` with selective definitions winning;
  - permissive selective lowering may now skip unsupported declarations because
    fallback definitions remain available. `--selective-no-fallback` keeps the
    old strict behavior and still reports missing selective plans;
  - fallback-only pure functions get direct `name/N` adapters over their old
    uniform `name/(N+2)` definitions, which lets selective HOF/direct code call
    pure fallback helpers by the selective direct ABI;
  - fallback-only nullary dict constructors get direct `dict/0` adapters that
    rebuild a selective-shaped dict tuple: pure methods are wrapped as direct
    closures, while effectful/open-row methods keep their CPS closures;
  - parameterized fallback dict constructors are intentionally not adapted yet:
    their direct ABI parameters are selective-shaped dictionaries, but their old
    fallback bodies expect uniform-shaped dependency dictionaries. Bridging
    those safely needs trait-method shape metadata for each dict parameter;
  - fallback uniform exports are intentionally preserved during the cutover:
    fallback definitions in other modules may still call remote uniform
    `name/(N+2)` or `dict/(N+2)` entries, so the merged module temporarily
    dual-exports the old fallback ABI and the new selective direct adapters;
  - private fallback dict constructors also get local direct adapters when the
    selective overlay needs them, but those adapters are not exported unless the
    old uniform constructor was exported;
  - direct multi-clause functions now lower as one grouped selective Core
    function: synthetic positional args feed a `case` over the argument tuple,
    with one arm per source clause. The planner proves the whole same-name
    group, not a single clause. Mixed/effectful multi-clause groups still fall
    back; examples `02-fibonacci` and `15-typechecking-errors` cover both
    paths;
  - `examples/28-deriving.saga` exposed a deep-but-finite compiler traversal in
    the old monadic optimizer/fallback path: raw monadic and raw selective Core
    could print, but `monadic-opt` overflowed the default Rust main-thread
    stack. The optimizer now walks linear `Bind`/`Let` spines iteratively while
    preserving binding-context state, so derived/generated code with deeply
    nested optimized `let` chains no longer needs a larger CLI stack;
  - stdlib cache fingerprints now include the backend, and selective builds
    compile stdlib modules through the same selective/fallback merge instead of
    reusing uniform-only stdlib beams;
  - added isolated project fixtures for stdlib dict use and local HOF direct
    callback so CLI tests do not race on a shared single-file `_build/dev`;
  - status: `cargo test -p saga selective_core --no-default-features` and
    `cargo test -p saga --test selective_core_cli` pass with the merged flagged
    backend.
- No-fallback e2e audit progress:
  - `saga test --selective-no-fallback base_test` now passes
    `25 passed, 0 failed`;
  - `saga test --selective-no-fallback pattern_matching_test` now passes
    `61 passed, 0 failed`;
  - direct pattern coverage now includes named/anonymous record patterns,
    punned fields, `as` aliases, string-prefix patterns, and binary string
    literal patterns;
  - grouped direct functions now support guarded clauses by lowering through
    value-level case chains instead of emitting ANF `let` expressions in Core
    guard position;
  - CPS case lowering also uses safe fallthrough chains, fixing the erlc
    `core_to_ssa` failure around synthetic `fail` in deep test lambdas;
  - handler-arm CPS lowering recognizes the important multishot shape
    `List.flat_map (fun x -> resume x) options` and lowers the callback as a
    direct closure that applies the current handler-arm continuation;
  - full `saga test --selective-no-fallback` now advances to dynamic
    multi-effect handler values:
    `let h = handler for Log, Validate { ... }; body with h`.
- Updated `docs/planning/selective-cps-value-matrix.md` to reflect the current
  state:
  - HOF direct specialization is no longer future work;
  - `RecordUpdate`, direct external calls, guarded case/function lowering, and
    handler-arm `flat_map` resume are marked supported in their current narrow
    forms;
  - handler values are promoted from a vague separate matrix to the next active
    producer/consumer discipline chunk.
- Implemented the first handler-value producer/consumer discipline slice:
  - selective lowering now threads the monadic translator's `HandlerValueMap`
    into the direct-first lowerer;
  - inline `handler for ...` values and named handler references lower to the
    same runtime shape as the uniform lowerer:
    `{__saga_handler_value, OpsByEffect, RuntimeReturn}`;
  - `OpsByEffect` groups arms by canonical effect name and installs dynamic
    handlers by extracting each per-effect op tuple into evidence;
  - return clauses lower as runtime return lambdas with `(value, evidence, k)`;
  - `if`-selected handler values now produce a common runtime handler tuple in
    each branch, covering `let logger = if dev then console_log else silent_log`;
  - dynamic `with h` can consume the runtime tuple and compose the handler
    return with the outer selective continuation.
- Tightened selective callback planning:
  - `--selective-no-fallback` is now correctly threaded into the selective
    lowerer from `emit_module_via_new_path`; strict mode no longer emits
    partial modules and waits for `erlc` to find missing definitions;
  - CPS callback arguments are now checked against the callee's expected
    callback shapes before lowering, so unsupported effectful callback bodies
    fall back/stop during planning instead of panicking while materializing the
    runtime CPS lambda.
- Current audit frontier after this slice:
  - `saga test --selective-no-fallback effects_test` now stops in stdlib at
    `run_writer`, before the EffectsTest module itself;
  - fallback-enabled `saga test --selective-codegen effects_test` currently
    reaches the old fallback lowerer and hits the known
    `lower_pure_expr: MExpr variant is not in Bind→Let's pure subset` panic
    once selective declines the unsupported `run_state`/effectful-callback
    shape. The next architecture decision is whether writer/state-style HOFs
    should be direct-specialized, adapted over fallback-only pure functions, or
    routed through a monadic fallback island.
