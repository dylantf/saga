# Selective-Uniform Implementation Log

This is the durable working memory for the selective-uniform backend
experiment. Update it at the end of every session that changes the design,
code, tests, or known state.

The charter is `docs/planning/selective-uniform-effects.md`.

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
- `examples/optimization/selective-uniform/23-local-pure-lambda-call.saga`
  - Current result: emits a direct local lambda value as a Core `fun`, records
    its proven source arity in local shape metadata, and applies it via
    `CallShape::LocalCallable`.
- `examples/optimization/selective-uniform/24-cps-island-local-pure-lambda.saga`
  - Current result: emits a CPS island that binds a direct local lambda before
    `read! ()`; the resumed continuation applies the lambda to the operation
    result and then calls `_ReturnK`. This pins that proven direct callable
    values can survive inside CPS island continuations without guessing arity.

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
  closure and ignoring the captured continuation. `finally`, full
  abort/result-marker routing, dynamic/native/composite handlers, and handler
  values remain unsupported in `lower_selective`.
- CPS islands support proven direct local lambda values. They still do not
  support higher-order CPS callable values or unknown callback parameters.
- `lower_selective` computes imported entry metadata for already-compiled
  non-stdlib user modules. Remote effect-row calls may lower to direct remote
  calls only when that imported metadata proves a direct entry exists; otherwise
  they remain `CallShape::Cps` boundaries.
- Imported effect-row `BeamFunction` arity from backend resolution may be the
  source arity or the adapter arity depending on where the resolved symbol came
  from. Remote direct-entry matching accepts only imported metadata-proven
  direct arities, checking both the resolved arity and `resolved_arity - 2`.

## Pipeline Integration Milestones

Current mode is **inspect-driven Core shape work**:

```text
parse/typecheck/elaborate
-> ANF
-> whole-module monadic translation
-> lower_selective
-> print Core via inspect --stage selective-core
```

This is intentionally not the final architecture. It lets us prove direct/CPS
entry shapes without yet replacing the production build pipeline. Normal
`saga build` / `saga run` still go through `emit_module_with_context` and the
existing monadic/uniform lowerer unless an explicit integration point is added.

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
   return-clause continuation case are working; narrow direct abort arms are
   working; broader handler semantics are still open.
2. **Selective entrypoint/bootstrap slice.** Add the minimal wrapper/evidence
   setup needed for a normal `main` entry to call direct or CPS-shaped code
   correctly.
3. **Experimental build/run toggle.** Add an explicit compiler option or flag
   that routes normal `emit_module_with_context` through `lower_selective` for
   supported modules. Keep the default production path unchanged.
4. **First pure/direct end-to-end run.** Use the experimental toggle to run a
   boring direct program through parse -> emit -> erlc -> erl, e.g.
   `main () = 42` or `main () = { print_stdout "ok"; () }`.
5. **First handled-effect end-to-end run.** Run a trivial handled effect, e.g.
   `read! () with forty_two`, through the same parse -> emit -> erlc -> erl
   path.
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
