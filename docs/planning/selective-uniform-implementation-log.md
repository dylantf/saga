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
- Ordinary local function-valued variables are deliberately not callable in the
  direct subset yet. They need explicit function-value shape metadata instead
  of arity guessing.
- Direct app lowering now goes through a single `CallShape` classifier in
  `lower_selective`: intrinsic, direct BEAM callable, or tagged local callable.
  Adding new app shapes should go through that classifier.
- Imported pure `BeamFunction`s may lower as remote direct calls when backend
  resolution reports an empty effect row. Local functions still require the
  direct subset/fixed-point classification before they can be called directly.

## Next Session Checklist

1. Read this log and `docs/planning/selective-uniform-effects.md`.
2. Check `git status --short`.
3. Decide the next vertical slice:
   - move pure direct lowering earlier than monadic IR, or
   - add the first explicit trait/dictionary direct slice.
4. If taking the trait slice, start from the observed `show 42` shape:
   `DictRef(__dict_Std_Base_Show_std_int_Std_Int_Int)` ->
   `DictMethodAccess(..., Std.Base.Show[0])` -> method call.
5. Keep updating focused fixtures/tests as each tiny subset starts working.

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
- Verification:
  - `cargo run --bin saga -- inspect examples/optimization/selective-uniform/01-pure-direct.saga --stage selective-core`
    emits direct `add1/1`, `twice/1`, and `main/1`.
  - The same `selective-core` command succeeds for `02-recursive-if.saga` and
    `03-pure-val.saga`.
  - `cargo test -p saga runtime_shape` passed.
  - `cargo test -p saga selective_core` passed.
  - `cargo fmt` run.
