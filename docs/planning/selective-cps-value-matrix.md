# Selective CPS Value Discipline Matrix

This is the checklist for CPS callable values in the selective-uniform
backend. Its job is to keep us out of the old "forgot evidence and
continuation, got runtime badarity" failure mode.

The old lowerer on `main` is useful here as a source of historical case
families, not as code to port. The relevant old-lowerer signals are:

- `docs/effect-implementation.md` on `main` describes the old `CallEffectMap`
  source of truth for effectful calls, including `Var`, `QualifiedName`,
  `DictMethodAccess`, and lambda-headed calls.
- `src/codegen/call_effects.rs` on `main` classifies effectful call heads:
  named/qualified functions, dict method access, and lambda heads.
- `src/codegen/lower/mod.rs` on `main` has separate dispatch for effectful
  named/qualified calls, effectful variable calls, effectful dict method calls,
  lambda-headed effectful calls, eta-reduced effectful values, partial
  application, and CPS chaining for effectful arguments.
- `src/codegen/lower/effects.rs` on `main` has the handler-value families:
  static named handlers, conditional handlers, dynamic handlers, inline arms,
  return clauses, `resume`, and `finally`.

## Invariants

- A call site must never infer runtime arity from source arity alone.
- Direct code must not call or store a CPS callable as a plain BEAM function.
- Named CPS functions are not runtime values by default. They are shape
  metadata until a value position explicitly materializes an adapter closure.
- Runtime CPS closure values are real values. They carry source arity and CPS
  adapter arity in `LocalValueShape::RuntimeCpsCallable`.
- Control-flow expressions that produce CPS callable values must materialize
  runtime closures in each branch/arm.
- Pure callbacks are type-valid in effectful callback positions. Lowering must
  either choose a direct/pure HOF specialization before CPS, or explicitly wrap
  the pure callback with `fun args Ev K -> K(pure(args...))` when the selected
  callee ABI is CPS.
- Handled callbacks whose exposed type is pure should follow the same direct
  specialization path as ordinary pure callbacks.
- If a callback value can dynamically be either leaky or pure, the common
  runtime representation is CPS; pure branches must be wrapped explicitly.
- Unsupported cells should fail during selective classification/lowering, not
  by producing Core that can fail with badarity.

## Shape Vocabulary

| Shape | Meaning | Runtime Value? | Current Lowering |
| --- | --- | --- | --- |
| `PureCallable { arity }` | Proven direct callable value, usually a lambda or local pure function value | Yes | Core `fun`, `FunRef`, or remote `make_fun` |
| `PureCallableFromUseType` | A local value that may be pure callable; arity is recovered from type/use site | Yes if pure | Direct callback support uses this cautiously |
| `CpsCallable { module, name, source_arity, adapter_arity, effects }` | Named local/imported CPS function reference | No, metadata only | Materialize explicit CPS adapter closure at value use |
| `RuntimeCpsCallable { source_arity, adapter_arity }` | Runtime CPS closure parameter or alias/materialized branch result | Yes | Core variable or `let` of a runtime closure |

## Producer Matrix

These are expression/value shapes that can produce a callable value.

| Producer | Example | Current Status | Correct Rule | Next Action |
| --- | --- | --- | --- | --- |
| Named same-module pure function | `let f = inc` | Supported | `PureCallable` / direct fun ref | Keep |
| Imported pure function | `let f = Helper.inc` | Supported | Remote `make_fun(Module, Name, Arity)` | Keep |
| Direct pure lambda | `let f = fun x -> x + 1` | Supported in direct subset | Runtime Core `fun` with direct arity | Keep |
| Named same-module CPS function | `let f = read_value` | Supported in CPS islands | Metadata-only `CpsCallable`; no Core binding until value use | Keep |
| Imported CPS function | `let f = Effects.read_value` | Supported in CPS islands | Metadata-only `CpsCallable`; value use creates adapter closure calling remote `/N+2` | Keep |
| Runtime CPS callback parameter | `apply_eff f = f ()` | Supported | `RuntimeCpsCallable`; call as `apply F(args..., Ev, K)` | Keep |
| Alias of named CPS function | `let g = f` where `f = read_value` | Supported | Metadata-only alias until runtime value is needed | Keep |
| Alias of runtime CPS closure | `let g = f` where `f` is a callback param | Supported | Emit real `let <G> = F`; track `RuntimeCpsCallable` | Keep |
| `if` returning CPS callables | `let f = if c then read_a else read_b` | Supported | Materialize Core `case` whose arms return adapter closures; result is `RuntimeCpsCallable` | Keep |
| `case` returning CPS callables | `let f = case c { True -> read_a; False -> read_b }` | Supported | Same as `if`, with direct patterns/guards only | Keep |
| Mixed CPS and pure branch/case | `if c then read_value else pure_value` | Supported via CPS fallback | Common representation is CPS; pure branch uses explicit pure-to-CPS adapter | Later direct-specialize when branch is statically pure |
| Pure function where effectful callback is expected | `apply_eff pure_value` | Supported via CPS fallback | First prefer direct HOF specialization when the whole call is net pure; otherwise use explicit pure-to-CPS adapter | Add direct-specialization pass later |
| Handled callback where effectful callback is expected | `apply_eff (fun x -> leaky x with h)` | Open/risk | If exposed callback type is pure, use direct HOF specialization or pure-to-CPS adapter fallback | Add fixture with local handler |
| CPS lambda value | `let f = fun () -> read! ()` | Open | Needs CPS lambda compilation as runtime closure | Later, after pure-to-CPS policy |
| Lambda-headed CPS call | `(fun x -> read! ()) ()` | Open | Old lowerer had `lower_lambda_head_call`; selective needs island-local CPS lambda path | Later |
| Partial application of CPS function | `let f = read_with_prefix p` | Open | Must materialize closure with remaining args plus `Ev,K`; do not use source arity | Later |
| Eta-reduced effect op ref | `let f = read` / operation callback | Open | Old lowerer had eta-reduced effect-op handling; selective needs explicit op adapter design | Later |
| Trait method value, pure | `let f = show` after dict elaboration | Partially supported for direct monomorphic method calls | Direct dict method extraction only in narrow subset | Broaden when trait specialization starts |
| Trait method value, CPS/effectful | `let f = someEffectfulMethod` | Open | Needs dict method CPS shape from trait metadata and explicit adapter closure | High priority before trait specialization |
| Dict method call, CPS/effectful | `x.effectfulMethod arg` after elaboration | Open | Old lowerer had effectful `DictMethodAccess` dispatch | High priority for traits |
| Constructor/tuple/list/record containing CPS callable | `(read_value, other)` | Open/reject | Storing CPS values in data needs representation policy; avoid accidental BEAM funs | Add negative tests before support |
| Handler expression value | `handler for E { ... }` | Open in selective | Build runtime handler tuple/return clause closure | Separate handler-value matrix |
| Named handler alias | `let h = my_handler` | Static handler support narrow | Static aliases can stay metadata; conditional/dynamic need runtime tuple | Extend handler path separately |
| Handler chosen by `if`/`case` | `let h = if c then h1 else h2` | Open in selective | Old lowerer has conditional handler item | Separate handler-value matrix |
| Let-rec/local function | `let fun f x = ...` | Open in selective for CPS values | Needs entry metadata and `LetRec` lowering with direct/CPS plan | Later |

## Consumer Matrix

These are places that consume a callable value or call shape.

| Consumer | Example | Current Status | Correct Rule | Next Action |
| --- | --- | --- | --- | --- |
| Direct call of direct function | `inc x` | Supported | Direct `/N` call | Keep |
| Direct call of CPS named function | `read_value ()` outside island | Rejected unless body/island classified | Must route through CPS island or adapter entry | Keep |
| CPS island call of named CPS function | `read_value ()` | Supported | Call source-name adapter `/N+2` with current `Ev,K` | Keep |
| CPS island call of runtime CPS closure | `f ()` | Supported | `apply F(args..., Ev, K)` | Keep |
| CPS function value as argument | `apply_eff read_value` / aliased variant | Supported for named CPS values | Materialize CPS adapter closure as argument | Keep |
| Runtime CPS closure as argument | `apply_outer f` | Supported for direct alias/arg cases | Pass Core variable; callee applies with `Ev,K` | Keep |
| Pure callable as direct callback argument | `apply_it inc` | Supported | Direct fun value, source arity | Keep |
| Pure callable as CPS callback argument | `apply_eff inc` | Supported via CPS fallback | Prefer direct HOF specialization if the selected HOF call can stay pure; otherwise explicit pure-to-CPS adapter | Add direct-specialization pass later |
| Effectful argument inside effectful outer call | `outer (read! ())` or `outer (decode x)` | Partially represented by monadic `Bind` sequencing | Old lowerer had `effectful_arg_idxs` chaining; selective should rely on monadic sequencing inside islands | Add fixtures when app args become non-trivial |
| Effectful callback argument inside effectful outer call | `outer read_value (effect_arg!)` | Open | Need both adapter closure and effectful-arg sequencing | Later |
| Return continuation value | final result of CPS island | Supported for direct atoms; CPS callable result supported for `if`/`case` bound values | Returning CPS callable out of island needs representation policy | Add guardrail |
| Yield argument | `op!(read_value)` | Open/risk | If op expects CPS callback, needs adapter; otherwise reject/store policy | Later |
| Handler arm `resume` value | `resume read_value` | Open/risk | Resuming CPS callable value needs adapter/materialized representation | Later |
| Handler return clause value | `return _ = read_value` | Open/risk | Same as return continuation value | Later |
| Direct data storage | `(read_value, 1)` | Open/reject | Needs representation policy before support | Add negative tests |
| Exported/public function returning CPS callable | `pub fun choose : ... -> Unit -> Int needs {E}` | Open | Cross-module ABI for returned CPS closure must be explicit | Later |

## MExpr Coverage Matrix

This is the selective lowerer's practical checklist over monadic IR.

| `MExpr` Form | Direct Subset | CPS Island Computation | CPS Callable Value Producer | Notes |
| --- | --- | --- | --- | --- |
| `Pure(Atom)` | Supported for direct atoms | Supported as direct result | Supported for named CPS and runtime CPS vars | Atomic values are the main shape-entry point |
| `Yield` | Rejected | Supported | Not a callable producer yet | Yield args use `atom_is_cps_value_subset`; callback args need policy |
| `Bind` | Supported for direct values | Supported | Supported for CPS metadata/runtime aliases and branch/case materialization | Core sequencing boundary |
| `Let` | Rejected/optimizer-only currently | Not primary path | Open | If optimizer emits it, mirror `Bind` discipline |
| `Ensure` | Rejected direct | Static finally paths supported in handlers | Open | Cleanup result should not create callable values yet |
| `If` | Supported direct | Supported in CPS islands | Supported for compatible CPS callable branches | Emits Core `case` |
| `Case` | Supported direct | Supported in CPS islands | Supported for compatible CPS callable arms | Direct patterns/guards only for now |
| `App` | Supported for direct call shapes | Supported for named/runtime CPS and direct fallback | Consumer, not producer | Pure-to-CPS callback args still open |
| `With` | Rejected direct | Supported for static handler subset | Not a callable producer yet | Handler values separate |
| `Resume` | Rejected direct | Supported inside handler arm subset | Open for CPS callable resume value | Needs adapter policy |
| `FieldAccess` | Supported direct | Via direct fallback | Not supported for CPS callable storage | Records containing callbacks open |
| `RecordUpdate` | Rejected | Rejected | Open/reject | Same storage policy |
| `DictMethodAccess` | Supported narrowly for pure trait method call/value shape | Open for CPS/effectful methods | Open | Key trait-specialization dependency |
| `ForeignCall` | Rejected/direct external via intrinsics only | Rejected | Not callable producer | Later external functions need explicit shape metadata |
| `BinOp` / `UnaryMinus` | Supported | Direct fallback | No | Keep |
| `BitString` | Rejected | Rejected | No | Later |
| `Receive` | Rejected | Rejected | Open | Actor/native effects later |
| `LetFun` | Rejected | Rejected | Open | Needed for local recursive helpers |
| `HandlerValue` | Rejected | Rejected/open | Handler-value producer | Separate matrix |

## Old Lowerer Cross-Check

The old lowerer on `main` says these are real cases, even if selective should
not port the implementation:

| Old Lowerer Family | Evidence from `main` | Selective Status |
| --- | --- | --- |
| Per-call effect classification | `call_effects.rs` comments list `Var`, `QualifiedName`, `DictMethodAccess`, `Lambda`; docs say one `CallEffectMap` per `App` | Selective currently does local `CallShape`; may want a selective call-shape prepass later |
| Effectful variable call | `lower_effectful_var_call` | Supported for runtime CPS callback vars in islands |
| Effectful named/qualified call | effectful call emission in `lower/mod.rs`, qualified call handling | Supported for local/imported CPS adapters |
| Effectful dict method call | `lower_effectful_method_call`, `DictMethodAccess` classification | Open/high priority |
| Lambda-headed effectful call | `lower_lambda_head_call` | Open |
| Eta-reduced effectful value | `lower_eta_reduced_effect_expr` | Partially covered for named CPS functions; op refs/partial apps open |
| Effectful argument CPS chaining | `effectful_arg_idxs` paths | Mostly delegated to monadic `Bind`; needs fixtures for nested call arguments |
| Partial application | old lowerer handles supplied args vs total arity | Open for CPS callables |
| Handler values | static/conditional/dynamic handler item code in `effects.rs` | Static with narrow handler bodies supported; dynamic/conditional handler values open |
| `finally` / cleanup | old handler finalization paths | Narrow static resume/abort finally supported |

## Related Specialization Track

Not every effect-shaped type should pay CPS forever. Some cases are generic
CPS for correctness but direct-specializable when the actual call site is
static.

| Shape | Example | Desired Optimization | Notes |
| --- | --- | --- | --- |
| Pure callback passed to effect-capable HOF | `List.iter pure_cb` where `iter` accepts `a -> Unit needs {E}` | Select pure/direct HOF specialization before building a pure-to-CPS adapter | If mixed with a leaky callback at runtime, common representation is CPS |
| Fully-handled callback passed to effect-capable HOF | `List.iter (fun x -> op! x with h)` where exposed callback type is pure | Same as pure callback | The callback body may use effects internally, but no effects leak from its type |
| Static Reader/config handler | `serialize record with { read_options () = resume opts }` | Turn handler lookup into explicit config argument, then optionally inline/propagate | The slow CPS/evidence path remains correctness fallback |
| Static tail-resume operation arm | `op args = resume value` | Direct substitution/argumentization when safe | Existing narrow finally/resume support is a stepping stone, not the final optimizer |

## Suggested Next Chunks

1. **Direct HOF specialization for net-pure callbacks**
   - The pure-to-CPS fallback now handles `apply_eff pure_value` correctly.
   - Add a handled-callback fixture whose exposed callback type is pure.
   - Implement direct HOF specialization so statically net-pure callback calls
     can avoid the fallback wrapper and CPS callback ABI.
   - Keep the fallback wrapper for dynamic/mixed cases where the selected ABI is
     still CPS.

2. **Effectful trait method calls and values**
   - Use trait metadata to classify CPS `DictMethodAccess`.
   - Support or reject effectful trait method values explicitly.
   - This is important before trait specialization because specialization needs
     clean call/value boundaries.

3. **CPS lambdas**
   - Support runtime CPS closure generation for `fun ... -> effectful body`.
   - Then lambda-headed CPS calls can reuse the same closure/call path.

4. **Storage guardrails**
   - Add negative tests for tuples/records/constructors/lists containing CPS
     callable values.
   - Support later only if we choose a representation.

5. **Handler value matrix**
   - Split handler values from callable values.
   - Cover static alias, conditional handler, dynamic handler expression,
     return clause, resume, finally, and imported handler modules.
