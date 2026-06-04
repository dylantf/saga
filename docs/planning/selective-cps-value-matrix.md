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
| Pure function where effectful callback is expected | `apply_eff pure_value` | Supported with local/imported direct HOF specialization when the callee body becomes direct under pure callbacks; CPS fallback remains | First prefer direct HOF specialization when the whole call is net pure; otherwise use explicit pure-to-CPS adapter | Keep; broaden only when new HOF value shapes appear |
| Handled callback where effectful callback is expected | `apply_eff handled_value` where `handled_value` uses an internal handler | Supported for named same-module callbacks, accumulator-style handler bodies, and direct pure wrappers such as `catch_panic (fun () -> body () with h)` | If exposed callback type is pure, use direct HOF specialization, direct CPS island lowering, or pure-to-CPS adapter fallback | Broaden only when new handled callback shapes appear |
| CPS lambda value | `let f = fun () -> read! ()` | Supported in CPS islands | Materialize runtime closure with user args plus evidence/continuation | Keep |
| Lambda-headed CPS call | `(fun x -> read! ()) ()` | Supported in CPS islands | Materialize/apply runtime CPS closure; no source-arity guessing | Keep |
| Partial application of CPS function | `let f = read_with_prefix p` | Open | Must materialize closure with remaining args plus `Ev,K`; do not use source arity | Later |
| Eta-reduced effect op ref | `let f = read` / operation callback | Open | Old lowerer had eta-reduced effect-op handling; selective needs explicit op adapter design | Later |
| Trait method value, pure | `let f = show` after dict elaboration | Supported for local/imported direct HOF callback values when the concrete dict is known, including generic dict chains | Known dispatcher lambdas partially applied to known dicts lower to direct closures; dynamic dict method values still use runtime extraction | Broaden only when new escaped/dynamic value shapes appear |
| Trait method value, CPS/effectful | `let f = someEffectfulMethod` | Supported for local and imported dicts, including generic constructors with dictionary parameters | Extract method closure as `RuntimeCpsCallable` using method/access type metadata | Trait specialization later |
| Dict method call, CPS/effectful | `x.effectfulMethod arg` after elaboration | Supported for local and imported dicts, including nested dispatch through dictionary parameters | Extract method closure and apply with evidence/continuation | Trait specialization later |
| Constructor/tuple/list/record containing CPS callable | `(read_value, other)` | Explicitly rejected for tuple/record/constructor | Storing CPS values in data needs representation policy; avoid accidental BEAM funs | Add list fixture when list literals are in this path |
| Handler expression value | `handler for E { ... }` | Supported for the current dynamic-handler e2e shapes, including multi-effect values | Build runtime `{__saga_handler_value, OpsByEffect, RuntimeReturn}` tuple with canonical per-effect op tuples | Broaden for abort/finally stress later |
| Named handler alias | `let h = my_handler` | Supported for local/imported names present in the translator's handler-value map | Static aliases can stay metadata; escaped/dynamic handlers materialize the runtime tuple | Keep |
| Handler chosen by `if`/`case` | `let h = if c then h1 else h2` | `if` supported for named/inline handler values; `case` still open | Branches produce the common runtime handler-value representation | Add `case` if examples need it |
| Constructor-stored handled thunk | `Stream (fun () -> producer () with stream_of)` | Supported for net-pure direct CPS-island lambdas; handler-arm delayed resume may be nested in constructors | Store the direct thunk, but lower its body through the CPS island/handler-arm machinery | Keep; stress with imported stream tests |
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
| Pure callable as CPS callback argument | `apply_eff inc` | Supported with local/imported direct HOF specialization for statically pure callback args; CPS fallback remains | Prefer direct HOF specialization if the selected HOF call can stay pure; otherwise explicit pure-to-CPS adapter | Broaden to aliases later |
| Effectful callback argument to pure direct wrapper | `Stream.from_gen (fun () -> count_down 3)` | Supported for direct callees whose parameter type is effectful callback-shaped | Direct call sites lower effectful callback slots as CPS runtime closures while leaving pure callback slots direct | Keep; stress with imported stream tests |
| Handler-arm HOF resume | `List.flat_map (fun x -> resume x) xs` inside an operation arm | Supported for imported/direct `flat_map` identity-resume shape | Lower callback as a direct closure that applies the current handler-arm continuation; preserves multishot list semantics | Generalize only after more handler-arm HOF shapes appear |
| Handler arm returning delayed-resume lambda | `tell x = fun acc -> (resume ()) (x :: acc)` | Supported for writer/state-style accumulator handlers | Return a direct Core lambda, but lower its body under the handler arm continuation so resume runs when the accumulator function is applied | Keep; stress with finally/abort later |
| Effectful argument inside effectful outer call | `outer (read! ())` or `outer (decode x)` | Partially represented by monadic `Bind` sequencing | Old lowerer had `effectful_arg_idxs` chaining; selective should rely on monadic sequencing inside islands | Add fixtures when app args become non-trivial |
| Effectful callback argument inside effectful outer call | `outer read_value (effect_arg!)` | Open | Need both adapter closure and effectful-arg sequencing | Later |
| Return continuation value | final result of CPS island | Supported for direct atoms; CPS callable result supported for `if`/`case` bound values | Returning CPS callable out of island needs representation policy | Add guardrail |
| Yield argument | `op!(read_value)` where the op parameter is callback-shaped | Supported for direct args and proven CPS callable args | Effect protocol boundaries may carry runtime CPS closures; arbitrary data storage of CPS values is still rejected | Keep; type/op-param metadata could make diagnostics sharper later |
| Handler arm `resume` value | `resume read_value` | Explicitly rejected | Resuming CPS callable value needs adapter/materialized representation | Later |
| Handler return clause value | `return _ = read_value` | Explicitly rejected | Same as return continuation value | Later |
| Direct data storage | `(read_value, 1)` | Explicitly rejected for tuple/record/constructor | Needs representation policy before support | Add list fixture when list literals are in this path |
| Exported/public function returning CPS callable | `pub fun choose : ... -> Unit -> Int needs {E}` | Open | Cross-module ABI for returned CPS closure must be explicit | Later |

## MExpr Coverage Matrix

This is the selective lowerer's practical checklist over monadic IR.

| `MExpr` Form | Direct Subset | CPS Island Computation | CPS Callable Value Producer | Notes |
| --- | --- | --- | --- | --- |
| `Pure(Atom)` | Supported for direct atoms | Supported as direct result | Supported for named CPS and runtime CPS vars | Atomic values are the main shape-entry point |
| `Yield` | Rejected | Supported with direct args or proven CPS callable protocol args | Not a callable producer | Protocol args mirror lowering: direct atoms lower normally, pure callables adapt to CPS closures, CPS callable values materialize runtime closures |
| `Bind` | Supported for direct values | Supported | Supported for CPS metadata/runtime aliases and branch/case materialization | Core sequencing boundary |
| `Let` | Supported where it appears like `Bind` in selective paths | Supported like `Bind` in the active CPS/direct subsets | Same alias/value rules as `Bind` | Keep watching optimizer-emitted shapes |
| `Ensure` | Rejected direct | Static finally paths supported in handlers | Open | Cleanup result should not create callable values yet |
| `If` | Supported direct | Supported in CPS islands | Supported for compatible CPS callable branches | Emits Core `case` |
| `Case` | Supported direct, including record/string patterns and guarded arms via value-level chains | Supported in CPS islands with safe fallthrough chains | Supported for compatible CPS callable arms | Keep; add bitstring/receive later |
| `App` | Supported for direct call shapes, direct external calls, HOF specialization, and selected handler-arm HOF resume shapes | Supported for named/runtime CPS, CPS lambda heads, direct fallback, and direct HOF specialization | Consumer, not producer | Remaining app work is partial application / effectful argument stress |
| `With` | Supported only for return-only static handlers over direct bodies | Supported for static handler subset | Not a callable producer yet | Handler values separate |
| `Resume` | Rejected direct | Supported inside handler arm subset for direct values | CPS callable resume values explicitly rejected | Needs adapter policy before support |
| `FieldAccess` | Supported direct | Via direct fallback | Not supported for CPS callable storage | Records containing callbacks open |
| `RecordUpdate` | Supported direct for direct fields | Via direct fallback where expression stays direct | Open/reject for CPS callable storage | Same storage policy |
| `DictMethodAccess` | Supported narrowly for pure trait method call/value shape | Supported for local/imported CPS/effectful methods, including generic dictionary-parameter constructors | Produces `RuntimeCpsCallable` for effectful methods | Trait specialization later |
| `ForeignCall` | Supported in direct subset for direct args; direct external apps filter Saga `Unit` for niladic native calls | Via direct fallback when direct-safe | Not callable producer | Effectful externals still need explicit shape metadata |
| `BinOp` / `UnaryMinus` | Supported | Direct fallback | No | Keep |
| `BitString` | Rejected | Rejected | No | Later |
| `Receive` | Supported, including `after` and BEAM system-message patterns | Supported in CPS islands, including `after` and BEAM system-message patterns | Open | Direct support exists because `receive` maps to a Core Erlang keyword; it is not an actor effect op |
| `LetFun` | Rejected | Rejected | Open | Needed for local recursive helpers |
| `HandlerValue` | Rejected in direct subset today | Supported as a CPS-island value producer | Handler-value producer | Broaden for abort/finally stress later |

## Native Handler Matrix

Native handlers are not selected by effect name alone. The user chooses a
handler, and only known backend-native handlers get this lowering category.
Other handlers for the same effects continue through the ordinary
direct/CPS/static-handler rules.

| Handler | Effects / Ops Covered | Current Status | Correct Rule | Next Action |
| --- | --- | --- | --- | --- |
| `Std.Actor.beam_actor` | `Actor.self`, `Process.spawn/send/exit`, `Monitor.monitor`, `Link.link/unlink`, `Timer.sleep/send_after/cancel_timer`; plus direct `receive` syntax used by actor code | Covered by `beam-actor-native-project`, including strict `selective-core --selective-no-fallback` inspection and default runtime run | Selective lowering owns this category directly: classify native handler bodies as direct-shaped when proved, lower `MHandler::Native` wrappers as no-ops only after their bodies are direct, and lower `BackendAtom` / `BackendSpawnThunk` in direct/native code. No monadic optimizer pass is in the execution path. | Keep; add new rows only for future backend-native handlers |
| `Std.Ref.beam_ref` / `Std.Ref.ets_ref` | `Ref.new/get/set/modify` | Covered for the current `RefTest` runtime path under the default selective backend; native direct rewrites exist for both BEAM ref and ETS ref shapes, including HOF callback boundaries such as `List.iter` | Native `with` is not automatically transparent. The supported path rewrites known native operations in selective lowering and bridges imported/open-row HOF calls through the CPS entry when the callback slot is CPS-shaped. ETS table initialization is shared between selective direct lowering and bootstrap wrappers. | Keep; strict `--selective-no-fallback` may still expose unrelated test-runner/frontier declarations before reaching runtime-equivalent coverage |

## Old Lowerer Cross-Check

The old lowerer on `main` says these are real cases, even if selective should
not port the implementation:

| Old Lowerer Family | Evidence from `main` | Selective Status |
| --- | --- | --- |
| Per-call effect classification | `call_effects.rs` comments list `Var`, `QualifiedName`, `DictMethodAccess`, `Lambda`; docs say one `CallEffectMap` per `App` | Selective currently does local `CallShape`; may want a selective call-shape prepass later |
| Effectful variable call | `lower_effectful_var_call` | Supported for runtime CPS callback vars in islands |
| Effectful named/qualified call | effectful call emission in `lower/mod.rs`, qualified call handling | Supported for local/imported CPS adapters |
| Effectful dict method call | `lower_effectful_method_call`, `DictMethodAccess` classification | Supported for local/imported dicts, including generic dictionary-parameter constructors |
| Lambda-headed effectful call | `lower_lambda_head_call` | Supported for selective CPS islands |
| Eta-reduced effectful value | `lower_eta_reduced_effect_expr` | Partially covered for named CPS functions; op refs/partial apps open |
| Effectful argument CPS chaining | `effectful_arg_idxs` paths | Mostly delegated to monadic `Bind`; needs fixtures for nested call arguments |
| Partial application | old lowerer handles supplied args vs total arity | Open for CPS callables |
| Handler values | static/conditional/dynamic handler item code in `effects.rs` | Inline, named, and `if`-selected dynamic handler values are supported for current e2e shapes; `case`/abort/finally stress remains |
| `finally` / cleanup | old handler finalization paths | Static resume cleanup supported, including cleanup that references arm-local bindings and protocol callback params; abort/return-clause routing remains separate |

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
| Known constructor/output-shape specialization | `impl ToJson for SomeGenericType` | Specialize through known constructors/fields to emit the final output shape directly, skipping runtime traversal of generic intermediate nodes | Schedule after trait call/value ABI is correct; especially relevant for derived/generic encoders/decoders |

## Trait Specialization Track

Dictionary passing remains the correctness fallback. Specialization should be
chosen at call sites when the compiler can prove the concrete dictionary and
method shape. This keeps dynamic dictionaries and polymorphic APIs valid while
letting hot monomorphic paths skip tuple construction and method-closure
extraction.

| Slice | Goal | Notes |
| --- | --- | --- |
| Immediate monomorphic method call | Rewrite a known `DictMethodAccess(dict_ctor, method)` followed by apply into direct method-body lowering | Local known dict constructors are covered. Imported monomorphic constructors are covered when their method body is admitted into the caller, e.g. `Show Bool` and `Show Int`; imported methods that reference private ordinary Saga helpers still fall back unless those helpers are cloneable |
| Impl-method metadata | Record, import, and query the trait name, impl type, method index/name, source arity, direct/CPS shape, and required sub-dicts for each dict constructor | `ModuleCodegenInfo::trait_impl_dicts` now carries per-method metadata for imported/public dicts. Selective lowering also consumes collected imported `MDictConstructor` bodies for direct call-site specialization |
| Generic dict constructor args | Preserve and specialize constructor chains such as `__dict_ToJson_List(__dict_ToJson_Person)` | Local and imported admitted chains can now inline known generic method calls through known sub-dict aliases. Public/fallback dict constructor definitions are still emitted for module boundaries |
| Dict-only local elision | Remove call-site dictionary tuple construction when the dict value is only used to reach a known method call | First direct-lowering slice is covered for local/imported known dict locals erased by specialization. The pass uses a source candidate proof plus a lowered-Core no-reference guard |
| Effectful impl methods | Choose direct, CPS, or direct-with-island based on the impl method's lowering plan | Same ABI discipline as ordinary functions: pure direct methods call direct, leaky methods call CPS, handled/net-pure methods may get direct island wrappers |
| Trait method values | Specialize `let f = method` separately from immediate calls | Known pure method values can now become direct closures for local/imported direct HOF callback positions; known CPS methods need explicit CPS adapter closures; dynamic dict methods still extract runtime closures |
| Generic functions with `where` clauses | Optional call-site specialization of functions whose dictionary params are statically known | Later than direct method calls. Avoid blanket monomorphization until naming/cache policy is clear |
| Known constructor/output-shape specialization | For derived encoders/decoders, use Generic/record/ADT shape at compile time to emit final output directly | `Generic` is an internal derivation substrate here. No user-facing opt-out/attribute yet; if specialization cannot prove the shape, fall back to the normal Generic/dict path |

## Suggested Next Chunks

1. **Trait specialization: immediate monomorphic method calls**
   - Local known dict constructors are now covered for the immediate shape:
     `let dict = __dict_T(); let method = DictMethodAccess(dict, i);
     method(args...)`.
   - Current lowering skips dict tuple construction, method closure extraction,
     and method closure apply by directly lowering the known method lambda
     body at the call site.
   - Imported dict constructors and parameterized/generic dict constructor
     chains intentionally remain on the existing dict-passing fallback until
     the metadata slices below land.

2. **Trait specialization metadata**
   - `ModuleCodegenInfo::trait_impl_dicts` now records per-method metadata:
     method name, source arity, trait-declared effects/open-row flag, and
     direct/CPS runtime shape.
   - The dict-level metadata still records trait name, trait type args, impl
     target type, dict constructor name/arity, required sub-dict constraints,
     and impl-level effects.
   - Selective lowering now consumes collected imported dictionary constructor
     bodies for admitted monomorphic direct methods. `Show Bool` and `Show Int`
     are the current stdlib canaries. `Show Int` proves private imported
     externals can be admitted when their BEAM target is resolved.

2.5. **Imported private helper policy**
   - Imported method bodies may now reference private same-module externals
     when name resolution already knows their BEAM target. This covers shapes
     such as `Show Int`, whose body calls private `Std.Int.to_string`, an
     `@external` helper.
   - Imported private ordinary Saga helpers still fall back unless the optimizer
     can clone the helper safely. That keeps us from generating remote calls to
     non-exported implementation details.
   - Remaining resolutions for ordinary private helpers: make selected stdlib
     helpers public, add selective helper-clone support like the monadic
     optimizer path, or add hidden generated exports if we decide that is an
     acceptable module-boundary tradeoff.

3. **Generic dict constructor chains**
   - Recognize chains such as
     `__dict_ToJson_List(__dict_ToJson_Person)`.
   - Local and imported direct selective lowering now store known direct method
     lambdas and thread known sub-dict aliases through generic impl-method
     bodies. This lets a generic method such as `Size (Box a)` inline its
     nested `Size a` method call when the sub-dict is statically known.
   - Public/fallback dict constructor functions are still emitted for module
     boundaries, but direct selective callers can now elide local dict tuple
     construction when specialization erases the use.

4. **Dict-only local elision**
   - Direct selective lowering now skips dictionary constructor lets when the
     resulting known dict local is erased by method specialization.
   - The implementation keeps this as an allocation/tuple-construction cleanup,
     not an ABI fallback requirement: it first identifies dict locals that are
     only candidates for known method dispatch, then confirms the lowered Core
     body no longer mentions the Core variable before omitting the binding.
   - Covered shape:
     `let d = __dict_T(subdicts...); let m = DictMethodAccess(d, i);
     m(args...)`, including harmless direct lets between the method binding and
     the final call and nested generic sub-dict chains.

5. **Known constructor/output-shape specialization**
   - After concrete trait calls are addressable, use Generic/record/ADT shape
     information to emit final derived outputs directly, especially
     `ToJson`/`FromJson`.
   - Do not add user-facing specialization attributes yet. If the compiler
     cannot prove the shape, use the normal Generic/dict fallback.
   - First rewrite landed: the direct lowerer tracks scoped known pure atoms
     and collapses unguarded cases whose scrutinee is a known constructor,
     tuple, or literal. Pattern variables bind known sub-values for the chosen
     arm, so nested constructor ladders can collapse one step at a time.
  - Covered canary: `routed-derive-options/01-routed-derive-options.saga`
     now lowers the direct static `serialize` variant from the residual
     `Rep__User(Adt("User", Variant(Leaf(5))))` constructor/case ladder to the
     proven leaf encoder path, with no runtime `Rep__User`/`std_generic_*`
     allocation or traversal in that hot direct variant.
   - Second rewrite landed: known atom/pattern facts now thread through
     CPS/static-handler lowering as well as direct lowering. This lets the
     split-trait record shape in
     `routed-derive-options/03-split-trait-record.saga` skip the hot
     `Rep__User -> Record -> And -> Labeled -> Leaf` traversal in `main`
     while preserving the normal dict/fallback path for unsupported dynamic
     uses.
   - Current limits: guarded arms, string-prefix patterns, and bitstring
     patterns still fall back to normal case lowering.
   - Cleanup landed: known direct atoms, known direct/CPS lambdas, and known
     dictionary values now flow through the shared `known_facts` helper module.
     Direct and CPS lowering still decide what Core to emit, but fact binding,
     structural pattern proofs, and known-atom expression evaluation now have a
     single home.

6. **Std.Test runner strict frontier**
   - Current strict blocker:
     `saga test --selective-no-fallback` compiles stdlib and the test modules,
     then stops at the project-level CPS-shaped `tests` aggregator function.
   - This is likely a direct runner/control-flow shape in the test harness,
     not a new effect ABI category.
   - Likely next investigation: inspect optimized monadic/Core for the
     generated/aggregated `tests` function and decide whether it needs a
     grouped direct-runner lowering case, a direct subset extension, or a
     classification correction.

7. **Derived generic dict constructor frontier**
   - Current audit result:
     `saga test --selective-no-fallback generic_fromjson_test` passes, and
     `examples/28-deriving.saga` runs under `--selective-codegen`.
   - Derived generic constructors currently lower as direct tuple-producing
     dict constructors in the inspected `GenericFromjsonTest` selective core.
   - Keep this on the schedule for optimization, not current ABI correctness:
     specialize known constructor/output shapes after trait specialization
     work, especially for JSON encoders/decoders.

8. **EffectsTest abort/return routing frontier**
   - Cleared: `saga test --selective-no-fallback effects_test` now reports
     `61 passed, 0 failed`.
   - Static `with` now has marked abort/value routing and a lexical delimiter
     stack for perform-site continuations.
   - Static handler install elision is paused until it can be reintroduced with
     a real grouped/imported-call lowering proof.

8. **Effectful trait method calls and values**
   - Local and imported dict constructors plus effectful method calls/values
     are covered, including generic constructors with dictionary parameters.
   - Next trait work can move from ABI correctness to specialization:
     monomorphic call-site specialization, known constructor/output-shape
     specialization, and direct handling of net-pure trait dispatch.

9. **CPS lambdas and partial application**
   - Basic runtime CPS closure generation is covered for callback arguments,
     effect protocol arguments, let-bound aliases, and lambda-headed calls.
   - Remaining lambda work is CPS partial application/captured callback
     parameter stress-testing, not the base closure ABI.

10. **Storage guardrails**
   - Tuple/record/constructor negative tests are covered.
   - Add list-literal coverage once list literals hit this selective path.
   - Support later only if we choose a representation.

11. **Handler value matrix**
   - Split handler values from callable values.
   - Inline, named, and `if`-selected dynamic handler values are covered for
     current e2e shapes.
   - Remaining stress: `case`-selected handlers, abort arms, `finally`, and
     imported handler modules if examples expose new shapes.

## Recently Cleared Frontiers

- **Selective backend no longer has a separate monadic optimizer path:** the
  default backend lowers from raw monadic translation, overlays selective Core
  on the raw fallback, and keeps `--selective-no-fallback` as the audit switch.
  `inspect` now exposes `monadic` and `selective-core`; optimizer-only stages
  were removed so wins must be owned by selective lowering or later peepholes.
- **Newly exposed native-handler frontier:** without optimizer-created native
  variants, functions called inside `with beam_actor` can still be emitted as
  ordinary CPS entries and perform evidence lookup with empty evidence. The
  next native-handler chunk is selective-owned native variants or equivalent
  call routing for functions invoked under `MHandler::Native`; this replaces
  the old optimizer's behind-the-IR native variant rewrite.
- **Stream HOF strict frontier:** `Std.Stream.for_each` now lowers as an
  open-row CPS HOF (`for_each/4`) that calls its callback with
  evidence/continuation and recurs on the CPS ABI.
- **AtomicRef recursive receive frontier:** `Std.AtomicRef.lock_server` now
  lowers as a CPS recursive receive loop with nested receive and actor
  evidence lookup.
- **Bitstring direct/CPS island frontier:** direct lowering now supports
  bitstring patterns in `case` arms, and CPS islands can construct bitstrings
  and sequence direct helper calls before CPS-relevant work. `advanced_test`
  now passes under `--selective-no-fallback`.
- **Handler re-yield frontier:** handler arms can now re-yield through the
  outer evidence using the arm continuation, covering
  `EffectsTest.reabort_wrapped`.
- **Local external call frontier:** bodyless local `@external` signatures are
  now recorded from passthrough `FunSignature` declarations and can be called
  directly inside selective CPS islands. This clears `AdvancedTest.tests`
  under strict selective-core.
- **Native Ref/HOF runtime frontier:** `RefTest` runs under
  `--selective-codegen`. The selective path now preserves imported open-row HOF
  callback shapes, bridges static-empty CPS HOF calls from direct/native code,
  rewrites known `beam_ref`/`ets_ref` native operations, and shares ETS table
  initialization helpers across bootstrap/selective/monadic native paths.
