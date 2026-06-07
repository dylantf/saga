# Direct-First Effect Shape Matrix

Status: **phase 1 classifier-boundary checklist complete**.

This matrix adapts the useful case-family discipline from the
`selective-uniform` branch's `selective-cps-value-matrix.md`.

It is not a design for a new backend. It is a checklist for hardening `main`'s
existing direct-first lowerer:

```text
classify shape once
lower from that classification
fallback means current direct/CPS behavior, not fallback Core
unknown ABI choices fail loudly
```

Optimization-specific cases now live in
[direct-first-optimizer-matrix.md](./direct-first-optimizer-matrix.md). Keep
this file focused on correct runtime shape; use the optimizer matrix for faster
equivalent shapes.

## Invariants

- A call site must never infer runtime arity from source arity alone.
- Direct code must not call a CPS callable as a plain BEAM function.
- CPS calls are represented by classifier metadata before lowering.
- Lowering may consume classifier facts but should not rediscover per-call
  effectfulness from lexical scope or ad hoc type peeks.
- Named CPS functions are metadata until a value position explicitly
  materializes a closure or adapter.
- Runtime CPS closure values are real values and must be called with
  `(user_args..., _Evidence, _ReturnK)`.
- Open-row calls must forward caller evidence, even when their static effect
  prefix is empty.
- Unsupported runtime representations should fail in classification/lowering,
  not as generated Core Erlang `badarity`.

## App Call Matrix

| Shape | Example | Current Source Of Truth | Desired Rule | Phase |
| --- | --- | --- | --- | --- |
| Direct named local call | `inc x` | `call_effects` => no CPS plan | Emit ordinary call | 1 |
| Direct imported call | `List.length xs` | `call_effects` + backend resolve | Emit ordinary remote/local call | 1 |
| Closed CPS named call | `read_value ()` | `CallEffectInfo::StaticOps` | Project/pin evidence and pass `_ReturnK` | 1 |
| Open-row CPS named call | `wrap cb` where callee needs `{..e}` | `CallEffectInfo::RowForwarded` | Forward ambient evidence and pass `_ReturnK` | 1 |
| Runtime CPS variable call | `f ()` where `f` is effectful/open-row callback | lexical facts inside `call_effects` | Apply variable with evidence + `_ReturnK` | 1 |
| Dict method direct call | `show x` after elaboration | `call_effects` + trait metadata | Extract/apply method directly | 1 |
| Dict method CPS call | effectful trait method | `call_effects` + trait/impl effects | Extract/apply method with evidence + `_ReturnK` | 1 |
| Lambda-headed direct call | `(fun x -> x + 1) n` | lambda type in `call_effects` | Lower as normal apply | 1 |
| Lambda-headed closed CPS call | `(fun x -> op! x) v` | lambda type in `call_effects` | Compile lambda with CPS shape and call with projected evidence | 1 |
| Lambda-headed open-row call | `(fun f -> f ()) cb` | lambda type in `call_effects` | Compile lambda with open CPS shape and forward evidence | 1 |
| Partial application of direct function | `String.replace "x"` | lowerer arity metadata | Emit direct closure | 1 |
| Partial application of CPS function | `read_with_prefix p` | partial-app shape helpers | Emit closure that takes remaining user args plus evidence/K | 1/guard |
| Effectful argument to direct outer call | `Some (read! ())` | nested effect walk + CPS chaining | CPS-chain argument before direct outer construction | 1 |
| Effectful argument to CPS outer call | `outer (inner ())` | nested effect walk + CPS chaining | CPS-chain inner before outer CPS call | 1 |
| Unknown app head with CPS type | dynamic computed callee | currently limited | Require explicit runtime shape or fail | guard |

## Callable Value Producer Matrix

| Producer | Example | Desired Representation | Phase |
| --- | --- | --- | --- |
| Named direct function value | `let f = inc` | BEAM fun/ref with direct arity | 1 |
| Imported direct function value | `let f = List.length` | Remote fun/ref with direct arity | 1 |
| Direct lambda value | `fun x -> x + 1` | Direct Core fun | 1 |
| Named CPS function value | `let f = read_value` | Metadata first; materialize CPS closure at value boundary | 1 |
| Imported CPS function value | `let f = Effects.read_value` | Metadata first; materialize adapter closure when needed | 1 |
| Runtime CPS callback parameter | `apply f = f ()` | Runtime CPS closure variable | 1 |
| Alias of runtime CPS closure | `let g = f` | Preserve runtime CPS closure shape | 1 |
| Alias of named CPS function | `let g = read_value` | Preserve metadata until materialization | 1/guard |
| If/case returning CPS callables | `if c then read_a else read_b` | Materialize common runtime CPS closure representation | guard |
| Mixed direct/CPS branch value | `if c then pure else effectful` | Explicit adapter to common shape or unsupported | guard |
| CPS callable stored in tuple/record/ADT | `(read_value, 1)` | Unsupported until representation policy exists | guard |
| Handler expression value | `handler for E { ... }` | Runtime handler tuple shape | later |
| Named handler alias | `let h = my_handler` | Static metadata or runtime handler tuple when escaped | later |

## Callable Value Consumer Matrix

| Consumer | Example | Desired Rule | Phase |
| --- | --- | --- | --- |
| Direct call of direct value | `f x` | Apply direct arity | 1 |
| CPS call of runtime CPS value | `f x` in CPS context | Apply `f(args..., evidence, k)` | 1 |
| CPS function value passed as effectful callback | `apply_eff read_value` | Materialize CPS closure/adapter | 1 |
| Direct function passed as effectful callback | `apply_eff inc` | Prefer direct HOF specialization later; otherwise pure-to-CPS adapter where required | guard/later |
| Effectful callback passed to direct wrapper | stream/thunk callback | Only allowed with explicit expected callback shape | guard |
| Return CPS callable from function | `choose () = read_value` | Needs exported/runtime representation policy | guard |
| Resume with CPS callable value | `resume read_value` | Unsupported until adapter policy exists | guard |
| Handler return clause returns CPS callable | `return _ = read_value` | Unsupported until adapter policy exists | guard |

## Effect Op And Handler Matrix

| Shape | Example | Current Rule | Desired Rule | Phase |
| --- | --- | --- | --- | --- |
| Plain effect op | `log! msg` | Evidence lookup + handler closure apply | Keep current CPS path | 1 |
| Closed-row op lookup | known effect layout | Static tuple indexing | Keep current fast lookup | 1 |
| Open-row op lookup | row-polymorphic caller | Runtime `find_evidence` | Keep current fallback | 1 |
| BEAM-native op under native handler | `Actor.self! () with beam_actor` | `direct_ops` native fast path | Re-express as effect-op plan later | 2 |
| Abort-only handler arm | no `resume` | Pass cheap continuation marker | Keep current no-resume classification | 1 |
| Static tail-resume pure arm | `get () = resume value` | Currently generic CPS unless native/special | First local direct optimization | 3 |
| Non-tail or multishot resume | resume captured/called multiple times | Generic CPS | Keep generic CPS | 3 guard |
| `finally` handler | cleanup around resume/abort | Existing handler lowering | Do not direct-specialize initially | guard |
| Dynamic handler value | handler chosen at runtime | Runtime handler tuple/evidence | Keep generic path | later |
| Same-effect nested handler | inner shadows outer | Evidence insertion/shadowing | Keep current semantics | 1 |

## Trait And Generic Specialization Matrix

This track starts only after call/value shape classification is explicit.
Dictionary passing remains the correctness fallback.

| Shape | Example | Desired Optimization | Phase |
| --- | --- | --- | --- |
| Immediate monomorphic method call | known dict + known method slot | Direct method body call/lowering | later |
| Imported public monomorphic dict | `Show Int` from stdlib | Direct call if metadata admits body safely | later |
| Parameterized dict constructor chain | `ToJson (List Person)` | Thread known sub-dicts through method body | later |
| Dict-only local elision | dict tuple built only to extract known method | Skip tuple construction if erased | later |
| Known Generic output shape | derived `ToJson Person` | Emit final serializer directly, skip runtime `Rep` walk | later |
| Dynamic dictionary | dictionary parameter unknown | Normal dictionary tuple dispatch | always |

## Phase 1 Working Set

The first pass finished these before any optimization:

1. Done: keep `CallEffectInfo::cps_call_plan()` as the lowerer's only CPS-call
   extraction API.
2. Done: move any remaining lowerer-local `CallEffectKind` matching back into
   `call_effects.rs`.
3. Done: add small guard tests for open-row empty-prefix cases, including a
   lambda-headed open-row call.
4. Done: add loud lowering failures for classified-CPS apps that fail to reach
   a CPS dispatch path.
5. Next: start an audit trace now that the classification boundary is stable.
