# Typed back-end tree

Status: approved 2026-10-13. Branch `typed-ir`, off `effect-anf` (`c27ba1d4`).
From a read-only survey; nothing in it was built or run, and every size is an
estimate from reading. Follows
[sound-function-representation.md](sound-function-representation.md) ("One
rule for effect routing").

## Why

After typechecking the back end works on the surface AST, with types,
resolution, call classification and handler facts in side tables keyed by
NodeId. Every pass that rebuilds the tree has to carry the entries along by
hand. That convention is where the last class of miscompiles came from.

The goal is not a new lowerer. It is to move every *decision* out of the
lowerer into one builder that produces a small typed tree in which each node
carries what the lowerer needs. The lowerer then only emits BEAM shapes.

## Decisions (one line each; overrule any of them)

1. Operands are **values**: forms whose evaluation runs no user code and
   cannot perform. Exactly today's `is_atomic` set in `normalize.rs`. Every
   call (pure ones too), primitive op and branching form is a `let` value or
   a tail.
2. This means pure code gains a `let` per nested call in emitted Core Erlang.
   Accepted, gated at step 1 on the five benchmarks and on `erlc` time for the
   stdlib. If the gate fails, stop and reconsider before step 2.
3. One expression type, two positions. Tail position is `Body { stmts, tail }`.
4. The seven classification rules become node kinds. `Call::new` computes the
   convention from the callee, so it cannot go stale under rewrites.
5. Migrate through a shallow builder: during migration `Val` and `Expr` have
   an `Ast(&ast::Expr)` variant, the builder builds one node deep, and each
   construct has exactly one implementation at all times. Then flip the
   builder to deep and delete the variant.
6. The generic fold moves onto the IR last. It is optional for correctness.
7. Every IR node is closed: absolute references, no key into a per-module
   table. There is no per-module semantic cache, so no serialisation.
8. The IR carries `EffectId`, `Row { effects, open }` and `OpRef`, and nothing
   positional about evidence, so the later evidence-as-a-map switch touches
   only the evidence emitter and the bridge.
9. Handler arms carry `ResumeUse` as data, set by `HandlerArm::new`.

## The IR (first draft)

```rust
// src/codegen/ir.rs  (names are absolute, never module-relative)
pub type Ty = Option<Rc<Type>>;          // None only for nodes elaboration made
pub struct Local { pub name: Rc<str>, pub id: u32 }
pub struct EffectId(pub Rc<str>);        // canonical family name
pub struct Row { pub effects: Vec<EffectId>, pub open: bool }   // no positions
pub enum Conv { Direct, Cps(Row) }
pub struct FnAbi { pub user_arity: usize, pub conv: Conv }
pub struct FnRef { pub module: Rc<str>, pub name: Rc<str>, pub abi: FnAbi,
                   pub external: Option<(Rc<str>, Rc<str>)> }
pub enum FnRepr { Bare, Tagged, BareEmptyRow }
pub struct OpRef { pub effect: EffectId, pub op: Rc<str> }
pub enum CtorRef { Nil, Cons, Bool(bool), Atom(Rc<str>), Tagged(Rc<str>) }

// Values: evaluating one runs no user code and cannot perform.
pub struct Val { pub kind: ValKind, pub ty: Ty, pub span: Span }
pub enum ValKind {
    Lit(Lit), Local(Local),
    Fn { target: FnRef, repr: FnRepr },
    LocalFn { name: Local, abi: FnAbi, repr: FnRepr },
    Const(FnRef),                         // arity-0 top-level binding
    Intrinsic(IntrinsicId),
    Ctor { ctor: CtorRef, args: Vec<Val> }, CtorFn { ctor: CtorRef, arity: usize },
    Tuple(Vec<Val>),
    Record { tag: Rc<str>, slots: Vec<Val> },          // named and anonymous
    Field { base: Box<Val>, slot: u32 },
    Lambda(Box<Lambda>),
    OpFn { op: OpRef, repr: FnRepr },                  // `log!` unapplied
    Dict(FnRef), DictParam(Local), DictApp { ctor: FnRef, args: Vec<Val> },
    DictMethod { dict: Box<Val>, slot: u32, nullary: bool, pure_view: Option<usize> },
    DictSuper { dict: Box<Val>, slot: u32 },
    Handler(Box<HandlerLit>), HandlerRef(HandlerId),
}
pub struct Lambda { pub params: Vec<Pat>, pub body: Body, pub repr: FnRepr }  // flattened

// Computations: only ever a let value or a tail.
pub struct Expr { pub kind: ExprKind, pub ty: Ty, pub span: Span, pub performs: bool }
pub enum ExprKind {
    Val(Val),
    Prim { op: PrimOp, args: Vec<Val> },
    Call(Call),
    Partial { target: FnRef, args: Vec<Val>, repr: FnRepr },
    Perform { op: OpRef, args: Vec<Val> },
    Resume(Val),
    Foreign { module: Rc<str>, fun: Rc<str>, args: Vec<Val> },
    Intrinsic { id: IntrinsicId, args: Vec<Val> },     // print, dbg, catch_panic, panic, todo
    RecordUpdate { base: Val, arity: u32, slots: Vec<(u32, Val)> },
    BitString(Vec<BitSeg<Val>>),
    If { cond: Val, then: Body, else_: Body },         // also `&&` / `||`
    Case { scrut: Val, arms: Vec<Arm> },
    Do { binds: Vec<(Pat, Body)>, success: Body, else_arms: Vec<Arm> },
    Receive { arms: Vec<Arm>, after: Option<(Val, Body)> },
    Block(Body),
    With { body: Body, handler: HandlerUse },
}
pub struct Body { pub stmts: Vec<Stmt>, pub tail: Box<Expr> }
pub enum Stmt {
    Let { pat: Pat, value: Expr, assert: bool, span: Span },   // `e;` is Let{Wild}
    LetFn { name: Local, abi: FnAbi, clauses: Vec<Clause> },
}
pub struct Call { pub callee: Callee, pub args: Vec<Val>, pub conv: Conv }  // via Call::new only
pub enum Callee {
    Fn(FnRef), LocalFn(Local, FnAbi),                                     // rule 4, saturated
    DictMethod { dict: Val, slot: u32, known_impl: Option<FnRef> },       // rule 5
    Value(Val),                                                           // rules 6 and 7
}
pub struct Arm { pub pat: Pat, pub guard: Option<Guard>, pub body: Body }
pub struct Clause { pub params: Vec<Pat>, pub guard: Option<Guard>, pub body: Body }
pub enum Guard { Simple(GuardExpr), Complex(Body) }
pub enum GuardExpr { Val(Val), Prim(PrimOp, Vec<GuardExpr>) }
pub enum Pat {
    Wild, Var(Local, Ty), Lit(Lit), Tuple(Vec<Pat>),
    Ctor { ctor: CtorRef, args: Vec<Pat> },
    Record { tag: Rc<str>, arity: u32, fields: Vec<(u32, Pat)>, as_name: Option<Local> },
    StrPrefix { prefix: String, rest: Box<Pat> }, Bits(Vec<BitSeg<Pat>>),
}
pub struct HandlerLit { pub effects: Vec<EffectId>, pub arms: Vec<HandlerArm>,
                        pub ret: Option<(Pat, Body)> }
pub struct HandlerArm { pub effect: EffectId, pub op: Rc<str>, pub params: Vec<Pat>,
                        pub body: Body, pub finally: Option<Body>,
                        pub resume: ResumeUse }                // set by HandlerArm::new
pub enum ResumeUse { Never, EveryTail, SomeTails, ValueUsed, Escapes }
pub enum HandlerUse {
    Inline(HandlerLit),
    Static { handler: HandlerId, captures: Vec<(Local, Val)> },
    Cond { cond: Val, then: HandlerId, else_: HandlerId },
    Dynamic { value: Val, effects: Vec<EffectId>, has_return: bool },
}
pub struct Module { pub name: Rc<str>, pub funs: Vec<FunDef>, pub dicts: Vec<DictCtor>,
                    pub handlers: Vec<HandlerDef>, pub externals: Vec<ExternalWrapper> }
pub struct FunDef { pub name: Rc<str>, pub abi: FnAbi, pub clauses: Vec<Clause>, pub span: Span }
pub struct DictCtor { pub name: FnRef, pub params: Vec<Local>, pub supers: Vec<Val>,
                      pub methods: Vec<(Lambda, Conv)> }       // replaces forced_lambda_cps
```

Types are optional because elaboration makes nodes with none; the facts the
lowerer needs (`repr`, `conv`) are mandatory and set by a positive rule at
construction. `performs` is cached by the constructors.

Where each surface `ExprKind` goes:

| Source | IR |
|---|---|
| `Lit` | `Val::Lit` |
| `Var`, `QualifiedName` | `Val::{Local, Fn, LocalFn, Const, Intrinsic, HandlerRef, Ctor}` |
| `Constructor` | `Val::Ctor` or `Val::CtorFn` |
| `App` | by head: `Perform`, `Val::Ctor` / `Val::DictApp`, `Intrinsic`, `Call`, `Partial`; an over-applied call is split in two |
| `BinOp`, `UnaryMinus` | `Prim`; `&&` and `\|\|` become `If` |
| `If`, `Case`, `Block`, `Do`, `Receive`, `With`, `Resume`, `BitString`, `RecordUpdate` | same-named `Expr` |
| `Lambda`, `Tuple`, `FieldAccess`, `RecordCreate`, `AnonRecordCreate`, `HandlerExpr` | `Val` |
| `EffectCall` | `Perform` (nullary), `Val::OpFn` (unapplied), or the head of a `Perform` |
| `DictMethodAccess`, `DictSuperAccess`, `DictRef` | `Val::DictMethod` / `Callee::DictMethod`, `Val::DictSuper`, `Val::Dict` / `DictParam` |
| `ForeignCall` | `Foreign` |
| `Ascription`, `RecordBuild`, `Pipe`, `BinOpChain`, `PipeBack`, `ComposeForward`, `Cons`, `ListLit`, `StringInterp`, `ListComprehension` | do not exist |

## End-state pipeline

```
per module, once:   elaborate -> BUILD IR -> local fold (IR)   => CompiledModule { codegen_info, ir }
per emitted module: cross-module fold (IR) -> facts (IR) -> lower (IR) -> print
```

## What the IR absorbs

`expr_types` / `type_at_node`, `effect_at_node`, front resolution,
`resolved_effect_call_name`, the backend `ResolutionMap`, `ConstructorAtoms`,
`record_fields` and its fallbacks, `EffectAbiPlan` and its fallbacks, resume
analysis (computed three ways today), the name-keyed handler maps,
`current_handler_source_module` (65 sites), the fold's origins, five carried
tables and the thread-local id record. Kept and computed from IR: helper and
HOF facts, `value_repr` (its result stored as `FnRepr`).

## Steps

Each merges on its own. Oracle: the existing suites plus a `.core` snapshot
(one hash per emitted module over stdlib, examples and fixtures). Steps 3 to
9 must leave the snapshot unchanged.

| # | Step | Est. + / − | Emitted code |
|---|---|---|---|
| 0 | Snapshot harness; one `CompiledModule` constructor (it is built by struct literal in nine places); fix the stale `emit(src)` line in `AGENTS.md` | +200 / −60 | same |
| 1 | Value-normal form on the AST: normalize lifts every non-value operand; guard-safe guards exempt; record fields in written order. **Gate: benchmarks and stdlib `erlc` time** | ±100 | changes |
| 2 | `ir.rs`; value forms through the builder; `lower_val`; the operand assert moves to one place | +450 / −200 | changes |
| 3 | Calls: `Call` / `Callee`, builder case, one `lower_call` | +400 / −950 | same |
| 4 | Bodies, lets, control forms, guards | +300 / −450 | same |
| 5 | Lambdas (`repr`), `Perform`, `Resume`, op references | +250 / −450 | same |
| 6 | `With`, `HandlerUse`, `HandlerArm::new`; name-keyed handler maps move behind the builder | +400 / −650 | same |
| 7 | Fast paths off the AST (port, or settle with handler unification) | +500 / −1,000 | same |
| 8 | Flip the builder to deep; delete `normalize.rs`, `effect_position.rs`, `anf.rs`, the `Ast` variants | +350 / −1,750 | same |
| 9 | Per-module IR in `CompiledModule`; imported bodies lowered from producer IR; delete `call_effects.rs`, plan precompute, `current_handler_source_module`, most of `semantic.rs`, the resolve walker | +450 / −2,300 | same |
| 10 | Fold on the IR; delete origins, carried tables, the thread-local, `handler_analysis.rs`, `trait_dispatch.rs`, the AST in `CompiledModule` | +1,000 / −2,500 | reviewed diff |

Estimated total +4,300 / −10,300. First net smaller at step 3. Stop points:
after 6, after 8, after 9.

Does not shrink: `beam_interop.rs`, `evidence.rs`, `effects/analysis.rs`,
`cerl.rs`, `runtime_shape.rs`, and emission proper. The lowerer stays around
11k lines because most of it is BEAM shape emission.

## Follow-ups this is shaped for

- **One way to compile a handler.** `Resume` exists only as a `let` value or
  a tail, so "the code after `resume` is a continuation" is one case of the
  let rule. Chain, delimit or reset becomes a function of `HandlerUse`, the
  arms' `ResumeUse` and `finally`. The fast paths become optional IR
  rewrites. Step 7 is where the two meet: do not port a fast path that
  handler unification will restate. Parked branch `stageb-delim` holds the
  acceptance tests and the two rejected simpler alternatives.
- **Evidence as a map.** See decision 8.

## Probable bugs found while reading (none reproduced)

- `let h = if c then a else b` used outside a `with` appears to lower to the
  then-handler regardless of `c`; the condition is evaluated once per `with`
  site, not at the `let`.
- `panic` and `todo` are matched by spelling before resolution, so a user
  function or local of that name would be intercepted.
- A body-only change in a project module may leave a consumer that inlined
  that body stale: the rebuild fingerprint hashes interfaces, not bodies.
- Dead arms for `ListLit` and `Ascription` in `ops.rs` and
  `exprs/handlers.rs`.

## Outcome

### Step 0 (2026-10-13)

- `tests/core_snapshot.rs`, hashes in `tests/fixtures/core_snapshot.txt`:
  172 units (34 stdlib modules, 129 single-file programs from `examples/`,
  `examples/bugs/` and `examples/optimization/*/`, 9 modules of
  `tests/fixtures/modules`). No `erlc`; about 17 s in a debug build.
  `SAGA_SNAPSHOT_BLESS=1` rewrites the list, `SAGA_SNAPSHOT_DUMP=<dir>`
  (with `SAGA_SNAPSHOT_FILTER`) writes the text.
- Output is deterministic as it stands: two runs gave byte-identical text
  for all 172 units. Nothing is normalised before hashing.
- Two units are pinned in a failing state that predates this work:
  `examples/bugs/nullary-handler-fn.saga` (`panic`: unknown handler item)
  and `selective-uniform/03-pure-val.saga` (`rejected` by the typechecker).
- `CompiledModule::new` is the only place the struct is built, with
  `metadata_only` and `entry` as two named calls of it. `Default` is gone.

### Step 1 (2026-10-13)

`normalize` lifts every operand that is not a value; `check_body` and
`lower_operand` reject one. `src/`: 453 lines added, 187 removed, of which
180 added are tests.

- Snapshot: 94 of 172 units changed (19 of 34 stdlib modules). Compared
  structurally (every `call M:F`, `apply F/N`, closure application, `fun`,
  `case`, `letrec`, `try`, `receive`, `primop`, tagged closure, per unit),
  93 differ only in `let`s (1,742 more in total). No fast path was lost.
- One unit gained a fast path: `examples/44-handle-bindings.saga`.
  `resume dbg msg` is now `let t = dbg msg; resume t`, the block shape the
  static tail-resume inlining already accepted when written by hand, so two
  inline handlers are inlined instead of installed. The same kind of gain
  is possible wherever a matcher asks for a plain argument and used to see
  a pure call: handler factory arguments (`recover_handler_factory_binding`)
  and imported static helper arguments.
- One lowering root was not normalized: the arm of a handler declaration
  inlined by static tail-resume (`lower_static_tail_resume_op`). It now is.
  Found by the strengthened `lower_operand`.
- Guards: a guard made only of operators, variables and literals is left as
  written (and the operand check is off while it is lowered). Every other
  guard is normalized as a body. Only `case` lowers such a guard as a body;
  function clauses, local functions, `receive` and `do ... else` arms emit
  it in guard position, where `erlc` accepts the `let`s and `case`s it now
  contains. A call to a user function in those guards did not compile
  before and still does not.
- `a && b` / `a || b`: an `if` when the right operand is not a value,
  unchanged otherwise.
- Record literals: fields are evaluated in written order, by the pass and
  by the lowerer. Before, a literal with pure fields evaluated them in
  declared order.
- Gate, release builds, same machine and session, `elapsed_ms`:
  `closed_row_hot_op` 794 / 784 / 779 before, 791 / 779 / 786 after;
  `open_row_hot_op` 1325 / 1324 / 1323 before, 1311 / 1310 / 1313 after;
  `deep_call_chain` 1690 / 1685 / 1663 / 1785 before,
  1707 / 1679 / 2078 / 1674 / 1676 after (the two high readings are one
  run each).
- Compile time, `saga build examples/42-dijkstra.saga` in an empty
  directory (so the stdlib is compiled too), `real`: 0.93 / 0.93 / 0.93 s
  before, 0.93 / 0.93 / 0.94 s after.
- Suite: 1,766 passed, 0 failed, 5 ignored (1,757 before, plus the snapshot
  test and 8 unit tests). No text-asserting test needed a change, and the
  function-shape matrix fixtures are unchanged. Clippy: the same 4 warnings.
- Stdlib `.core`: 401,111 bytes before, 426,357 after (+6.3%); the whole
  corpus 1,494,360 to 1,574,141 (+5.3%).

### Step 2 (2026-10-13)

`src/codegen/ir.rs` (the types) and `src/codegen/lower/build.rs` (the shallow
builder, methods on the `Lowerer`). `src/`: 725 lines added, 601 removed.
Snapshot unchanged.

- Through the builder and the one `lower_val`: literals, variables,
  references to top-level, imported, external and block-local functions,
  constants, intrinsics, constructors (nullary, applied, as functions),
  tuples, record literals, field access, `DictRef`, `DictMethodAccess`,
  `DictSuperAccess`, and a named handler used as a value (`HandlerRef`, whose
  lowering is still `lower_handler_def_to_tuple`). Left for later steps:
  lambdas (step 5, body and `repr` together), operation references (5),
  handler literals (6), `DictApp` (with calls, step 3).
- Deleted: `lower_resolved_value_ref`, `tagged_resolved_value_ref`,
  `lower_local_fun_ref`, `lower_ctor_with_origin`,
  `constructor_function_value`, `lower_record_fields`, `fun_arity`,
  `constructor_origin_module_for`, `assert_operand`, and the `lower_expr` arms
  of the migrated kinds.
- The operand check is in `Lowerer::operand`, the only function that makes
  a `Val::Ast`. `lower_operand` is `operand` then `lower_val`. Three sites
  that are not migrated yet call `operand` for the check alone (call
  arguments in `calls.rs` and `function_values.rs`, operation arguments in
  `effects/call.rs`). The dictionary of a method or superclass access is now
  checked too; it was lowered unchecked.
- Deviations from the draft, all because nothing reads the missing part yet:
  `Val` is the enum itself, with no `ty` or `span`. Names are `String`.
  `Local` is the Core Erlang variable name, without an id. `FnRef` is
  `{ module, name, abi }` where `module` is the Erlang module (`None` for the
  module being emitted) and `abi` is the existing `CallableAbi`; there is no
  `external` field because the builder settles wrapper or Erlang target, and
  no `FnAbi`/`Conv`/`Row` yet. `LocalFn` holds an `FnRef` like `Fn`.
  `Record` is `{ tag, arity, fields: Vec<(slot, Val)> }` with the fields in
  written order, since that is the order they are evaluated in.
  `Intrinsic` is `{ name, arity }`. `CtorRef::Atom` is a `&'static str`.
- One theoretical difference: a bare reference to a function of the module
  being emitted took its arity from `fun_info[name]` when present, else from
  the resolved ABI. It is now always the declared ABI. They differ only for
  an `@external` function whose name a block-local function elsewhere in the
  module reuses (block-local functions overwrite `fun_info` by bare name and
  are never removed). A check that they agree did not fire on the snapshot
  corpus, the codegen unit tests or the effect property tests.
