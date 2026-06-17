# Trait Dictionary Passing

Traits are compiled via **dictionary passing**: each trait becomes a tuple of method closures, and `where` clauses become extra function parameters that receive these tuples at runtime.

```
# Source
trait Show a { fun show : a -> String }
impl Show for Int { show n = int_to_string n }
fun print_it : a -> String where {a: Show}
print_it x = show x

# After elaboration (conceptual)
__dict_Std_Base_Show_Int = { fun n -> int_to_string n }
print_it __dict_Show_a x = element(1, __dict_Show_a)(x)
```

Three compiler phases cooperate: the **typechecker** records evidence about which trait constraints apply at each call site, the **elaborator** transforms the AST to thread dictionary arguments, and the **lowerer** emits Core Erlang tuple operations.

A fourth, earlier concern — **default method bodies** — is independent of dict passing but worth describing alongside it since it sits in the same trait pipeline. See [Default Method Bodies](#default-method-bodies) below.

Trait method effects are part of the type/effect contract, not payload baked
into the dictionary. The typechecker records method effect capability on the
trait method and records each impl method's actual effects in
`ImplInfo.method_effects`. At runtime, effectful dict methods use the normal
effectful function ABI: user args plus `_Evidence` and `_ReturnK`. Evidence is
threaded at the call site, where handlers are in scope; dictionary constructors
do not capture handlers.

---

## Default Method Bodies

Source: `src/derive.rs::inherit_trait_defaults`, `src/parser/decl.rs::parse_trait_def`

Trait declarations may attach a default body to any method:

```saga
trait ToJson a {
  fun to_json_with : Options -> a -> String
  fun to_json : a -> String
  to_json x = to_json_with default_options x   # default body
}
```

When an impl omits a method that has a default, the default fires; when the impl provides the method explicitly, the explicit body wins. Defaults are independent per method — a trait can mix defaulted and non-defaulted methods freely.

### Parse Representation

`TraitMethod.default_body: Option<TraitDefaultBody>` mirrors `ImplMethod`'s `(params, body)` shape (`src/ast.rs`). The parser ([src/parser/decl.rs:824-846](../src/parser/decl.rs#L824-L846)) peeks for an `Ident` matching the just-declared method name immediately after the signature; if it sees one, it parses `<pats>... = <expr>` and attaches the result.

### The Inheritance Pass

Defaults are a pre-typecheck AST transformation. After `expand_derives` runs, `inherit_trait_defaults` walks every `Decl::ImplDef`:

1. Look the trait up in the same `DeriveScope` used by routed derives (merges local + imported `TraitDef`s).
2. For each trait method the impl doesn't provide that has a `default_body`, clone the default into the impl as a synthetic `ImplMethod`.
3. Deep-clone the body with **fresh `NodeId`s** via `crate::desugar::freshen_expr_ids` / `freshen_pat_ids` so resolver/evidence/LSP state keyed on NodeId doesn't collide across impls.

After this pass every impl carries one `ImplMethod` per trait method. Every later phase — name resolution, typechecking, elaboration, codegen — sees a complete impl and needs no knowledge of defaults. In particular, dict construction in `elaborate.rs` works unchanged: the dict tuple has one slot per trait method, populated from the impl's now-complete `methods` list.

Method calls inside a cloned default body resolve through the trait dispatch path described in the rest of this document. A default like `to_json x = to_json_with default_options x` cloned into `impl ToJson for Person` produces a regular call to `to_json_with` on a `Person`-typed argument, which the typechecker resolves to `Person`'s `to_json_with` impl method like any other trait call.

### Interaction with Routed Derives

`derive_routed` ([src/derive.rs:793-825](../src/derive.rs#L793-L825)) skips defaulted methods when synthesizing the bridge and delegating impls — there's no need to invent a body when the inheritance pass will fill one in. For a trait whose every method has a default body, the derive errors (nothing to synthesize). Otherwise the bridge and delegating impls carry only the routed (non-defaulted) methods; the inheritance pass clones the defaults into both.

This is the headline interaction: library authors mark "this method is the routed one; that method is a convenience wrapper" purely by giving the wrapper a default body. The derive synthesizer doesn't need to know which is which.

### Pre-Binding for Default Body References

Default bodies (and explicit impl method bodies) are checked in Pass 6 (`register_all_impls`), before the main pass checks top-level function bodies. `pre_bind_functions` ([src/typechecker/check_decl.rs](../src/typechecker/check_decl.rs)) pre-binds `Decl::FunBinding` names with fresh vars, so a default body like `to_json x = to_json_with default_options x` can reference a top-level zero-arity binding `default_options = ...` defined anywhere in the module. When the main pass eventually checks that binding's RHS, it unifies the inferred type against the pre-bound var.

### Known Limits

- **No mutual-recursion detection.** Default `a` calls `b`, default `b` calls `a`, impl provides neither → runtime stack overflow. Documented in the inheritance pass; not caught by the compiler.
- **No trait-def-time validation.** A type-incorrect default body errors at the first impl that inherits it, not at the trait declaration. Error-locality only — incorrect defaults still always error deterministically.

---

## Phase 1: Typechecker — Evidence Recording

Source: `src/typechecker/check_decl.rs`

### Where Clause Registration

When the typechecker processes a function signature with `where` clauses, it populates two maps on `TraitState`:

```rust
where_bound_var_names: HashMap<u32, String>        // var_id -> source name ("a")
where_bounds: HashMap<u32, HashSet<String>>         // var_id -> {"Show", "Debug"}
```

For `fun f : a -> b -> String where {a: Show, b: Debug}`, this stores two entries mapping the fresh type variable IDs for `a` and `b` to their source names and required traits.

### Constraint Solving

During `build_fun_scheme`, pending constraints from the function body are partitioned:

- **Concrete type** (`Type::Con`): The typechecker looks up the impl and records evidence with `resolved_type: Some(("Int", []))`. Sub-constraints are pushed for parameterized types (e.g., `Show for List a` pushes a `Show` constraint on `a`).

- **Type variable** (`Type::Var`): The typechecker checks if the variable is in `where_bounds` for the required trait. If so, it records evidence with `resolved_type: None` and `type_var_name: Some("a")`.

Multi-parameter traits add `trait_type_args` to the same process. If a trait
declares a supported functional dependency, such as `trait Selectable selection
row | selection -> row`, the typechecker may use the self type to improve or
pin the extra arguments before recording evidence. See
[`docs/typechecking.md`](typechecking.md#multi-parameter-traits-and-functional-dependencies)
for the solver details; dictionary passing itself only consumes the resolved
evidence.

### TraitEvidence

Each resolved constraint produces a `TraitEvidence` entry keyed by call-site `NodeId`:

```rust
struct TraitEvidence {
    node_id: NodeId,                            // which AST node triggered this
    trait_name: String,                         // "Show"
    resolved_type: Option<(String, Vec<Type>)>, // Some(("Int", [])) or None
    type_var_name: Option<String>,              // Some("a") for polymorphic
    trait_type_args: Vec<Type>,                 // extra args for multi-param traits
}
```

The `type_var_name` field is critical for disambiguation. When multiple where-clause bounds use the same trait (e.g., `where {k: Debug, v: Debug}`), `type_var_name` tells the elaborator which dictionary parameter to use. It's resolved via `resolve_where_var_name()`, which handles the subtlety that substitution may remap type variable IDs between the signature and the body — the lookup resolves each bound ID through substitution before matching.

### Operator Traits

`Num` and `Eq` use BEAM BIFs directly (e.g., `erlang:'+'`) rather than dictionary passing. `Semigroup` now lowers through regular trait dictionaries, so `<>` elaborates to a `combine` dictionary method call.

### Trait Method Effects

Effect capability is **opt-in on the trait method's effect row**, and impls are
**bounded** by it (`register_impl` rejects an impl whose body uses effects the
trait method's row does not permit):

- pure method row (`fun foo : a -> Int`): every impl method must be pure
- closed named row (`fun foo : a -> Int needs {Config}`): impl bodies may use
  only that named set
- open row (`fun foo : a -> Int needs {..e}`): impl bodies may use any effects

How a method's effects reach a caller depends on the row and on whether the
call's self type is concrete or an abstract, where-bound type variable.

**Concrete dispatch.** When the self type resolves to a `Type::Con`,
`Checker::emit_concrete_trait_impl_effects` ([infer.rs](../src/typechecker/infer.rs))
emits the *selected impl's* actual effects into the caller's row. The effects
come from `ImplInfo.method_effects: HashMap<String, Vec<String>>` (per-method
effect names, populated in `register_impl`, cloned cross-module via
`ModuleExports.trait_impls`). This holds for closed-named and open rows alike,
with per-method precision: a pure sibling of an effectful impl stays pure.

**Generic dispatch (abstract self).** A closed-named row is part of the trait
method's *type*, so its named effects already propagate through the normal
`emit_saturated_call_effects` path — a generic over such a trait already
requires `needs {Config}`. An **open** row is the interesting case: the impl's
concrete effects are *not* in the trait method's named row, so they would be
silently dropped. Instead, when an open-row method is called on an abstract
where-bound variable `a`, the constraint's effects **surface** as the
per-constraint row variable `..a` (named after the type variable) and must be
**forwarded**:

```saga
trait Foo a { fun foo : a -> Int needs {..e} }

fun count_foos : a -> Int needs {..a} where {a: Foo}   # ..a required
count_foos x = foo x
```

Omitting `needs {..a}` is an error, mirroring the open-row callback forwarding
rule (you can only handle/forward effects the signature names or opens; `..a` is
unknowable, so a generic can't handle it — it must forward). This keeps generic
signatures stable as new impls are added elsewhere (the modularity invariant:
adding an impl never changes existing code's effect row).

Mechanism ([infer.rs](../src/typechecker/infer.rs),
[check_decl.rs](../src/typechecker/check_decl.rs)):

- `emit_concrete_trait_impl_effects` detects an abstract self (`Type::Var`) for
  an open-row method (`trait_call_forwards_open_row`), pushes `..a` (the type
  var's own id, reused as a row variable) onto the function's `effect_row.tails`,
  and records it in `Checker::trait_forward_row_vars: HashMap<u32, String>`
  (var id → trait name). This map is scoped per function clause (saved/restored
  in `check_fun_clauses`).
- The forwarding requirement fires in `check_fun_clauses`, alongside the
  callback-row-var check it mirrors. For each recorded var still abstract after
  substitution and **not** present among the declared row's tails, it raises
  "forwards effects from `Foo a`; add `needs {..a}`". Driving the check off
  `trait_forward_row_vars` (rather than the body's live effect tails) is what
  makes a `with`-wrapped body still require the annotation — a `with` rebuilds
  the effect row and drops the abstract tail, but it cannot actually handle an
  unnameable open row, so the requirement must persist.
- `..a` is meaningful only while `a` is abstract. At a concrete site `a` resolves
  to a `Type::Con` and the real effects come from
  `emit_concrete_trait_impl_effects`'s named-effect path; the type-resolved tail
  is never emitted as a (garbage) effect row.

See [effect-polymorphic-traits.md](planning/effect-polymorphic-traits.md) for
the full design rationale and the three-row propagation matrix.

---

## Phase 2: Elaborator — Dictionary Synthesis

Source: `src/elaborate.rs`

### Pass 1: Collection

The elaborator scans declarations to build lookup tables:

| Map                | Key                      | Value                           | Source                      |
| ------------------ | ------------------------ | ------------------------------- | --------------------------- |
| `trait_methods`    | method name              | (trait, index)                  | `TraitDef`                  |
| `fun_dict_params`  | function name            | [(trait, type_var)]             | `FunSignature` where clause |
| `dict_names`       | (trait, type_args, type) | constructor name                | `ImplDef`                   |
| `impl_dict_params` | (trait, type_args, type) | [(constraint_trait, param_idx)] | `ImplDef` where clause      |

Dict constructor names follow the pattern `__dict_{CanonicalTrait}_{module}_{CanonicalType}` with dots mangled to underscores, e.g., `__dict_Std_Base_Show_std_int_Std_Int_Int`. Built via `typechecker::make_dict_name`.

### Pass 2: AST Transformation

**ImplDef -> DictConstructor.** Each impl becomes a function that returns a tuple of method closures. If the impl has where-clause constraints (e.g., `impl Show for List a where {a: Show}`), the constructor takes dictionary parameters:

```
# Source
impl Debug for Dict k v where {k: Debug, v: Debug} {
  debug d = "{" <> debug_entries (to_list d) <> "}"
}

# Emitted
__dict_Debug_Dict(__dict_Debug_k, __dict_Debug_v) =
  { fun d -> "{" <> debug_entries(__dict_Debug_k, __dict_Debug_v, to_list d) <> "}" }
```

**FunBinding: prepend dict params.** Functions with where clauses get dictionary parameters prepended:

```
# Source:   debug_entries xs = ...  where {k: Debug, v: Debug}
# Emitted:  debug_entries(__dict_Debug_k, __dict_Debug_v, xs) = ...
```

**App: insert dict args at call sites.** When elaborating a function call, the elaborator checks `fun_dict_params` to see if the callee expects dictionaries. If so, it inserts dict arguments before the user arguments:

```
# Source:   debug_entries (to_list d)
# Emitted:  debug_entries __dict_Debug_k __dict_Debug_v (to_list d)
```

**Trait method calls -> DictMethodAccess.** A call like `show x` is recognized as a trait method call via `trait_methods`. The elaborator resolves the dictionary and emits:

```
DictMethodAccess { dict: <resolved_dict>, method_index: 0 }
```

### Dictionary Resolution

`resolve_dict_nth(trait, node_id, occurrence)` is the core lookup:

1. **Evidence-first**: Look up `evidence_by_node[node_id]` for the nth evidence entry matching the trait.
   - If `resolved_type` is concrete -> call `dict_for_type()` to build the dict expression.
   - If `resolved_type` is None -> use `type_var_name` to build `Var("__dict_Debug_k")`.
2. **Fallback**: If no evidence exists, fall back to `current_dict_params` (keyed by trait name). This handles inferred constraints where the typechecker absorbed the constraint into the function's scheme without per-node evidence.

The `occurrence` parameter handles multiple where-clause bounds for the same trait (e.g., `where {k: Debug, v: Debug}` — occurrence 0 gets `k`'s dict, occurrence 1 gets `v`'s).

### dict_for_type: Recursive Dict Construction

For parameterized types, `dict_for_type` recursively applies sub-dictionaries:

```
# dict_for_type(Show, List String)
App(
  DictRef("__dict_Std_Base_Show_std_list_List"),       # List's Show dict constructor (takes 1 dict param)
  DictRef("__dict_Std_Base_Show_std_string_Std_String_String")  # String's Show dict (element's dict)
)

# dict_for_type(Debug, Dict String Int)
App(
  App(
    DictRef("__dict_Std_Base_Debug_std_dict_Dict"),    # Dict's Debug dict (takes 2 dict params)
    DictRef("__dict_Std_Base_Debug_std_string_Std_String_String")   # key dict
  ),
  DictRef("__dict_Std_Base_Debug_std_int_Std_Int_Int")        # value dict
)
```

The `impl_dict_params` table tells `dict_for_type` which type arguments need sub-dicts and in what order, so phantom type parameters don't generate spurious dict args.

### Tuples

Tuples are special-cased because they're variable-arity. Instead of a `DictConstructor`, the elaborator inlines a lambda that extracts and shows each element using `erlang:element/2`. No dict is constructed at runtime.

---

## Phase 3: Lowerer — Core Erlang Emission

Source: `src/codegen/lower/`

### DictConstructor

Emitted as a regular Core Erlang function. Dict parameters become function parameters; methods become a tuple body:

```erlang
'__dict_Std_Base_Show_std_list_List'/1 =
fun (___dict_Show_a) ->
    {fun (Xs) -> ... show each element using ___dict_Show_a ...}
```

Zero-param dicts (no where clause) are arity-0 functions that return a tuple directly.

### DictMethodAccess

Lowered to `erlang:element/2` on the dict tuple:

```erlang
%% show x  where dict is in scope
let <Dict> = <dict_expr> in
  let <Method> = call 'erlang':'element'(1, Dict) in
    apply Method(X)
```

Method indices are 0-based in the AST, 1-based in Core Erlang's `element/2`.

### DictRef

Resolved by the lowerer based on the resolution map:

- **Imported dict**: `call 'std_int':'__dict_Std_Base_Show_std_int_Std_Int_Int'()`
- **Local dict**: `apply '__dict_Std_Base_Show_Foo'/0()`
- **Dict parameter variable**: plain `Var` reference (e.g., `___dict_Show_a`)

---

## Naming Conventions

| Context          | Pattern                                            | Example                                    |
| ---------------- | -------------------------------------------------- | ------------------------------------------ |
| Dict constructor | `__dict_{CanonicalTrait}_{module}_{CanonicalType}` | `__dict_Std_Base_Show_std_int_Std_Int_Int` |
| Dict parameter   | `__dict_{BareTrait}_{typevar}`                     | `__dict_Debug_k`                           |
| Core Erlang var  | `___dict_{BareTrait}_{typevar}`                    | `___dict_Debug_k` (triple underscore)      |

The triple underscore in Core Erlang comes from `core_var()` prefixing names that start with lowercase.

---

## Key Invariants

1. **One dict param per (trait, type_var) pair.** `where {a: Show + Debug}` creates two params: `__dict_Show_a` and `__dict_Debug_a`.

2. **Occurrence-based disambiguation.** When a function call site needs multiple dicts for the same trait (e.g., calling `debug_entries` which needs `Debug` for both `k` and `v`), `resolve_dict_nth` uses an occurrence counter to select the right evidence entry.

3. **Evidence keyed by NodeId.** The typechecker records evidence at the specific AST node (call site) that triggered the constraint, and the elaborator looks it up by the same NodeId. If NodeIds change between typechecking and elaboration (e.g., due to AST cloning with fresh IDs), evidence lookups fail silently and fall through to the less-precise `current_dict_params` fallback.

4. **Substitution-aware var name resolution.** Type variable IDs may be remapped by unification between where-clause registration and constraint solving. `resolve_where_var_name()` resolves through substitution to find the original bound ID, ensuring `type_var_name` is correctly set on evidence.

---

## Optimization: Trait Specialization & Generic Folding

Source: `src/codegen/trait_dispatch.rs`, `src/codegen/generic_fold.rs`, `src/codegen/lower/{calls,module}.rs`

The dict-passing scheme above is the *baseline* calling convention. A codegen
optimization layer rewrites statically-known dispatch into direct calls and
fuses `Generic`-derived `Rep` walks, so hot codecs do not build, dispatch
through, and re-traverse dictionary tuples and `Rep` constructor trees at
runtime. It is purely a backend concern — the typechecker and elaborator are
untouched.

The deep, phase-by-phase working record (history, fixtures, per-phase
measurements) lives in
[planning/trait-specialization.md](planning/trait-specialization.md). This
section is the navigable reference; that doc is the archaeology.

### Three design anchors (load-bearing — every change must preserve them)

1. **Optimizer fact, not correctness fact.** Dispatch facts live in
   `OptimizationFacts` (`src/codegen/optimize.rs`), alongside `handler_analysis`.
   They are optional and fallback-safe: `Dynamic` is always a legal
   classification, and a missing fact keeps the baseline `element/2` dispatch.
   Runtime correctness may never depend on a fact being present.

2. **Specialization rewrites only the callee expression.** A trait call lowers
   (conceptually) to `apply (element(i, <dict ctor>)) (args…, _Evidence,
   _ReturnK)`. Specialization changes *only* the `element(i, <dict ctor>)`
   sub-expression into a direct function reference; all user-argument, evidence,
   and return-continuation threading in `lower_runtime_cps_apply` stays
   identical. This is how the optimization honors "trait methods carry effect
   rows": an effectful `PostgresRow` method specializes exactly like a pure
   `ToJson` one — same evidence ABI, cheaper callee.

3. **Facts say _which_ impl; lowering joins _what_ shape.** `DictDispatch`
   carries impl identity only. At lowering the consumer cross-references the
   existing `CallEffectInfo` (`src/codegen/call_effects.rs`) for the same `App`
   `NodeId` to recover the call shape. No effect logic is duplicated.

### The substrate — `DictDispatchMap`

`src/codegen/trait_dispatch.rs::analyze()` classifies every dict-method call site
(keyed by the **outer `App` `NodeId`** — the same key as `call_effects`) as:

- `KnownImpl { dict_constructor, method_index, sub_dicts }` — the dict resolves
  to a statically-known impl.
- `Dynamic` — the dict is a runtime value (an escaping where-bound dict param,
  etc.); stays on the `element/2` path.

`SAGA_DEBUG_TRAIT_DISPATCH` traces classification.

### Specialization — devirtualize known dict-method calls

Turns a `KnownImpl` site from `apply (element(i, dict))(…)` into a direct call.

- **Producer side (hoist):**
  `src/codegen/lower/module.rs::plan_dict_method_hoists` hoists *all* local
  nullary dict methods out of their tuple into top-level functions named
  `__saga_dictmethod_<dict>_<idx>`, exports them, and references them by `FunRef`
  from the dict tuple (so the dict still works dynamically).
- **Consumer side (specialize):**
  `src/codegen/lower/calls.rs::specialized_dict_method_callee` →
  `classify_dict_specialization` emits the direct callee — a local `FunRef`, or
  for an imported impl a `call 'producer':'__saga_dictmethod_…'`. A **saturation
  guard** (`trait_method_user_arity`) requires the call be fully applied first.
- **Cross-module enabler:** every function is exported in Core (privacy is a
  front-end concern), so an inlined producer body's private-helper calls can
  lower to `call 'producer':'helper'`. This is the GHC "ship the unfolding,
  specialize at the consumer" move — BEAM won't inline across modules, so we do
  it at the AST level.

### Generic folding — fuse the `Rep` walk

`src/codegen/generic_fold.rs` is a **fuel-bounded bottom-up fixpoint AST
rewriter** (`fold_program` → `FoldOutput { program, carried_resolution }`). It
runs **after `normalize_effects`, before `resolve`**, so every NodeId-keyed
analysis (resolution, `call_effects`, optimizer) recomputes over the rewritten
tree, and it is meaning-preserving (Anchor 2: the effect ABI is untouched).

- **Parameterized inline (4a / 4a-x).** β-reduces a statically-known
  *parameterized* dict-method call: the conditional impl's method lambda is
  inlined with its `where`-bound dict params substituted by the concrete
  sub-dicts, producing nested single-arm `case`s that bottom out at a
  nullary dict call. 4a-x does this **cross-module** — external impl bodies are
  inlined, freshened, and the producer's resolution remapped onto the fresh
  NodeIds (`carried_resolution`, merged after `resolve_names`).
- **Rep-cancellation fusion (encode, "Phase 5").** Inlines `to x` together with
  the codec and cancels the `Rep` constructor tree via
  `case_of_known_constructor` / `case_of_case`, so the encoder never allocates
  the `Adt/Variant/And/Labeled/Leaf` tree it would immediately destructure.
- **Decode/from fusion ("Phase 6").** The mirror for the `from`/decode direction
  (Rep-anchored — see the gates in the planning doc; do not loosen them).
- **Literal-key β-reduction (Items 1/2).** Reduces the `apply_name_style ∘
  symbol_name (Proxy n)` proxy closures to literal field-name keys and
  propagates a constant `opts` through the recursive codec.

### Two correctness findings — do not regress

1. **Capture-avoiding substitution is mandatory.** Bottom-up folding nests
   inlined bodies that all reuse the same binder name (every building-block codec
   names its payload `inner`/`x`; freshening refreshes NodeIds, not names), so
   one name is shadowed at several depths. `substitute_var` stops at any
   sub-scope that re-binds the name (`Case` arms, `Lambda`/handler params,
   `Block` `let`/`letfun`, `Do`, `ListComprehension`, `Receive` — via
   `pat_binds`). Without this, a shadowed scrutinee is rewritten and badmatches
   at runtime (the original Phase 5 blocker).
2. **`bind_subpats` preserves effect semantics.** It *substitutes* a
   `Var`/`Wildcard` parameter only when the argument `is_duplicable` (pure &
   cheap — var, literal, field access, constructor app of duplicables); a
   non-duplicable argument is let-bound (single-arm `case`) so its effects run
   exactly once. `to`'s `Rep` trees are field accesses / literals / ctor apps →
   duplicable, which is what lets fusion proceed without changing effects.

### Measuring & debugging

- `SAGA_STATS=trait-spec` — per-module summary of specialized vs fallback
  dispatch sites, one reason per fallback
  (`src/codegen/lower/trait_spec_stats.rs`). Keyed by `App` `NodeId`; reports
  what lowering actually decided.
  ```
  SAGA_STATS=trait-spec saga build 2>&1 >/dev/null | grep trait-spec
  trait-spec[EncodeDerive]: 26 known | 26 specialized | 0 fell back
  ```
  The invariant for fully-foldable `saga_json` codecs is **zero fallbacks**
  (`N | N | 0`), *not* a fixed site count (Phase 5 raises the count by inlining
  the nullary `Generic.to` and the codec walk).
- `SAGA_DEBUG_TRAIT_DISPATCH` — classification trace (the upstream view).

### Scope — and where codec perf actually lives

The fold **deforests the `Rep` tree**: a derived codec's runtime has no
`Leaf`/`Labeled`/`And` allocations — profiling confirms zero such calls in the
decode trace (the `FromJson` dict fires once per record). So this layer is a
**devirtualization + deforestation** win; do **not** re-chase the `Rep`
machinery for codec speed — it is already gone.

The remaining derived-vs-hand codec gap is **library-side**, not compiler:

- decode's ~2× is `Codec.saga`'s `parse_object_raw` **double-scanning every
  value** (slice the raw span via `skip_value`, then re-parse the slice) — a
  single-pass-builder rewrite, not a fold.
- encode's ~2× is the `object` field-list → iodata framing.
- the benchmark's large absolute numbers were dominated by **GC over a
  pathological live working set** (holding the whole dataset resident), fixed by
  spawning per phase — not by any codec change.

Unstarted, low-priority polish (see planning doc): **Phase 7** (prune dict params
made dead by specialization) and **Item 3** (inline the concrete leaf
`Int`/`String` encoders cross-module). Both tidy the emitted Core but target
costs profiling showed are not the bottleneck.
