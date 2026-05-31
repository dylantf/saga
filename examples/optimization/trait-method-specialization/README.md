# Trait Method Specialization Fixtures

These examples form an optimization ladder for specializing effectful trait
method calls under known handlers. Run each file with:

```bash
cargo run --bin saga --quiet -- run --monadic-stats examples/optimization/trait-method-specialization/<file>.saga
```

Each table is an immutable snapshot from a clean sequential run. Add a new
table for each optimizer milestone instead of editing earlier snapshots.

## Baseline

Captured before implementing trait-method specialization.

| Level | File | Shape | Module Stats | Entry-Reachable Stats | Output |
| --- | --- | --- | --- | --- | --- |
| 1 | `01-direct-effect.saga` | Direct perform under static handler | `Yield 1 -> 1`, `Bind 6 -> 2`, `decls 5 -> 5` | `Yield 1 -> 0`, `Bind 6 -> 1`, `decls 2 -> 1` | `"15"` |
| 2 | `02-concrete-trait-method.saga` | Concrete dict constructor + trait method call | `Yield 1 -> 1`, `Bind 8 -> 3`, `decls 6 -> 6` | `Yield 0 -> 0`, `Bind 7 -> 2`, `decls 2 -> 2` | `"15"` |
| 3 | `03-generic-wrapper.saga` | Generic wrapper with `where {a: Encodable}` | `Yield 1 -> 1`, `Bind 8 -> 3`, `decls 6 -> 6` | `Yield 0 -> 0`, `Bind 7 -> 2`, `decls 2 -> 2` | `"15"` |
| 4 | `04-parameterized-dict.saga` | Parameterized impl using a sub-dictionary | `Yield 1 -> 1`, `Bind 12 -> 4`, `decls 8 -> 8` | `Yield 0 -> 0`, `Bind 9 -> 2`, `decls 2 -> 2` | `"16"` |
| 5 | `05-let-bound-handler-factory.saga` | Let-bound handler factory + generic dispatch | `Yield 1 -> 1`, `Bind 9 -> 3`, `decls 6 -> 6` | `Yield 0 -> 0`, `Bind 8 -> 2`, `decls 3 -> 2` | `"15"` |

## After Level 2: Nullary Dictionary Method Specialization

Captured after adding the first conservative pass: local nullary dict
constructors can expose a selected method lambda inside an already-known handler
stack.

| Level | File | Module Stats | Entry-Reachable Stats | Output |
| --- | --- | --- | --- | --- |
| 1 | `01-direct-effect.saga` | `Yield 1 -> 1`, `Bind 6 -> 2`, `decls 5 -> 5` | `Yield 1 -> 0`, `Bind 6 -> 1`, `decls 2 -> 1` | `"15"` |
| 2 | `02-concrete-trait-method.saga` | `Yield 1 -> 1`, `Bind 8 -> 3`, `decls 6 -> 6`, generated `0 -> 1` | `Yield 0 -> 0`, `Bind 7 -> 2`, `decls 2 -> 2`, generated `0 -> 1` | `"15"` |
| 3 | `03-generic-wrapper.saga` | `Yield 1 -> 1`, `Bind 8 -> 3`, `decls 6 -> 6`, generated `0 -> 1` | `Yield 0 -> 0`, `Bind 7 -> 2`, `decls 2 -> 2`, generated `0 -> 1` | `"15"` |
| 4 | `04-parameterized-dict.saga` | `Yield 1 -> 1`, `Bind 12 -> 4`, `decls 8 -> 8`, generated `0 -> 1` | `Yield 0 -> 0`, `Bind 9 -> 2`, `decls 2 -> 2`, generated `0 -> 1` | `"16"` |
| 5 | `05-let-bound-handler-factory.saga` | `Yield 1 -> 1`, `Bind 9 -> 3`, `decls 6 -> 6` | `Yield 0 -> 0`, `Bind 8 -> 2`, `decls 3 -> 2` | `"15"` |

## After Level 3: Known Dictionary Argument Specialization

Captured after specializing generated static variants with known nullary
dictionary arguments. If a call site binds `let d = __dict_T()` and then calls a
generic function with `d`, the generated variant receives a dictionary-keyed
name and substitutes the known dictionary tuple into the cloned body. This lets
the level 3 generic wrapper erase the method dispatch inside the variant.

| Level | File | Module Stats | Entry-Reachable Stats | Output |
| --- | --- | --- | --- | --- |
| 1 | `01-direct-effect.saga` | `Yield 1 -> 1`, `Bind 6 -> 2`, `decls 5 -> 5` | `Yield 1 -> 0`, `Bind 6 -> 1`, `decls 2 -> 1` | `"15"` |
| 2 | `02-concrete-trait-method.saga` | `Yield 1 -> 1`, `Bind 8 -> 3`, `decls 6 -> 6`, generated `0 -> 1` | `Yield 0 -> 0`, `Bind 7 -> 2`, `decls 2 -> 2`, generated `0 -> 1` | `"15"` |
| 3 | `03-generic-wrapper.saga` | `Yield 1 -> 1`, `Bind 8 -> 3`, `decls 6 -> 6`, generated `0 -> 1` | `Yield 0 -> 0`, `Bind 7 -> 2`, `decls 2 -> 2`, generated `0 -> 1` | `"15"` |
| 4 | `04-parameterized-dict.saga` | `Yield 1 -> 1`, `Bind 12 -> 4`, `decls 8 -> 8`, generated `0 -> 1` | `Yield 0 -> 0`, `Bind 9 -> 2`, `decls 2 -> 2`, generated `0 -> 1` | `"16"` |
| 5 | `05-let-bound-handler-factory.saga` | `Yield 1 -> 1`, `Bind 9 -> 3`, `decls 6 -> 6`, generated `0 -> 1` | `Yield 0 -> 0`, `Bind 8 -> 2`, `decls 3 -> 2`, generated `0 -> 1` | `"15"` |

## After Level 4: Parameterized Dictionary Specialization

Captured after recognizing parameterized dictionary constructors when every
dictionary argument is already known. The optimizer can now materialize
`__dict_Encodable_Box(__dict_Encodable_Int)` as a concrete dictionary tuple,
substitute the inner dictionary into the outer method lambda, and continue
through the nested `DictMethodAccess`.

| Level | File | Module Stats | Entry-Reachable Stats | Output |
| --- | --- | --- | --- | --- |
| 1 | `01-direct-effect.saga` | `Yield 1 -> 1`, `Bind 6 -> 2`, `decls 5 -> 5`, generated `0 -> 0` | `Yield 1 -> 0`, `Bind 6 -> 1`, `decls 2 -> 1`, generated `0 -> 0` | `"15"` |
| 2 | `02-concrete-trait-method.saga` | `Yield 1 -> 1`, `Bind 8 -> 3`, `decls 6 -> 6`, generated `0 -> 1` | `Yield 0 -> 0`, `Bind 7 -> 2`, `decls 2 -> 2`, generated `0 -> 1` | `"15"` |
| 3 | `03-generic-wrapper.saga` | `Yield 1 -> 1`, `Bind 8 -> 3`, `decls 6 -> 6`, generated `0 -> 1` | `Yield 0 -> 0`, `Bind 7 -> 2`, `decls 2 -> 2`, generated `0 -> 1` | `"15"` |
| 4 | `04-parameterized-dict.saga` | `Yield 1 -> 1`, `Bind 12 -> 4`, `decls 8 -> 8`, generated `0 -> 1` | `Yield 0 -> 0`, `Bind 9 -> 2`, `decls 2 -> 2`, generated `0 -> 1` | `"16"` |
| 5 | `05-let-bound-handler-factory.saga` | `Yield 1 -> 1`, `Bind 9 -> 3`, `decls 6 -> 6`, generated `0 -> 1` | `Yield 0 -> 0`, `Bind 8 -> 2`, `decls 3 -> 2`, generated `0 -> 1` | `"15"` |

## Reading The Snapshots

Level 1 proves the existing direct-call optimizer works for an ordinary static
handler: the entry-reachable `Options.get_options` yield is erased.

Levels 2-5 initially keep one module-level residual yield. In
`monadic-opt`, that yield lives inside a generated `dict-ctor` method lambda:

```text
dict-ctor __dict_Encodable_Std_Int_Int ()
  method[0]:
    Pure(Lambda([x], bind[value] __anf_v0 <- Yield(Options/get_options@1, ...)))
```

The call site then constructs a dictionary, extracts the method with
`DictMethodAccess`, and applies the method value.

The first specialization pass recognizes nullary dict constructors at local
call sites, remembers the selected method lambda, and inlines that method only
inside an already-known handler stack when the inlined method exposes an
existing direct-call opportunity. This generates static variants for levels
2-4. For example, level 2's generated `compute` variant becomes:

```text
fun __saga_static_variant__compute... (x) =
  BinOp(+, Var(x), Lit(10))
```

The module-level residual yield remains because the original dictionary
constructor still exists in the optimized program. The hot generated variant is
yield-free.

The level 3 pass extends this to dictionary parameters of generated variants.
Level 3's generated `serialize` variant still keeps the original dictionary
argument in its ABI, but the body no longer reads it:

```text
fun __saga_static_variant__serialize...__dict_<hash> (__dict_Encodable_a, x) =
  BinOp(+, Var(x), Lit(10))
```

The level 4 pass extends dictionary-value recovery to parameterized dictionary
constructors whose arguments are already known dictionaries. Level 4's generated
`serialize` variant now removes both the outer `Box` method dispatch and the
inner `Int` method dispatch from the hot body.

Level 5 still moves because handler-factory recovery already turns the let-bound
factory result into the same static-handler shape before dictionary argument
specialization runs.

The `entry-reachable` numbers currently report `Yield 0 -> 0` for levels 2-5.
That is a stats reachability limitation: the reachability walker sees the
top-level functions reached from `main`, but it does not yet model
`DictMethodAccess` as reaching the selected dictionary constructor method body.
Use `monadic-opt` inspection of the generated variant as the ground truth for
this fixture set until stats learn that edge.

The next unspecialized rung is imported or otherwise unknown dictionary values:
the current pass only follows parameterized constructors when every constructor
argument is a dictionary binding already visible in the current optimizer scope.
