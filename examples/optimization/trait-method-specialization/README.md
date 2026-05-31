# Trait Method Specialization Fixtures

These examples form an optimization ladder for specializing effectful trait
method calls under known handlers. Run each file with:

```bash
cargo run --bin saga --quiet -- run --monadic-stats examples/optimization/trait-method-specialization/<file>.saga
```

Baseline stats were captured before implementing trait-method specialization.

| Level | File | Shape | Module Stats | Entry-Reachable Stats | Output |
| --- | --- | --- | --- | --- | --- |
| 1 | `01-direct-effect.saga` | Direct perform under static handler | `Yield 1 -> 1`, `Bind 6 -> 2`, `decls 5 -> 5` | `Yield 1 -> 0`, `Bind 6 -> 1`, `decls 2 -> 1` | `"15"` |
| 2 | `02-concrete-trait-method.saga` | Concrete dict constructor + trait method call | `Yield 1 -> 1`, `Bind 8 -> 3`, `decls 6 -> 6` | `Yield 0 -> 0`, `Bind 7 -> 2`, `decls 2 -> 2` | `"15"` |
| 3 | `03-generic-wrapper.saga` | Generic wrapper with `where {a: Encodable}` | `Yield 1 -> 1`, `Bind 8 -> 3`, `decls 6 -> 6` | `Yield 0 -> 0`, `Bind 7 -> 2`, `decls 2 -> 2` | `"15"` |
| 4 | `04-parameterized-dict.saga` | Parameterized impl using a sub-dictionary | `Yield 1 -> 1`, `Bind 12 -> 4`, `decls 8 -> 8` | `Yield 0 -> 0`, `Bind 9 -> 2`, `decls 2 -> 2` | `"16"` |
| 5 | `05-let-bound-handler-factory.saga` | Let-bound handler factory + generic dispatch | `Yield 1 -> 1`, `Bind 9 -> 3`, `decls 6 -> 6` | `Yield 0 -> 0`, `Bind 8 -> 2`, `decls 3 -> 2` | `"15"` |

## Reading The Baseline

Level 1 proves the existing direct-call optimizer works for an ordinary static
handler: the entry-reachable `Options.get_options` yield is erased.

Levels 2-5 intentionally keep one module-level residual yield. In
`monadic-opt`, that yield lives inside a generated `dict-ctor` method lambda:

```text
dict-ctor __dict_Encodable_Std_Int_Int ()
  method[0]:
    Pure(Lambda([x], bind[value] __anf_v0 <- Yield(Options/get_options@1, ...)))
```

The call site then constructs a dictionary, extracts the method with
`DictMethodAccess`, and applies the method value. The current optimizer does not
inline through that dictionary/method indirection, so the handler stack is not
visible at the effectful method body.

The `entry-reachable` numbers currently report `Yield 0 -> 0` for levels 2-5.
That is a stats reachability limitation: the reachability walker sees the
top-level functions reached from `main`, but it does not yet model
`DictMethodAccess` as reaching the selected dictionary constructor method body.
Use the module-level residual yield as the baseline signal for this fixture set
until stats learn that edge.
