# Cross-Module Dictionary Specialization Fixtures

These project fixtures form an optimization ladder for imported dictionary
constructors and imported generic trait dispatch. Run each level from its
project directory:

```bash
cd examples/optimization/cross-module-dict-specialization/<level>
cargo run --manifest-path ../../../../Cargo.toml --bin saga --quiet -- run --monadic-stats
```

Each table is an immutable snapshot from a clean sequential run. Add a new
table for each optimizer milestone instead of editing earlier snapshots.

## Baseline

Captured before implementing imported dictionary constructor specialization.
Level 1 is a control: cross-module static function variants already work for a
direct imported effectful function. Levels 2-5 are the dictionary shapes we want
to improve.

| Level | Project | Shape | Whole-App Entry-Reachable Stats | Output |
| --- | --- | --- | --- | --- |
| 1 | `01-imported-direct-effect` | Imported function performs directly | `Yield 1 -> 0`, `Bind 6 -> 2`, `decls 2 -> 2`, generated `0 -> 1` | `"15"` |
| 2 | `02-imported-concrete-method` | Imported concrete trait helper calls imported dict method | `Yield 1 -> 1`, `Bind 8 -> 3`, `decls 3 -> 3`, generated `0 -> 1` | `"15"` |
| 3 | `03-imported-generic-wrapper` | Imported generic wrapper receives an imported concrete dict | `Yield 1 -> 1`, `Bind 8 -> 3`, `decls 3 -> 3`, generated `0 -> 1` | `"15"` |
| 4 | `04-imported-parameterized-dict` | Imported parameterized dict uses an imported sub-dictionary | `Yield 1 -> 1`, `Bind 12 -> 4`, `decls 4 -> 4`, generated `0 -> 1` | `"16"` |
| 5 | `05-imported-handler-factory` | Imported handler factory plus imported generic dispatch | `Yield 1 -> 1`, `Bind 9 -> 4`, `decls 4 -> 4`, generated `0 -> 0` | `"15"` |

## Intended Rungs

Level 1 should already generate a caller-local cross-module static variant and
erase its direct `Options.get_options` yield.

Level 2 asks whether the imported variant can see the imported concrete
dictionary constructor method body. Before imported dictionary constructor
collection, it should fall back or retain the residual yield.

Level 3 adds the generic function ABI: the caller passes an imported dictionary
argument into an imported public generic helper.

Level 4 adds a parameterized dictionary constructor whose argument is itself an
imported dictionary value.

Level 5 composes imported handler-factory recovery with imported dictionary
specialization, mirroring the `saga_json` shape more closely.

## After Imported Dictionary Constructor Collection

Captured after adding conservative imported dictionary constructor candidates
and merging imported handler-arm analysis into the caller optimizer. Level 2 now
fully erases the imported dictionary method yield. Levels 3-5 generate optimized
caller-local variants too, but the whole-app reachability stat still sees the
imported dictionary constructor call used to build the now-unused dictionary
argument because generated variants currently preserve the original generic ABI.

| Level | Project | Whole-App Entry-Reachable Stats | Output |
| --- | --- | --- | --- |
| 1 | `01-imported-direct-effect` | `Yield 1 -> 0`, `Bind 6 -> 2`, `decls 2 -> 2`, generated `0 -> 1` | `"15"` |
| 2 | `02-imported-concrete-method` | `Yield 1 -> 0`, `Bind 8 -> 2`, `decls 3 -> 2`, generated `0 -> 1` | `"15"` |
| 3 | `03-imported-generic-wrapper` | `Yield 1 -> 1`, `Bind 8 -> 3`, `decls 3 -> 3`, generated `0 -> 1` | `"15"` |
| 4 | `04-imported-parameterized-dict` | `Yield 1 -> 1`, `Bind 12 -> 4`, `decls 4 -> 4`, generated `0 -> 1` | `"16"` |
| 5 | `05-imported-handler-factory` | `Yield 1 -> 1`, `Bind 9 -> 3`, `decls 4 -> 3`, generated `0 -> 1` | `"15"` |

The next likely optimization rung is dictionary-argument pruning for generated
variants whose specialized bodies no longer read the dictionary parameter.
