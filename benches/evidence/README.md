# Evidence representation benchmarks

Three single-file programs that isolate the cost of the runtime evidence
frame, written before changing its representation from a positional tuple of
`{Tag, Ops}` to a map `#{Tag => Ops}` (see "Stage B implementation notes" in
`docs/planning/sound-function-representation.md`).

## Running

```bash
cargo build --release
target/release/saga run benches/evidence/closed_row_hot_op.saga
```

Each program prints one line with a result that depends on the whole
computation. The iteration count is the `iterations` function at the top of
each file. The wall time of `saga run` includes compiling the program and
starting the VM.

To read the emitted code for a hot path:

```bash
target/release/saga emit benches/evidence/closed_row_hot_op.saga
```

The quotes below were taken from that output on commit `0d35fea3`.

## closed_row_hot_op.saga

Isolates the positional lookup of an operation in a closed row: three
`element` loads today, against one map get after the change. This is the gate.

`loop` is a self-recursive named function declared `needs {Counter, Log,
Trace}`, ten million iterations, one `tick!` each. The `Counter` handler comes
from a handler factory that captures a run-time value, and is installed in
`main` and not in `loop`, so no static fast path applies. `Counter` sorts
first, so it is slot 1 of a three-entry frame.

The operation in `'loop'/4` is emitted as:

```erlang
apply call 'erlang':'element'
(1, call 'erlang':'element'
  (2, call 'erlang':'element'
    (1, _Evidence)))(_Cor20, fun (___eff0) ->
```

and the continuation ends in a self call that passes the frame unchanged:

```erlang
apply 'loop'/4(_Cor10, _Cor13, _Cor18, _Cor19)    %% _Cor18 = _Evidence
```

There is no bridge call in the loop and no direct call to a handler function.

## open_row_hot_op.saga

The same workload and the same result, with the operation performed by a
lambda passed to `repeat : Int -> Int -> (f: Int -> Int needs {..e}) -> Int
needs {..e}`. Isolates the lookup by tag in a closure body.

The lambda is emitted in `'run'/3` as:

```erlang
{'$saga_cps', fun (I, _Evidence, _ReturnK) ->
  apply call 'erlang':'element'
  (1, call 'std_evidence_bridge':'find_evidence'
    (_Evidence, '_script.Counter'))(_Cor36, _ReturnK)}
```

One bridge call (a linear search by tag) and one `element` per operation.
`'repeat'/5` calls the callback through the tagged closure match
(`<{'$saga_cps', _Cor22}> when is_function(_Cor22, 3) -> apply _Cor22(...)`)
and passes `_Evidence` unchanged, both to the callback and to its own
recursive call, so the lookup is the only evidence work in the loop.

## deep_call_chain.saga

Isolates reframing at calls. No operation is performed in the hot path; the
five operations run once after the last iteration. Two million iterations of
`drive`, each calling a chain of six named functions whose rows alternate
between closed rows narrower than the caller's and open rows.

| Call | Callee row | Emitted evidence argument |
|------|------------|---------------------------|
| `drive` -> `level1` | closed, 4 of 5 | `select_evidence(_Evidence, [1,2,3,5])` |
| `level1` -> `level2` | open, prefix of 3 | `reframe_evidence(_Evidence, {4, [1,2,3,4]}, [1,2,4])` |
| `level2` -> `level3` | closed, 3 | `select_evidence(_Evidence, [1,2,3])` |
| `level3` -> `level4` | open, prefix of 1 | `reframe_evidence(_Evidence, {3, [1,2,3]}, [1])` |
| `level4` -> `level5` | closed, 1 | `select_evidence(_Evidence, [1])` |
| `level5` -> `level6` | open, no prefix | `_Evidence`, unchanged |
| `drive` -> `drive` | same row | `_Evidence`, unchanged |

For example, in `'level1'/3`:

```erlang
let <_Cor34> =
  call 'std_evidence_bridge':'reframe_evidence'
  (_Evidence, {4, [1|[2|[3|[4|[]]]]]}, [1|[2|[4|[]]]])
in
...
apply 'level2'/3(_Cor31, _Cor34, _Cor35)
```

So five of the seven calls per iteration go through a bridge call that builds
a new tuple: three `select_evidence` and two `reframe_evidence`. The call from
a closed row to an open row with an empty prefix does not reframe.

The compiler warns that `level1`, `level3` and `level5` declare effects they
never use. That is intended: the declared rows are what force the reframing.
