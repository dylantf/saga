# Badarity Repro: Test Assertion Inside Effectful Callback

Run from this directory:

```sh
saga test
```

Observed on June 27, 2026:

```text
MiniEffectReproTest
  minimal effect repro
    ✗ asserts inside a handler selected through an effectful choose
      PANIC: function called with 1 argument(s), but expects 3
```

The repro has no Edda imports. It uses a tiny `TryNext` effect and a
`choose_string` function that handles `skip`. The selected route callback calls
`Std.Test.assert_eq True True`; that assertion is enough to trigger the runtime
badarity panic.
