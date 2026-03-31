# CLI Improvements

Improvements to compiler output, error presentation, and overall CLI UX
for the alpha release.

---

## Stack traces

Runtime errors currently show Erlang-internal names (`'_script':main/0`)
with no connection to the user's source code. We need to embed source
location metadata at compile time so errors can point back to dylang code.

- During lowering, attach source location info (file, line, function name)
  to error-producing expressions. Gleam does this by throwing maps with
  metadata: `#{gleam_error => panic, file => "...", line => 123, ...}`.
  We could do similar for `panic`, `assert_eq`, and effect-related crashes.
- Capture BEAM stack traces at runtime (`Class:Reason:StackTrace` in the
  catch block) and translate Erlang MFA tuples into dylang function names.
- Filter out internal frames (erl_eval, init, runtime wrapper, CPS
  continuation scaffolding) so the trace shows only user-relevant calls.
- Display format should show function name + file:line, e.g.:
  ```
  Stack trace:
    main        src/App.dy:14
    helper      src/Lib.dy:8
  ```

---

## BEAM crash translation

The most impactful single change. When a runtime error occurs on the BEAM,
`exec_erl` currently dumps raw Erlang term format:

```
error: badarith
[{erlang,'div',[1,0],[{error_info,#{module => erl_erts_errors}}]},
 {'_script',main,0,[]},
 ...]
```

Instead, parse the Erlang error tuples and print readable messages:

```
Runtime error: arithmetic error (division by zero)
  in main()
```

Cover the common crash reasons: `badarith`, `badmatch`, `function_clause`,
`case_clause`, `badarg`, `if_clause`. Anything unrecognized can fall back
to printing the raw reason, but with a header like `Runtime error (BEAM):`
so it's at least framed as a dylang error.

---

## Build progress output

Currently: silence during compilation, then `Built 21 module(s)`. Add
per-module progress so the user knows something is happening:

```
Compiling Std.List...
Compiling Std.Result...
Compiling MathLib...
Compiling Main...
Built 22 module(s) in _build/dev (0.34s)
```

Include total build time in the summary line.

---

## Suppress or rewrite erlc warnings

`erlc` writes warnings directly to stderr that leak into the user's
terminal, e.g.:

```
no_file: Warning: evaluation of operator 'div'/2 will fail with a 'badarith' exception
```

Capture `erlc` stderr and either:

- Suppress warnings that are redundant with our own diagnostics
- Rewrite useful ones into dylang-style format with file:line:col
- Drop `no_file:` prefix at minimum

---

## Color in build output

Tests already use ANSI colors (green checkmarks, yellow skips). Build
output should match:

- Green for success (`Built 22 module(s)`)
- Red for errors
- Yellow for warnings
- Dim/gray for progress lines (`Compiling Std.List...`)

Keep color off when stderr is not a TTY (piped output, CI).

---

## Richer `check` output

`dylang check` currently prints just `OK`. Show what was checked:

```
Checked 4 module(s), no errors
```

Or with warnings:

```
Checked 4 module(s), 1 warning

Warning at src/Lib.dy:11:1: unused function: `helper`
  11 | helper x = x + 1
     | ^^^^^^
```

---

## Build timing

Add timing to `build` and `run` commands. Show total wall time:

```
Built 22 module(s) in _build/dev (0.34s)
```

Useful for noticing regressions and gives the user a sense of whether
the build is fast or something is wrong.

---

## Test timing

Add per-test and total suite timing to `dylang test`:

```
MathLib
  add
    ✓ adds two positive numbers (1ms)
    ✓ adds negative numbers (0ms)

5 passed, 0 failed, 1 skipped (12ms)
```

Already noted in the main roadmap as a TODO.
