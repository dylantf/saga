# Test Runner Refactor: Project-Module Based Suite Execution

## Summary
- Replace script-per-file test execution with one generated project entry module that imports the selected test modules and calls `Std.Test.run_modules`.
- Make test files normal Saga modules: each test file must declare `module ...` and export `pub fun tests : Unit -> Unit needs {Register}`.
- Remove parser/desugar/compiler special cases for top-level `test`/`describe`; registration becomes a shallow `Register` effect used only to collect test metadata and thunks.
- Execute the collected suite in one BEAM VM, fail-fast within a test, continue across tests, catch panics per test, print live results, print a per-module summary, and print one overall summary.

## Public Interface Changes
- Align assertions around public `Std.Test.Test`; custom assertion helpers must use `needs {Test}` instead of `needs {Assert}`.
- Add public `Std.Test.Register` for test module `tests` functions.
- Keep `test`, `describe`, `skip`, and `only` as ordinary `Std.Test` functions taking strings + lambdas; no parser sugar remains.
- Add public `Std.Test.run_modules : List (String, Unit -> Unit needs {Register}) -> Unit` for the generated entry module.

Test authoring becomes:

```saga
module FooTest
import Std.Test (Register, describe, test, assert_eq)

pub fun tests : Unit -> Unit needs {Register}
tests () = {
  describe "foo" (fun () -> {
    test "bar" (fun () -> {
      assert_eq 1 1
    })
  })
}
```

## Implementation Changes
- `Std.Test`
  - Introduce `Register` as the collection effect and keep `Test` as the assertion effect.
  - Collect each module into a deterministic flat entry stream preserving `GroupStart` / `GroupEnd` / `TestCase` order.
  - Make `run_modules` do three phases: collect all selected modules, apply one global `only` normalization pass across the full suite, then execute modules in order.
  - Implement global `only` by marking non-`only` tests as skipped rather than removing them, so output and summaries retain full module/group structure.
  - Wrap each test body in `catch_panic`; a panic becomes a failed test, not a suite crash.
  - Keep fail-fast assertion handling within a single test; continue across tests and modules.
  - Print per-test live results, then a per-module summary immediately after each module, then one final summary; exit nonzero iff any test failed.
- CLI/build pipeline
  - Add/finish `build_project_ext(profile, extra_source_dirs, custom_main)` and use it for `saga test`.
  - Discover test files from configured `tests_dir`, keep existing file/path filtering, preserve sorted file order, resolve those files to module names, and generate a synthetic entry module importing only the selected modules.
  - Treat missing `module` declarations in selected test files as a hard `saga test` error, not a silent skip.
  - Compile tests as project modules, not scripts; add the test source dir to the module map and feed the generated entry module in as `Main`.
  - Keep execution to a single VM boot and one compile pipeline run for the suite.
- Compiler/editor cleanup
  - Remove parser `test_mode`, top-level test-expression AST support, test desugaring, synthesized per-file `main`, and LSP heuristics that detect test mode from `import Std.Test`.
  - Keep test syntax entirely library-level.
  - Fix the current false-positive unused-effects warning so callback-absorbed `Register` usage in `Std.Test` helpers does not warn after the refactor.
- Migration/docs
  - Convert existing test suites and examples to explicit `module ...` + `pub fun tests`.
  - Update `docs/testing.md` and `docs/language-design.md` to describe normal-module test authoring and remove the old special-syntax/desugaring narrative.

## Test Plan
- Suite execution
  - `saga test` compiles once, boots one VM, and runs all selected test modules in stable file order.
  - `saga test <filter>` keeps the current file/path-based selection behavior and only imports those modules into the synthetic entrypoint.
- Registration/execution behavior
  - Nested `describe` groups preserve ordering and indentation.
  - First failed assertion aborts only that test body.
  - A panicking test is reported as failed and does not crash the suite.
  - Per-module summaries and the final summary report correct pass/fail/skip counts.
- Global `only`
  - If any `only` exists anywhere in the selected suite, every non-`only` test in every module is reported as skipped.
  - Mixed modules with and without `only` still print correct module summaries.
- Migration/validation
  - Tests compile as normal modules with module-scoped imports, traits, and record/pattern behavior.
  - Missing `tests` exports or broken generated imports fail during build/typecheck with clear errors.
  - No false unused-effects warning is emitted for the new `Std.Test` helpers.

## Assumptions And Defaults
- `only` is global across the full selected suite, not per-module.
- Non-`only` tests are marked skipped, not removed, during focus mode.
- The CLI filter remains module/file selection only in this refactor; no new test-name filtering is added.
- Deterministic ordering is based on the sorted discovered test files used to build the selected module list.
- This refactor accepts the test authoring change as a breaking change: test files must be normal modules with an exported `tests` function, and custom assertion helpers must switch from `needs {Assert}` to `needs {Test}`.
