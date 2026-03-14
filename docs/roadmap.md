# Roadmap

Checkbox = implemented and working. Unchecked = not yet done.

---

## Interpreter / Core Language

- [x] Let bindings, functions (curried), lambdas
- [x] If/else, blocks
- [x] Case / pattern matching (with guards)
- [x] Records, field access
- [x] Custom types / ADTs
- [x] List literals, `::` cons operator
- [x] Tuples (any arity, pattern matching, type annotations)
- [x] `|>` pipe, `<>` concat
- [x] Mutual recursion
- [x] Constructor call syntax `Circle(5)`
- [x] Let destructuring (`let (x, y) = ...`, `let Point { x } = ...`, `let h :: t = ...`)
- [x] String interpolation (`$"hello {name}"`)
- [x] `panic` and `todo` builtins (halt immediately, return `Never`)

## Effects / Handlers

- [x] Effect declarations (`effect Log { ... }`)
- [x] Effect calls (`log! "msg"`)
- [x] Inline handlers (`expr with { log msg -> ... }`)
- [x] Named handlers (`handler console_log for Log { ... }`)
- [x] Handler stacking (`expr with { h1, h2, op args -> body }`)
- [x] `resume` (deep handlers, single-shot)
- [x] `return value ->` clause in handlers
- [x] Abort without resume (structured exceptions)
- [x] `needs` on functions (`fun f () -> T needs {Log, Http}`)
- [x] `needs` on handlers (`handler stripe for Billing needs {Log} { ... }`)
- [x] `needs` on impl blocks (different impls may use different effects)

## Type Checker (HM)

- [x] Let / function / lambda inference
- [x] If/else, case/match, records, ADTs, lists, cons, pipe, concat, blocks
- [x] Effects: EffectDef, EffectCall, HandlerDef, With, Resume, return clauses
- [x] `needs` effect set tracking (direct calls, propagation, `with` subtraction, HOF absorption)
- [x] `Type::EffArrow` for annotated callback parameters
- [x] Disallow effect invocations in guard expressions
- [x] Prelude substitution leak: module checkers started at `next_var: 0`, causing var ID
      collisions with the parent checker. Imported scheme types resolved through the parent's
      substitution, creating phantom dependencies that blocked generalization of polymorphic
      functions like `run_state`. Fixed by starting module checkers at the parent's `next_var`.

## Traits / Impls

- [x] Trait definitions and impl blocks
- [x] Impl checking (method count, names, body types)
- [x] Where clause enforcement (`where {a: Show + Eq}`)
- [x] Supertrait enforcement
- [x] Constraint propagation through scheme instantiation
- [x] Runtime dispatch (`__impl_Trait_Type_method` mangled keys)
- [x] Built-in traits: `Show`, `Num`, `Eq`, `Ord`
- [x] Conditional impls (`impl Show for List a where {a: Show}`)
- [x] `needs` on impl blocks (parsing + type checking)
- [ ] `deriving` syntax to auto-generate trait impls from ADT structure (e.g. `type Color { Red | Green } deriving {Show, Eq}`)

## Type System

- [x] Exhaustiveness checking for case expressions
  - [x] Top-level constructor coverage (missing constructors = error)
  - [x] Wildcard / variable patterns short-circuit as total
  - [x] Bool literal patterns recognized as True/False constructors
  - [x] Guarded arms conservatively treated as non-covering
  - [x] Do...else exhaustiveness (bail constructors across all bindings)
  - [x] Nested pattern exhaustiveness (Maranget's usefulness algorithm)
  - [x] Redundant / unreachable arm detection
- [x] `do...else` block -- sequential pattern bindings with explicit success expression (each `Pat <- expr` extracts on match or short-circuits to else; last line without `<-` is the success return value; else arms must unify with success type)

## Module System

- [x] `module Foo` declarations
- [x] `import Foo`, `import Foo as F`, `import Foo (a, b)`
- [x] Qualified names (`Math.abs`)
- [x] `pub` exports
- [x] Cycle detection
- [x] `project.toml` root marker, `Main.dy` entry point
- [x] Typechecker: per-module checker, shared cache, qualified name injection

## Pre-Backend Polish

- [x] `not` operator (boolean negation)
- [x] Negative number literals in patterns (`case x { -1 -> ... }`)
- [x] Dict type
- [x] String-splitting desugaring for pattern matching on strings, e.g. "foo" <> rest
- [x] Split prelude into stdlib modules (`List`, `Maybe`, `Result`)
- [x] Number literal separators
- [x] Multiline strings (`"""..."""`, `$"""..."""`)
- [x] Raw strings (`@"..."`, `@"""..."""`)
- [ ] Regular expressions
- [x] List comprehensions
- [x] Function composition
- [x] Conversion builtins (`Int.parse`, `Int.to_float`, `Float.parse`, `Float.trunc`, `Float.round`, `Float.floor`, `Float.ceil`)
- [ ] String operations (`string_length`, `string_split`, `string_chars`, etc.)
- [ ] More list functions (`zip`, `range`, `take`, `drop`, `any`, `all`)

## Syntax

## Backend

### Infrastructure

- [x] Core Erlang IR (`CExpr`, `CPat`, `CLit`, `CModule`) + pretty-printer
- [x] Lowering pass (dylang AST -> CErl IR)
- [x] `erlc` invocation, `_build/` output directory
- [x] `dylang build <file>` command

### Expression lowering

- [x] Literals (int, float, bool, string, unit)
- [x] Variables
- [x] Binary operators (arithmetic, comparison, concat)
- [x] Short-circuit `&&` / `||`
- [x] `if/else`
- [x] Blocks and `let` bindings
- [x] Lambdas
- [x] `case` / pattern matching (constructors, tuples, literals, wildcards)
- [x] Tuples
- [x] List literals and cons (`[1, 2, 3]`, `h :: t`)
- [x] ADT constructor expressions (`Some(x)`, `Circle(r)`)
- [x] Records (create, field access, update)
- [x] String interpolation (`$"..."`) -- desugared to `<>` chains by parser
- [x] `do...else` blocks

### Guards

- [x] Simple guards (comparisons, arithmetic) emitted directly as Core Erlang `when` clauses
- [x] Complex guards (user-defined function calls) desugared into arm body conditionals with fallthrough

### Function calls

- [x] Calling other top-level functions in the same module (saturated apply)
- [x] Multi-argument functions (direct `apply 'name'/N`, no currying overhead)
- [x] Multi-clause functions (`fib 0 = 0`, `fib 1 = 1`, `fib n = ...` -> single `case` body)
- [x] Mutual recursion (top-level; `letrec` for local fns deferred)
- [x] Tail call guarantee (recursive apply emitted in tail position; BEAM handles TCO natively)

### Module system

- [x] Multi-module builds (resolve imports, compile dependency order)
- [x] Qualified calls (`Math.abs x` -> `call 'math':'abs'(X)`)
- [x] Exposed imports (`import Math (add)` -> `call 'math':'add'(...)`)
- [x] `pub` export filtering (only pub functions exported in module mode)
- [x] Cross-module effectful calls (handler params + `_ReturnK` threaded across module boundaries)
- [x] Constructor atom mangling (prefix with module name to avoid cross-module collisions)
- [x] Cross-module trait impl injection (importing a module imports its pub trait impls)
- [x] Module-qualified dict names (`__dict_Show_Graphics_Color` not `__dict_Show_Color`)
- [x] Entry point validation (`main` cannot have `needs`, effects handled via `with`)
- [ ] Opaque types (constructors visible inside defining module, hidden to importers)

### Data structures

- [x] Dict lowering (`Dict.empty` -> `maps:new()`, `Dict.*` -> `maps:*` BIFs, `Eq` via `=:=`)
- [x] List lowering (`List.*` -> `lists:*`/`erlang:*` BIFs, `foldl` arg-swap wrapper)

### Traits

- [x] Dictionary passing (trait impls as tuples of funs, passed as extra args; elaboration pass)
- [x] Built-in trait dispatch (`Show` via dict constructors; `Eq`/`Ord`/`Num` use direct BEAM BIFs)
- [x] Replace `show`/`print` builtin special-cases with proper `Show` trait dispatch
- [x] Fix `show`/`print` as higher-order values (`show` is `DictMethodAccess`, `print` is a synthesized dict-parameterized function)

### Codegen bugs

- [x] Integer division: `/` on `Int` emits `erlang:'/'` (float division) instead of `erlang:'div'`
- [x] Polymorphic type class dicts used as bare function refs without applying dict arguments (e.g. `'__dict_Show_Result'/2` not called with sub-dicts)

### Effects (CPS transform)

- [x] CPS plumbing (effect/handler metadata in lowerer, handler params on effectful functions)
- [x] Effect calls in blocks (`log! "msg"` -> `apply Handler('log', "msg", K)`)
- [x] Resumable handlers (`resume value` -> `apply _K(value)`)
- [x] Non-resumable handlers (don't call `_K`, handler return value is result)
- [x] Return clauses (`return value -> Ok value`)
- [x] Named handlers (`handler silent for Log { ... }`)
- [x] Inline handlers (`expr with { op args -> body }`)
- [x] Handler stacking (multiple effects, one handler param per effect)
- [x] Effect propagation (threading handler params through calls to effectful functions)
- [x] Multishot continuations (calling `_K` multiple times; free on BEAM)
- [x] Elaborator: Show dict insertion inside handler arm bodies (`print` in handler crashes)
- [x] Handler `needs` clause (handler that itself uses effects)
- [x] Effect calls in non-block positions (nested in `if` conditions, binary ops, etc.)
- [x] HOF effect absorption (passing effectful closures through higher-order functions like `try`)
- [x] Return clause bypass on handler abort (return clause wraps abort results incorrectly)

### Stdlib / prelude

- [x] Wire prelude functions to BEAM equivalents (`List`, `Maybe`, `Result`)
- [x] FFI (`@external` declarations for Erlang module calls)
- [x] Compile Std.\* modules to BEAM (script mode auto-compiles stdlib into `_build/`)
- [x] Prelude imports flow into lowerer (script mode resolves `List` -> `std_list`)
- [x] Deduplicate prelude impls (Show dicts, `print` currently emitted into every module; should live in one place)

## Runtime Optimization

- [ ] Expand `is_guard_safe` to allow Erlang guard BIFs (`is_integer`, `is_atom`, `is_list`, etc.) so they stay in `when` and enter the decision tree
- [ ] Verify tail call optimization works end-to-end (emit a deep-recursive test, confirm no stack overflow on BEAM)
- [ ] Benchmark trait dictionary passing overhead vs. Erlang direct dispatch
- [ ] Profile generated Core Erlang for unnecessary intermediate `let` bindings (peephole cleanup pass)

## Upcoming

- [x] Generic effects (`effect State s { fun get () -> s; fun put (val: s) -> Unit }`)
  - Parser: type params on effect declarations, `EffectRef` with type_args in needs/handler clauses
  - Type checker: shared type vars across operations, fresh instantiation on lookup, handler specialization
  - Handlers: `handler counter for State Int { ... }` binds the type param
  - Enables prelude-provided `State s`, `MVector` backed by BEAM arrays
- [ ] Local function definitions (`let f x = ...` inside a block, with recursion + closure capture)

## Maybe

- Higher-kinded types (`* -> *`, enables `Functor`, `Applicative`)
- `Functor` / `Applicative` traits in stdlib
- `Semigroup` / `Monoid` in stdlib
- Effect row polymorphism / effect variables (`needs e`)
- `Dynamic` type for consuming untyped Erlang data (JSON parsers, ETS, message passing)
- Cache cloning in typecheck_import: At check_module.rs:204-209, six HashMap caches are .clone()d into every module checker. For deep import trees this is a lot of allocation. The caches are read-heavy and append-only during module checking. Using Rc<RefCell<...>> or passing references would avoid the cloning, but this makes the borrow checker harder to work with. Can be revisited if performance becomes a concern (and after profiling to see if the cloning is the issue).

## Out of Scope

- Effect inference (explicit `needs` annotations required)
- Effect tunneling (unhandled effects are errors)
