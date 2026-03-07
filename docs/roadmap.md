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
- [ ] Effect row polymorphism / effect variables (`needs e`) -- deferred, larger change

## Type Checker (HM)

- [x] Let / function / lambda inference
- [x] If/else, case/match, records, ADTs, lists, cons, pipe, concat, blocks
- [x] Effects: EffectDef, EffectCall, HandlerDef, With, Resume, return clauses
- [x] `needs` effect set tracking (direct calls, propagation, `with` subtraction, HOF absorption)
- [x] `Type::EffArrow` for annotated callback parameters

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
- [ ] `Semigroup` / `Monoid` in stdlib

## Type System (Future)

- [ ] Exhaustiveness checking for case expressions
- [ ] Higher-kinded types (`* -> *`, enables `Functor`, `Applicative`)
- [ ] `Functor` / `Applicative` traits in stdlib

## Module System

- [x] `module Foo` declarations
- [x] `import Foo`, `import Foo as F`, `import Foo (a, b)`
- [x] Qualified names (`Math.abs`)
- [x] `pub` exports
- [x] Cycle detection
- [x] `project.toml` root marker, `Main.dy` entry point
- [x] Typechecker: per-module checker, shared cache, qualified name injection

## Backend

- [ ] BEAM / Core Erlang codegen
- [ ] JavaScript codegen (after BEAM is solid)
- [ ] FFI (`foreign erlang "mod" "fun" as f in Effect`)

## Out of Scope

- Multishot continuations (single-shot is sufficient for practical effects)
- Effect inference (explicit `needs` annotations required)
- Effect tunneling (unhandled effects are errors)
