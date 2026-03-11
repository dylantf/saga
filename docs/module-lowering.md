# Module Lowering

Notes on compiling the module system in the backend (lowerer + Core Erlang).

---

## What already exists

The evaluator and typechecker already have a fully working module system:

- **Dependency-ordered loading** with cycle detection (`tc_loading` /
  `loader.loading` sets).
- **Module caching** (`tc_loaded`: module name to `Vec<(String, Scheme)>`,
  `tc_type_ctors`: module name to type-constructor map).
- **Pub/export filtering** (`public_names`, `public_names_for_tc`).
- **Prelude injection** (Std modules skip prelude to avoid circular deps,
  user modules get it automatically).
- **Constructor hoisting** via `__ctor_type_` mapping for uppercase names
  in exposing lists.
- **Qualified name resolution** (`"Module.name"` keys in env/type env).

The backend does not need to re-implement any of this. It follows the same
pattern as trait evidence: the typechecker records what is needed (module
exports as `Scheme` types), and the lowerer derives the concrete codegen
details (arity, effect params, module atoms) from that data.

---

## Module name mapping

`Foo.Bar.Baz` becomes the Erlang module atom `'foo_bar_baz'`. Flat lowercase
with underscores, same convention as Elixir. Avoids tooling issues with dots in
quoted atoms.

---

## Cross-module symbol table

The lowerer currently builds `top_level_funs`, `effect_defs`, `handler_defs`,
etc. from a single module's declarations. For cross-module calls it needs the
same information about imported functions: arity (including effect-expanded
arity), effect sets, handler params.

### Where does this data come from?

The typechecker's `tc_loaded` cache already stores `Vec<(String, Scheme)>` per
module. The lowerer derives arity and effect sets by inspecting each `Scheme`'s
inner `Type` (counting arrow params, extracting `needs` effects). This is the
same approach used for trait dispatch: the typechecker collects evidence, the
lowerer fills in the concrete details.

The lowerer already has `collect_type_effects` in utils which does similar
work. No changes to the typechecker are needed.

### How it flows

1. Typechecker processes modules in dependency order, populating `tc_loaded`.
2. `tc_loaded` (or a view of it) is passed to the lowerer.
3. Before lowering module A, the lowerer walks A's imports and, for each
   imported module, derives codegen info from the cached `Scheme` types:
   function arities, effect sets, record field orders, effect/handler defs.
4. This populates the existing lookup tables (`top_level_funs`, `fun_effects`,
   `effect_defs`, etc.) alongside the local declarations.

---

## Exports

Filter declarations by `pub`. Only `pub` functions appear in the `CModule`
export list (name/arity pairs). Non-pub functions are emitted as definitions
but not exported, making them module-private in Erlang.

---

## Qualified calls

For pure functions, a qualified call like `Math.abs x` lowers to:

```erlang
call 'math':'abs'(X)
```

using the existing `CExpr::Call(module, func, args)` IR node. Currently
`QualifiedName` just emits `CExpr::Var(name)` -- needs to emit `Call` instead.

For effectful functions, handler params and the return continuation must be
threaded across the module boundary. If module B exports `fetchData` which
`needs {Http}`, then a call from module A becomes:

```erlang
call 'b':'fetchData'(Arg1, _HandleHttp, _ReturnK)
```

The lowerer knows to do this because the imported `Scheme` for `fetchData`
contains the `Http` effect in its type.

---

## Tag/constructor atom qualification

Record constructor tag atoms and ADT constructor atoms must be prefixed with
the module name to avoid collisions. `Point` defined in module `Geo` becomes
`'geo_point'` as a tag atom. Same for ADT constructors: `Circle` in `Shapes`
becomes `'shapes_circle'`.

---

## Entry point

`Main.main` is the boot function. The main module's `main` function must be
exported as `main/0` (or with the appropriate effect-expanded arity) so the
Erlang runtime can call it.

---

## Multi-file emission

One `.core` file per module. Each is compiled independently with `erlc`.
The driver processes modules in dependency order (same order as typechecking),
so by the time module A is compiled, all its dependencies are already `.beam`
files.

---

## Implementation order

1. Module name mapping utility
2. Export filtering (pub only) in `CModule` emission
3. Derive codegen info from `tc_loaded` Schemes (populate lowerer tables)
4. Qualified calls for pure functions (`QualifiedName` -> `CExpr::Call`)
5. Tag/constructor atom qualification
6. Qualified calls for effectful functions (handler threading)
7. Multi-file emission (one `.core` per module, driver loop)
8. Entry point (`Main.main` as boot function)
