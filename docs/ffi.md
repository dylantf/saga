# FFI

saga calls Erlang/OTP code through `@external` annotations. The compiler trusts the type signature and emits a direct foreign call — no runtime validation or marshalling.

## Syntax

```
@external("erlang", "lists", "reverse")
pub fun reverse : (xs: List a) -> List a
```

The three string arguments are: target (always `"erlang"` for now), module, function. A full type signature is required.

## Direct FFI

When the Erlang function's argument and return types already match saga's BEAM representations, no bridge is needed:

```
@external("erlang", "erlang", "length")
pub fun length : (xs: List a) -> Int

@external("erlang", "maps", "put")
pub fun put : (key: k) -> (value: v) -> (dict: Dict k v) -> Dict k v where {k: Eq}
```

This works for functions returning plain values (ints, floats, binaries, lists, maps), `{ok, V} | {error, E}` (matches `Result`), and `true | false` (matches `Bool`).

## Bridge files

When an Erlang function's return convention doesn't match saga's type representations, you write a **bridge file** — a `.erl` file that adapts between conventions.

### Example: wrapping `Maybe` returns

Erlang idiomatically returns `Value | undefined` for optional values, but saga represents `Maybe` as tagged tuples: `{just, V}` / `{nothing}`. A bridge converts between these:

```
-- Int.saga
@external("erlang", "std_int_bridge", "parse")
pub fun parse : (s: String) -> Maybe Int
```

```erlang
%% Int.bridge.erl
-module(std_int_bridge).
-export([parse/1]).

parse(S) ->
    case string:to_integer(S) of
        {N, []} -> {just, N};
        _ -> {nothing}
    end.
```

### Example: wrapping error types

```
-- File.saga
@external("erlang", "std_file_bridge", "read_file")
fun read_file : (path: String) -> Result String FileError
```

```erlang
%% File.bridge.erl
-module(std_file_bridge).
-export([read_file/1]).

read_file(Path) ->
    case file:read_file(Path) of
        {ok, Bin} -> {ok, Bin};
        {error, Reason} -> {error, map_error(Reason)}
    end.

map_error(enoent) -> {'std_file_NotFound'};
map_error(eacces) -> {'std_file_PermissionDenied'};
map_error(Other)  -> {'std_file_Other', atom_to_binary(Other)}.
```

### Discovery

- **Stdlib bridges** live in `src/stdlib/` as `<Module>.bridge.erl`. They're embedded in the compiler binary and written to the build directory automatically.
- **User bridges** are any `.erl` files in the project root (excluding `_build/` and `tests/`). They're copied to the build directory and compiled alongside generated `.core` files.

The `-module(name)` in your `.erl` file must match the module string in `@external`.

## Type representation reference

Bridge functions must return values matching these BEAM representations:

| Type                 | BEAM representation    | Example                    |
| -------------------- | ---------------------- | -------------------------- |
| `Int`                | Integer                | `42`                       |
| `Float`              | Float                  | `1.5`                      |
| `String`             | Binary                 | `<<"hello">>`              |
| `Bool`               | Atoms `true` / `false` | `true`                     |
| `Unit`               | Atom `unit`            | `unit`                     |
| `List a`             | Erlang list            | `[1, 2, 3]`                |
| `(a, b)`             | Tuple                  | `{1, <<"hi">>}`            |
| `Ok v`               | `{ok, V}`              | `{ok, <<"contents">>}`     |
| `Err e`              | `{error, E}`           | `{error, <<"not found">>}` |
| `Just v`             | `{just, V}`            | `{just, <<"hello">>}`      |
| `Nothing`            | `{nothing}`            | `{nothing}`                |
| Custom `Foo x y`     | `{module_Foo, X, Y}`   | `{shapes_Circle, 5}`       |
| Custom nullary `Foo` | `{module_Foo}`         | `{std_file_NotFound}`      |

Notes:

- `Err` maps to the atom `error`, not `err`
- `Unit` is the atom `unit`, not an empty tuple `{}`
- Custom ADT constructors are prefixed with the module name: `Circle` in module `Shapes` becomes `shapes_Circle`
- Nullary custom constructors are 1-tuples (`{std_file_NotFound}`), unlike builtins like `True`/`False` which are bare atoms

## Limitation: Erlang cannot call effectful saga closures

You can pass a saga function value across the FFI boundary, but **Erlang code can only call it if the function is pure** (no `needs` clause). The moment a saga lambda performs effects, the codegen rewrites it into CPS form, injecting two extra parameters on top of the visible ones:

1. A handler dictionary for each effect the lambda needs
2. A return continuation `_ReturnK`

So a saga value of type `Unit -> Result a needs {Postgres}` does *not* compile to an Erlang `fun/1`. It compiles to a `fun/3`:

```erlang
fun(_unit, _Handle_SagaPgo_Postgres_raw_execute, _ReturnK) -> ... end
```

If the bridge tries to call it as `Fun(unit)` you get a runtime "function called with 1 argument(s), but expects 3" error. Even if you knew the arity, Erlang has no way to synthesize the handler value or compose a meaningful continuation — those are runtime artifacts of saga's effect lowering that only saga code can produce.

### What this means in practice

- **Pure callbacks across the FFI boundary work.** `(Int -> Int)` or `(a -> b)` with no `needs` lower to ordinary Erlang funs and the bridge can call them directly. This is how `lists:sort/2` with a comparator, `maps:map/2`, etc. work in the stdlib bridges.

- **Effectful callbacks across the FFI boundary do not work.** If you find yourself wanting to write an FFI like `wrap : ((Unit -> a needs {E}) -> Erlang) -> ...` where the Erlang side calls back into the saga lambda, **you can't** — the lambda isn't an Erlang `fun/1`.

### Workaround: drive the lifecycle from saga, not the bridge

When you want a "wrap a callback in setup/teardown" shape (transactions, locks, file handles, spans, retries, etc.), invert the flow. The bridge exposes **separate primitives** for the lifecycle phases — setup and teardown — and the saga handler arm calls the user's lambda directly between them, where the saga effect machinery is in full effect.

Don't write this:

```erlang
%% Won't work — Fun is a 3-arg CPS closure, not a fun/1.
with_resource(Setup, Fun) ->
    Resource = acquire(Setup),
    try Fun(Resource)
    after release(Resource)
    end.
```

Write this instead:

```erlang
%% Two separate primitives that don't take callbacks.
acquire(Setup) -> ...
release(Handle) -> ...
```

```
@external("erlang", "my_bridge", "acquire")
fun acquire_raw : Config -> Handle

@external("erlang", "my_bridge", "release")
fun release_raw : Handle -> Unit

handler my_handler for MyEffect needs {OtherEffect} {
  with_resource config f = {
    let handle = acquire_raw config
    let result = f ()        # called from saga, effect args available
    let _ = release_raw handle
    resume result
  }
}
```

The lambda `f` is now called from inside saga, where its handler dictionary and continuation are in scope and the codegen can wire everything correctly. The bridge only manages the resource lifecycle.

**Caveat — panics:** if `f ()` panics, `release_raw` never runs and the resource leaks. Wrap with `catch_panic` if the resource is precious (database connections, file handles), or accept the leak risk and document it.
