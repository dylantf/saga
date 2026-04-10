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
