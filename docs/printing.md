# Printing, Show, and Debug

Design document for the printing/stringification story in dylang.

---

## Current State

- `print` and `print_error` are builtins in `Std.IO`, both constrained by `Show`
- `Show` is a trait in `Std.Base`, loaded via the prelude
- Show is implemented for: Int, Float, String, Bool, Unit, List, Maybe, Result, Dict, tuples, and types that `deriving (Show)`
- String interpolation (`$"hello {x}"`) desugars to `"hello " <> show x` in the parser
- `panic` and `todo` are builtins that print to stderr and halt

## Problem

Show is doing double duty. The auto-derived/structural representations (e.g. `Just(42)`, `User { name: "Dylan", age: 30 }`) are developer-facing debug output, not user-facing display. There's no way to distinguish "I want a nice user-facing string" from "dump the structure for debugging."

---

## Design

### Two Traits

**Debug** - structural/developer representation.
- Not auto-derived. Opt in with `deriving (Debug)` or a manual `impl`.
- The compiler knows how to generate structural impls for ADTs, records, and tuples via `deriving`.
- Shows constructor names, field names, nesting: `Just(42)`, `User { name: "Dylan", age: 30 }`
- All stdlib types (Maybe, Result, List, Dict, Ordering, tuples, primitives) implement Debug.
- Used implicitly by: error messages, test failure output, panic/todo messages, stack traces, `dbg`
- Lives in prelude (`Std.Base`)

**Show** - user-facing representation.
- Auto-derived only for primitives: Int, Float, String, Bool
- NOT auto-derived for records, ADTs, tuples, Maybe, Result, Dict, etc.
- Must be manually implemented to opt in
- Used implicitly by: string interpolation (`$"hello {x}"`)
- Lives in prelude (`Std.Base`)

### Implicit Usage

| Context | Trait used | Rationale |
|---------|-----------|-----------|
| String interpolation `$"{x}"` | Show | User-facing output, should be intentional |
| `print x` / `print_error x` | Show | Same as interpolation |
| `dbg x` | Debug | Developer tool, always available |
| `panic` / `todo` messages | Debug | Developer context, structural is fine |
| Test failure output | Debug | Developer context |
| Error messages / stack traces | Debug | Developer context |

### Builtin Functions

| Function | Trait | Output | Returns | Purpose |
|----------|-------|--------|---------|---------|
| `print x` | Show | stdout | Unit | User-facing output |
| `print_error x` | Show | stderr | Unit | User-facing error output |
| `dbg x` | Debug | stderr | `x` (passthrough) | Developer inspection, like Rust's `dbg!` |

`dbg` returns its argument so it can be inserted anywhere without changing program behavior:
```
let result = dbg (compute something)
```

### String Interpolation

Desugaring stays the same mechanically, but now calls `show` which requires the Show trait:
```
$"Hello {name}" -> "Hello " <> show name <> ""
```

If `name`'s type doesn't implement Show, you get a compile error. To dump a debug representation, be explicit:
```
$"Debug: {debug x}"
```

### Deriving

```
# Derives structural Debug (and Show, if you want it)
type Color { Red | Green | Blue } deriving (Debug, Show)

# Debug only (the common case for complex types)
record User { name: String, age: Int } deriving (Debug)

# Manual Show for user-facing representation
impl Show for User {
  show u = u.name
}
```

Debug is opt-in via `deriving (Debug)` or manual impl, just like any other trait. The stdlib provides it for all built-in types. User types that want debug printing need to derive or implement it.

### Migration from Current State

1. Add Debug trait to `Std.Base`
2. Move current structural Show impls (Maybe, Result, List, Dict, tuples, records) to Debug impls
3. Keep Show impls for primitives (Int, Float, String, Bool, Unit) since their debug and display forms are identical
4. String interpolation continues to desugar to `show` (no change)
5. Add `dbg` builtin
6. Update `panic`/`todo` to use Debug internally

### Future: Effects-Based IO

The builtins (`print`, `print_error`, `dbg`) are escape hatches for convenience and debugging. Production code should use effects:

```
effect Console {
  fun write (msg: String) -> Unit
  fun write_error (msg: String) -> Unit
  fun read_line () -> String
}

effect Logger {
  fun error (msg: String) -> Unit
  fun warn (msg: String) -> Unit
  fun info (msg: String) -> Unit
  fun debug (msg: String) -> Unit
}
```

These live in `Std.Console` and `Std.Logger` respectively, imported explicitly. The builtins remain available for quick scripts and debugging regardless.
