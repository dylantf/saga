# Val Bindings

## Summary

Add `val` declarations for named, module-level pure values.

## Motivation

Currently, defining a simple named constant requires a `Unit ->` function:

```
fun pi : Unit -> Float
pi () = 3.14159

fun max_retries : Unit -> Int
max_retries () = 5
```

This is ceremonial — `pi` isn't a computation, it's a value. AI agents and new users frequently try to write zero-argument functions, which don't exist in the language. `val` provides the right tool for this.

Beyond scalars, there's no way to define module-level data structures without wrapping them in a function:

```
fun allowed_origins : Unit -> List String
allowed_origins () = ["localhost", "example.com", "app.io"]

fun error_codes : Unit -> Dict Int String
error_codes () = Dict.from_list [(404, "Not Found"), (500, "Server Error")]
```

`val` eliminates the boilerplate for both cases.

## Design

### Syntax

```
# Private val
val pi = 3.14159
val max_retries = 5

# Public val
pub val version = "1.0.0"
pub val default_port = 8080
```

### Allowed expressions

The RHS must be **pure** (no effects, no `!`) and must **not produce a function type**. Beyond that, any expression is valid:

```
# Literals
val pi = 3.14159
val app_name = "dylang"

# Arithmetic and string operations on other vals
val tau = 2.0 * pi
val greeting = "hello" <> " " <> "world"

# Data structures
val allowed_origins = ["localhost", "example.com", "app.io"]
val error_codes = Dict.from_list [(404, "Not Found"), (500, "Server Error")]
val default_config = Config { port: 8080, debug: False, name: "app" }

# Pure function calls
val keyword_set = Set.from_list ["if", "then", "else", "case", "let"]
```

Explicitly **not** allowed:

```
# Effect operations (not pure)
val contents = read_file! "config.toml"

# Function types (use `fun` for functions)
val add = fun a b -> a + b
val inc = add 1
```

The function type restriction prevents two ways of defining functions. If the inferred type of the RHS is `a -> b`, it's an error — use `fun` instead.

### Type inference

The type is inferred from the expression. No annotation syntax — `pub val` does not require a type signature. The value is self-documenting.

### References between vals

Vals can reference other vals. The compiler topologically sorts val declarations and rejects cycles:

```
val pi = 3.14159
val tau = 2.0 * pi       # ok, pi is defined above (order in source doesn't matter)

val a = b                 # error: circular reference
val b = a
```

### Compilation

Vals compile to zero-arity Erlang functions. At use sites, a `val` reference emits a zero-arity function call. This is an implementation detail — vals are not functions in dylang's type system.

```
# dylang
val pi = 3.14159
val tau = 2.0 * pi

# Compiles to (roughly):
# 'pi'/0 = fun () -> 3.14159
# 'tau'/0 = fun () -> call 'erlang':'+' (2.0, apply 'pi'/0 ())
```

The BEAM JIT optimizes zero-arity functions returning simple expressions effectively, so there is negligible overhead compared to true inlining.

For cases where inlining is desired (e.g. hot paths with scalar constants), the `@inline` annotation can be used:

```
@inline
val pi = 3.14159

@inline
val max_retries = 5

@inline
val app_name = "dylang"
```

When `@inline` is present, the typechecker verifies the RHS is a compile-time inlineable value:
- Scalar literals: `Int`, `Float`, `String`, `Bool`
- Tuples/lists of inlineable values: `(1, 2)`, `[1, 2, 3]`
- References to other `@inline` vals

If the check passes, the value is substituted at every use site during lowering — no zero-arity function is emitted. If the RHS isn't inlineable (e.g. a function call, record constructor, `Dict.from_list`), the typechecker reports an error.

```
@inline
val pi = 3.14159              # ok, scalar literal

@inline
val tau = 2.0 * pi            # error: arithmetic not inlineable (yet)

@inline
val origins = ["a", "b"]      # ok, list of literals

@inline
val codes = Dict.from_list [] # error: function call not inlineable
```

### Module exports

`pub val` values are visible to importing modules. Since they compile to zero-arity functions, importing modules call into the defining module at runtime.

### Interaction with existing features

- `val` is **not** a function — it cannot be called with arguments, it has no arity, and it does not participate in the CPS effect transform
- `val` cannot appear inside function bodies (use `let` for local bindings)
- `val` names cannot be used as patterns (they're not constructors)
- `val` does not go through the normal function lowering path — it's a separate, simplified codegen path that emits a zero-arity Core Erlang function directly
- The "all functions take at least one argument" rule is unchanged — `val` is a different kind of declaration, not a zero-argument function

## Implementation

### AST

- New `Decl::Val` variant: `{ name, value: Expr, public: bool }`
- Parse `[pub] val <name> = <expr>` at the declaration level
- `val` becomes a reserved keyword

### Typechecker

- Infer the type of the RHS expression
- Verify the expression is pure (empty effect set)
- Verify the inferred type is not a function type (`a -> b`)
- Register the val in the type environment so other declarations can reference it

### Codegen

- Emit a zero-arity Core Erlang function for each `val`
- At use sites, emit a zero-arity function call
- Does not go through the standard function lowering path (no parameter handling, no CPS, no effect threading)

### Estimated scope

Small-to-medium. A new AST variant, validation in the typechecker, and a dedicated emit path in lowering. No changes to the effect system, trait system, or CPS transform.

## Future extensions

- **Const folding for `@inline`**: Evaluate arithmetic and string concat on `@inline` vals at compile time (e.g. `@inline val tau = 2.0 * pi`)
- **Record literals in `@inline`**: Allow record constructors with inlineable fields
