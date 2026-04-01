# Compiler Pipeline

## Overview

```
Source (.dy)
  -> Lexer (src/lexer.rs)
  -> Parser (src/parser/)
  -> AST (src/ast.rs)
  -> Derive Expansion (src/derive.rs)
  -> Desugar (src/desugar.rs)
  -> Typecheck (src/typechecker/)
     includes: Name Resolution (src/typechecker/resolve.rs)
  -> Elaborate (src/elaborate.rs)
  -> Normalize (src/codegen/normalize.rs)
  -> Codegen Resolve (src/codegen/resolve.rs)
  -> Lower (src/codegen/lower/)
  -> Core Erlang AST (src/codegen/cerl.rs)
  -> Print -> .core file
  -> erlc -> .beam file
  -> erl (run)
```

## Phases

### Parse
Hand-written Pratt parser. Produces `Vec<Decl>` (the `Program` type). Each AST node gets a unique `NodeId` assigned at creation time.

### Derive Expansion
Generates trait impl declarations from `deriving` clauses (e.g. `deriving (Show, Debug, Eq)`).

### Desugar
Transforms sugar nodes into core AST forms: pipes, composition, list literals, string interpolation, cons, etc. Does NOT desugar `do/else` (that's handled in lowering).

### Typecheck
HM-style inference with traits, effects, and exhaustiveness checking. Multi-module: scans all `.dy` files to build a module map, resolves imports by declared module name.

Includes a **name resolution** sub-pass (`src/typechecker/resolve.rs`) that runs after imports are processed and before inference. It rewrites bare names in the AST to canonical (module-qualified) form using the `ScopeMap` built from imports. For example, `Var { name: "map" }` becomes `Var { name: "Std.List.map" }`. The pass is scope-aware: local bindings shadow imports. See `docs/name-resolution.md` for full details.

Key outputs:
- `CheckResult`: type environment, trait evidence, scope_map, diagnostics
- `ModuleCodegenInfo` per module: exports, constructors, external functions, trait impl dicts, effect definitions, handler definitions
- Prelude import declarations (stored in `CheckResult.prelude_imports`)

### Elaborate
Transforms trait method calls into explicit dictionary passing. Runs per-module. Takes the parsed program + `CheckResult`, produces a new program with:
- `DictConstructor` declarations replacing `ImplDef`
- `DictRef` and `DictMethodAccess` expressions replacing trait method calls
- `ForeignCall` expressions for `@external` functions
- Dictionary parameters added to functions with `where` clauses

### Normalize
Effect normalization pre-pass. Adjusts the AST for CPS transformation in the lowerer.

### Codegen Resolve (src/codegen/resolve.rs)
Pre-computes two lookup tables consumed by the lowerer:

**ConstructorAtoms** (`HashMap<String, String>`): Maps constructor names to their mangled Erlang atoms. Handles BEAM convention overrides (Ok->ok, Err->error, Nothing->undefined, True->true, etc.), module-prefixed mangling (NotFound -> std_file_NotFound), and qualified forms (Std.File.NotFound -> std_file_NotFound).

**ResolutionMap** (`HashMap<NodeId, ResolvedName>`): Maps each `Var`, `QualifiedName`, and `DictRef` AST node to its resolved target:
- `LocalFun { name, arity, effects }` - top-level function in the current module
- `ImportedFun { erlang_mod, name, arity, effects }` - function from another module
- `ExternalFun { erlang_mod, erlang_func, arity }` - `@external` FFI function
- Not in map = local variable (function param, let binding, lambda param)

Each resolved name carries its effect requirements so the lowerer can determine CPS threading without a separate lookup.

Resolution is per-Var-node. Whether a name appears bare (`to_list`) or as a call head (`to_list t`), the same NodeId gets the same resolution. The lowerer reads the head Var's resolution to decide between `call` (cross-module) and `apply` (local).

**Per-module resolution maps**: Each module gets its own `ResolutionMap` computed when it's compiled, stored in `CompiledModule.resolution`. When lowering a user module, all imported modules' pre-computed maps are merged in. This means handler bodies, impl methods, and dict constructors from Std modules have their names already resolved against their source module's scope, with no re-resolution needed.

### Lower (src/codegen/lower/)
Converts the elaborated AST into a Core Erlang AST (`CModule`). This is the most complex phase:

- **CPS transformation** for algebraic effects: effectful functions get handler parameters and return continuations added
- **Handler inlining**: `expr with handler_name` inlines the handler's arms as CPS callbacks
- **Saturated vs partial application detection**: compares arg count against resolved arity
- **Effect threading**: passes handler params through call chains automatically

The lowerer consumes:
- `CodegenContext.modules` (all `CompiledModule` bundles)
- `constructor_atoms` from the resolver (constructor name -> Erlang atom)
- `resolved` (merged resolution map) from the resolver (NodeId -> call target)
- `fun_info` (arity, effects, param absorbed effects) built during `init_module`

**Name resolution vs CPS are cleanly separated:**
- The `ResolutionMap` (from `resolve.rs`) answers "what does this name refer to?" for every `Var`, `QualifiedName`, and `DictRef` node. It carries the target module, function name, arity, and effects. The lowerer reads it via `self.resolved.get(&node_id)`.
- `FunInfo` (from `init_module`) tracks CPS metadata for local functions: expanded arity (including handler params), effect requirements, and per-parameter absorbed effects. This is NOT name resolution -- it's about how to thread handler parameters and return continuations.
- `module_aliases` maps source-level module names to Erlang atom names (e.g. "List" -> "std_list"). Used as a fallback in `lower_qualified_call` for unresolved qualified names.
- `effect_defs`, `handler_defs`, `op_to_effect` handle dynamic effect dispatch (which handler params are in scope depends on the `with` block, not static resolution).

What the lowerer does NOT do:
- Name resolution. All name -> module mapping is done by the resolver.
- Constructor mangling. All constructor -> atom mapping is done by the resolver.

### Emit
Pretty-prints the Core Erlang AST to a `.core` file. Then `erlc` compiles it to `.beam`, and `erl` runs it.

## Data Flow: CompiledModule

All per-module compilation results are bundled into `CompiledModule`:

```rust
struct CompiledModule {
    codegen_info: ModuleCodegenInfo,  // from typechecker
    elaborated: Program,              // from elaborator
    resolution: ResolutionMap,        // from resolver
}
```

`CodegenContext` carries `modules: HashMap<String, CompiledModule>` plus `prelude_imports` and `let_effect_bindings`. This is the single source of truth for all cross-module information during lowering.

## Build Orchestration (src/cli/build.rs)

### Single file (`dylang run file.dy`)
1. Parse + typecheck (loads prelude, scans Std modules)
2. `compile_std_modules`: for each Std module, elaborate + normalize + resolve -> `CompiledModule`
3. Elaborate user code
4. `emit_module_with_context`: resolve user code, merge all module resolutions, lower, print
5. `erlc` all `.core` files, `erl` to run

### Project (`dylang build`)
Same as single file but also processes user-defined modules and a `Main` module. User modules get elaborated but don't currently get pre-computed resolution maps (they're resolved inline during `emit_module_with_context`).

### Test (`dylang test`)
Builds the project first, then for each test file: typecheck, elaborate, emit. Reuses the project's compiled modules to avoid recompilation.
