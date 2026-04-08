# Trait Dictionary Passing

Traits are compiled via **dictionary passing**: each trait becomes a tuple of method closures, and `where` clauses become extra function parameters that receive these tuples at runtime.

```
# Source
trait Show a { fun show : a -> String }
impl Show for Int { show n = int_to_string n }
fun print_it : a -> String where {a: Show}
print_it x = show x

# After elaboration (conceptual)
__dict_Std_Base_Show_Int = { fun n -> int_to_string n }
print_it __dict_Show_a x = element(1, __dict_Show_a)(x)
```

Three compiler phases cooperate: the **typechecker** records evidence about which trait constraints apply at each call site, the **elaborator** transforms the AST to thread dictionary arguments, and the **lowerer** emits Core Erlang tuple operations.

---

## Phase 1: Typechecker — Evidence Recording

Source: `src/typechecker/check_decl.rs`

### Where Clause Registration

When the typechecker processes a function signature with `where` clauses, it populates two maps on `TraitState`:

```rust
where_bound_var_names: HashMap<u32, String>        // var_id -> source name ("a")
where_bounds: HashMap<u32, HashSet<String>>         // var_id -> {"Show", "Debug"}
```

For `fun f : a -> b -> String where {a: Show, b: Debug}`, this stores two entries mapping the fresh type variable IDs for `a` and `b` to their source names and required traits.

### Constraint Solving

During `build_fun_scheme`, pending constraints from the function body are partitioned:

- **Concrete type** (`Type::Con`): The typechecker looks up the impl and records evidence with `resolved_type: Some(("Int", []))`. Sub-constraints are pushed for parameterized types (e.g., `Show for List a` pushes a `Show` constraint on `a`).

- **Type variable** (`Type::Var`): The typechecker checks if the variable is in `where_bounds` for the required trait. If so, it records evidence with `resolved_type: None` and `type_var_name: Some("a")`.

### TraitEvidence

Each resolved constraint produces a `TraitEvidence` entry keyed by call-site `NodeId`:

```rust
struct TraitEvidence {
    node_id: NodeId,                            // which AST node triggered this
    trait_name: String,                         // "Show"
    resolved_type: Option<(String, Vec<Type>)>, // Some(("Int", [])) or None
    type_var_name: Option<String>,              // Some("a") for polymorphic
    trait_type_args: Vec<Type>,                 // extra args for multi-param traits
}
```

The `type_var_name` field is critical for disambiguation. When multiple where-clause bounds use the same trait (e.g., `where {k: Debug, v: Debug}`), `type_var_name` tells the elaborator which dictionary parameter to use. It's resolved via `resolve_where_var_name()`, which handles the subtlety that substitution may remap type variable IDs between the signature and the body — the lookup resolves each bound ID through substitution before matching.

### Operator Traits

`Num`, `Semigroup`, and `Eq` use BEAM BIFs directly (e.g., `erlang:'+'`) rather than dictionary passing. They never produce dictionary parameters or evidence for the elaborator.

---

## Phase 2: Elaborator — Dictionary Synthesis

Source: `src/elaborate.rs`

### Pass 1: Collection

The elaborator scans declarations to build lookup tables:

| Map                | Key                      | Value                           | Source                      |
| ------------------ | ------------------------ | ------------------------------- | --------------------------- |
| `trait_methods`    | method name              | (trait, index)                  | `TraitDef`                  |
| `fun_dict_params`  | function name            | [(trait, type_var)]             | `FunSignature` where clause |
| `dict_names`       | (trait, type_args, type) | constructor name                | `ImplDef`                   |
| `impl_dict_params` | (trait, type_args, type) | [(constraint_trait, param_idx)] | `ImplDef` where clause      |

Dict constructor names follow the pattern `__dict_{CanonicalTrait}_{module}_{CanonicalType}` with dots mangled to underscores, e.g., `__dict_Std_Base_Show_std_int_Std_Int_Int`. Built via `typechecker::make_dict_name`.

### Pass 2: AST Transformation

**ImplDef -> DictConstructor.** Each impl becomes a function that returns a tuple of method closures. If the impl has where-clause constraints (e.g., `impl Show for List a where {a: Show}`), the constructor takes dictionary parameters:

```
# Source
impl Debug for Dict k v where {k: Debug, v: Debug} {
  debug d = "{" <> debug_entries (to_list d) <> "}"
}

# Emitted
__dict_Debug_Dict(__dict_Debug_k, __dict_Debug_v) =
  { fun d -> "{" <> debug_entries(__dict_Debug_k, __dict_Debug_v, to_list d) <> "}" }
```

**FunBinding: prepend dict params.** Functions with where clauses get dictionary parameters prepended:

```
# Source:   debug_entries xs = ...  where {k: Debug, v: Debug}
# Emitted:  debug_entries(__dict_Debug_k, __dict_Debug_v, xs) = ...
```

**App: insert dict args at call sites.** When elaborating a function call, the elaborator checks `fun_dict_params` to see if the callee expects dictionaries. If so, it inserts dict arguments before the user arguments:

```
# Source:   debug_entries (to_list d)
# Emitted:  debug_entries __dict_Debug_k __dict_Debug_v (to_list d)
```

**Trait method calls -> DictMethodAccess.** A call like `show x` is recognized as a trait method call via `trait_methods`. The elaborator resolves the dictionary and emits:

```
DictMethodAccess { dict: <resolved_dict>, method_index: 0 }
```

### Dictionary Resolution

`resolve_dict_nth(trait, node_id, occurrence)` is the core lookup:

1. **Evidence-first**: Look up `evidence_by_node[node_id]` for the nth evidence entry matching the trait.
   - If `resolved_type` is concrete -> call `dict_for_type()` to build the dict expression.
   - If `resolved_type` is None -> use `type_var_name` to build `Var("__dict_Debug_k")`.
2. **Fallback**: If no evidence exists, fall back to `current_dict_params` (keyed by trait name). This handles inferred constraints where the typechecker absorbed the constraint into the function's scheme without per-node evidence.

The `occurrence` parameter handles multiple where-clause bounds for the same trait (e.g., `where {k: Debug, v: Debug}` — occurrence 0 gets `k`'s dict, occurrence 1 gets `v`'s).

### dict_for_type: Recursive Dict Construction

For parameterized types, `dict_for_type` recursively applies sub-dictionaries:

```
# dict_for_type(Show, List String)
App(
  DictRef("__dict_Std_Base_Show_std_list_List"),       # List's Show dict constructor (takes 1 dict param)
  DictRef("__dict_Std_Base_Show_std_string_Std_String_String")  # String's Show dict (element's dict)
)

# dict_for_type(Debug, Dict String Int)
App(
  App(
    DictRef("__dict_Std_Base_Debug_std_dict_Dict"),    # Dict's Debug dict (takes 2 dict params)
    DictRef("__dict_Std_Base_Debug_std_string_Std_String_String")   # key dict
  ),
  DictRef("__dict_Std_Base_Debug_std_int_Std_Int_Int")        # value dict
)
```

The `impl_dict_params` table tells `dict_for_type` which type arguments need sub-dicts and in what order, so phantom type parameters don't generate spurious dict args.

### Tuples

Tuples are special-cased because they're variable-arity. Instead of a `DictConstructor`, the elaborator inlines a lambda that extracts and shows each element using `erlang:element/2`. No dict is constructed at runtime.

---

## Phase 3: Lowerer — Core Erlang Emission

Source: `src/codegen/lower/`

### DictConstructor

Emitted as a regular Core Erlang function. Dict parameters become function parameters; methods become a tuple body:

```erlang
'__dict_Std_Base_Show_std_list_List'/1 =
fun (___dict_Show_a) ->
    {fun (Xs) -> ... show each element using ___dict_Show_a ...}
```

Zero-param dicts (no where clause) are arity-0 functions that return a tuple directly.

### DictMethodAccess

Lowered to `erlang:element/2` on the dict tuple:

```erlang
%% show x  where dict is in scope
let <Dict> = <dict_expr> in
  let <Method> = call 'erlang':'element'(1, Dict) in
    apply Method(X)
```

Method indices are 0-based in the AST, 1-based in Core Erlang's `element/2`.

### DictRef

Resolved by the lowerer based on the resolution map:

- **Imported dict**: `call 'std_int':'__dict_Std_Base_Show_std_int_Std_Int_Int'()`
- **Local dict**: `apply '__dict_Std_Base_Show_Foo'/0()`
- **Dict parameter variable**: plain `Var` reference (e.g., `___dict_Show_a`)

---

## Naming Conventions

| Context          | Pattern                                        | Example                                          |
| ---------------- | ---------------------------------------------- | ------------------------------------------------ |
| Dict constructor | `__dict_{CanonicalTrait}_{module}_{CanonicalType}` | `__dict_Std_Base_Show_std_int_Std_Int_Int`   |
| Dict parameter   | `__dict_{BareTrait}_{typevar}`                 | `__dict_Debug_k`                                 |
| Core Erlang var  | `___dict_{BareTrait}_{typevar}`                | `___dict_Debug_k` (triple underscore)             |

The triple underscore in Core Erlang comes from `core_var()` prefixing names that start with lowercase.

---

## Key Invariants

1. **One dict param per (trait, type_var) pair.** `where {a: Show + Debug}` creates two params: `__dict_Show_a` and `__dict_Debug_a`.

2. **Occurrence-based disambiguation.** When a function call site needs multiple dicts for the same trait (e.g., calling `debug_entries` which needs `Debug` for both `k` and `v`), `resolve_dict_nth` uses an occurrence counter to select the right evidence entry.

3. **Evidence keyed by NodeId.** The typechecker records evidence at the specific AST node (call site) that triggered the constraint, and the elaborator looks it up by the same NodeId. If NodeIds change between typechecking and elaboration (e.g., due to AST cloning with fresh IDs), evidence lookups fail silently and fall through to the less-precise `current_dict_params` fallback.

4. **Substitution-aware var name resolution.** Type variable IDs may be remapped by unification between where-clause registration and constraint solving. `resolve_where_var_name()` resolves through substitution to find the original bound ID, ensuring `type_var_name` is correctly set on evidence.
