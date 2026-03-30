The Problem
The resolver builds a flat module-level scope: HashMap<String, ScopedName> and then walks the entire AST with that same unchanging scope. It has zero awareness of lexical bindings — function params, let bindings, lambda params, case pattern bindings. Any name that exists in the module scope "wins" over a local binding, because the resolver doesn't know local bindings exist.

There's also a secondary bug where @external functions from all imported modules are dumped into the bare scope unconditionally (lines 348-356).

How Real Compilers Do This
Real compilers (Rust's resolve, Elm's canonicalize, OCaml's typechecker) all maintain a scope stack — when you enter a binding context (function body, lambda, let, case arm), you push a frame of locally-bound names. When looking up a name, you check locals first. If found locally, it shadows everything from outer scopes.

Two reasonable places to do this:

During typechecking (OCaml style) — piggyback on the typechecker's existing save/restore env
Standalone resolve pass (Rust style) — the resolver itself maintains the scope stack
Option 2 is the right fit because:

The resolver runs after elaboration, which creates new AST nodes (DictRef, DictConstructor, ForeignCall) that need resolution
It keeps the typechecker focused on types, not codegen concerns
It's a self-contained change to one file
The Design
What stays the same
The module-level scope construction in resolve_names (steps 1-3: register local funs, register imports, register trait dicts) stays exactly as-is. This correctly builds the set of module-level and imported names.

What changes

1. New Scope struct replaces the two bare HashMap parameters:

struct Scope<'a> {
module: &'a HashMap<String, ScopedName>, // module-level names
qualified: &'a HashMap<String, ScopedName>, // qualified names (unchanged)
locals: Vec<HashSet<String>>, // stack of local binding frames
}
With methods:

push_frame(names: HashSet<String>) / pop_frame()
is_local(name: &str) -> bool — walks the stack top-down
resolve(name: &str) -> Option<&ScopedName> — returns None if local, otherwise checks module 2. collect_pat_vars helper extracts all bound variable names from a pattern tree:

Pat::Var { name } → {name}
Pat::Constructor { args } → union of recursive calls on args
Pat::Tuple { elements } → union
Pat::Record { fields, as_name } → field aliases + as_name
Pat::Wildcard / Pat::Lit → empty
etc. 3. Every binding site pushes a frame:

AST node Locals to push
FunBinding { params, body } collect_pat_vars on each param
Lambda { params, body } collect_pat_vars on each param
Block with Let { pattern, .. } collect_pat_vars(pattern) — visible to subsequent stmts
Block with LetFun { name, params, body } name visible to subsequent stmts; params visible in body
Case arm { pattern, guard, body } collect_pat_vars(pattern) for guard + body
Do { bindings } each (pat, expr) binding's pat vars visible to subsequent bindings + success
ListComprehension generator/let pat vars accumulate through qualifiers + body
Receive arm collect_pat_vars(pattern) for guard + body
Inline Handler arm param names for body
HandlerDef arm param names for body
ImplDef / DictConstructor method method params for body 4. The Var handler becomes:

ExprKind::Var { name, .. } => {
if !scope.is_local(name) {
if let Some(scoped) = scope.module.get(name) {
map.insert(expr.id, scoped_to_resolved(scoped));
}
}
// Local binding or unknown name → not in map → lowerer emits CExpr::Var
} 5. Delete the external function leak (current lines 348-356). These externals already enter scope correctly through the normal export/expose path when they're public. The per-module CompiledModule.resolution maps (merged in by emit_module_with_context) handle resolution within handler bodies from other modules.

What doesn't change
ResolvedName enum — no new variants needed
The lowerer — "not in map = local variable" convention stays
The typechecker — completely untouched
Constructor atom resolution — unrelated
Why this is correct
The convention "not in resolution map = local variable" already works in the lowerer. We just need to stop incorrectly putting local variables into the map.
The scope stack is cheap — for typical programs, 3-5 frames deep, each frame a small HashSet.
Every binding form is handled exhaustively — if we miss one, the worst case is a local that gets incorrectly resolved to a module-level name (the current bug), not a crash.
