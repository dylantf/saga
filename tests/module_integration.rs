use dylang::{eval, lexer, parser};
use std::path::PathBuf;

fn fixtures_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/modules")
}

fn run(source: &str) -> eval::EvalResult {
    let loader = eval::ModuleLoader::project(fixtures_root());
    let tokens = lexer::Lexer::new(source).lex().expect("lex error");
    let program = parser::Parser::new(tokens)
        .parse_program()
        .expect("parse error");
    eval::eval_program(&program, &loader)
}

fn ok(source: &str) {
    match run(source) {
        eval::EvalResult::Ok(_) => {}
        eval::EvalResult::Error(e) => panic!("runtime error: {}", e.message),
        eval::EvalResult::Effect { name, .. } => panic!("unhandled effect: {}", name),
    }
}

fn err(source: &str) -> String {
    match run(source) {
        eval::EvalResult::Error(e) => e.message,
        eval::EvalResult::Ok(_) => panic!("expected error, got Ok"),
        eval::EvalResult::Effect { name, .. } => panic!("expected error, got effect: {}", name),
    }
}

// --- Math module ---

#[test]
fn import_math_qualified() {
    ok("
import Math
fun main () -> ()
main () = print (Math.add 1 2)
");
}

#[test]
fn import_math_with_alias() {
    ok("
import Math as M
fun main () -> ()
main () = print (M.double 5)
");
}

#[test]
fn import_math_exposing() {
    // Syntax: import Math (name1, name2)  -- no 'exposing' keyword
    ok("
import Math (add, double)
fun main () -> ()
main () = print (add 3 4)
");
}

#[test]
fn import_private_function_not_accessible_qualified() {
    let msg = err("
import Math
fun main () -> ()
main () = print (Math.secret ())
");
    assert!(
        msg.contains("Math.secret"),
        "expected missing qualified name error, got: {}",
        msg
    );
}

#[test]
fn import_private_function_not_exposable() {
    let msg = err("
import Math (secret)
fun main () -> ()
main () = print (secret ())
");
    assert!(
        msg.contains("secret"),
        "expected not-exported error, got: {}",
        msg
    );
}

// --- Shapes module ---

#[test]
fn import_shapes_area_and_constructor() {
    // Constructors are values in scope under their module prefix: Shapes.Circle
    // But QualifiedName only handles lowercase names after '.', so constructors
    // must be imported unqualified.
    // area is a pub function; Circle is a pub constructor -- both exported.
    ok("
import Shapes (area)
import Shapes (Circle)
fun main () -> ()
main () = print (area (Circle 3.0))
");
}

#[test]
fn import_shapes_qualified_function() {
    // Qualified access works for lowercase names (functions)
    ok("
import Shapes (Circle)
import Shapes
fun main () -> ()
main () = print (Shapes.area (Circle 3.0))
");
}

#[test]
fn private_type_constructor_not_exported() {
    // Config is from a private type, so it shouldn't be exported
    let msg = err("
import Shapes (Config)
fun main () -> ()
main () = print ()
");
    assert!(
        msg.contains("Config"),
        "expected not-exported error, got: {}",
        msg
    );
}

// --- Qualified constructors ---

#[test]
fn qualified_constructor() {
    ok("
import Shapes
fun main () -> ()
main () = print (Shapes.area (Shapes.Circle 3.0))
");
}

// --- Caching: same module imported twice gives same bindings ---

#[test]
fn module_imported_twice_no_error() {
    ok("
import Math
import Math as M2
fun main () -> ()
main () = {
  let a = Math.add 1 2
  let b = M2.double 3
  print (Math.add a b)
}
");
}

// --- Multiline import list ---

#[test]
fn import_multiline_exposing() {
    // Newlines inside (...) are suppressed by the lexer's nesting counter
    ok("
import Math (
  add,
  double,
)
fun main () -> ()
main () = print (add 1 (double 2))
");
}

// --- Qualified constructor patterns ---

#[test]
fn qualified_constructor_pattern() {
    ok("
import Shapes
fun describe (s: Shapes.Shape) -> String
describe s = case s {
  Shapes.Circle(r) -> \"circle\"
  Shapes.Rect(w, h) -> \"rect\"
}
fun main () -> ()
main () = print (describe (Shapes.Circle 3.0))
");
}

// --- Cross-module traits ---

#[test]
fn cross_module_trait_impl() {
    // Trait defined in Printable, impl defined locally -- dispatch must find it
    // `greet` (the method) is what's exported, not the trait name `Greet`
    ok("
import Printable (greet)
record Dog { name: String }
impl Greet for Dog {
  greet d = \"Woof, I am \" <> d.name
}
fun main () -> ()
main () = print (greet (Dog { name: \"Rex\" }))
");
}

#[test]
fn cross_module_show_impl() {
    // impl Show for Animal defined in Animals module, dispatched in main.
    // Records have no runtime constructor value -- Animal{} is just syntax.
    // Importing the module pulls in the mangled __impl_Show_Animal_show name.
    ok("
import Animals
fun main () -> ()
main () = {
  let a = Animal { name: \"Rex\", species: \"Dog\" }
  print (show a)
}
");
}

#[test]
fn cross_module_show_in_interpolation() {
    // impl Show for Animal used implicitly inside string interpolation
    ok("
import Animals
fun main () -> ()
main () = {
  let a = Animal { name: \"Rex\", species: \"Dog\" }
  print $\"Animal: {a}\"
}
");
}

#[test]
fn qualified_record_create() {
    // A.Animal { ... } should create an Animal record using the unqualified type name
    ok("
import Animals as A
fun main () -> ()
main () = {
  let a = A.Animal { name: \"Rex\", species: \"Dog\" }
  print (show a)
}
");
}

// --- Stdlib (Std.*) ---

#[test]
fn stdlib_maybe_qualified() {
    ok("
fun main () -> ()
main () = {
  let x = Maybe.map (fun n -> n + 1) (Some 41)
  print (show x)
}
");
}

#[test]
fn stdlib_constructors_unqualified() {
    ok("
fun main () -> ()
main () = {
  let x = Some 1
  let y = None
  let z = Ok 2
  let w = Err \"oops\"
  print (show x)
}
");
}

#[test]
fn stdlib_list_qualified() {
    ok("
fun main () -> ()
main () = {
  let xs = [1, 2, 3]
  let ys = List.map (fun x -> x * 2) xs
  print (show ys)
}
");
}

// --- Error cases ---

#[test]
fn circular_import_gives_error() {
    let msg = err("
import CycleA
fun main () -> ()
main () = print ()
");
    assert!(
        msg.contains("CycleA") || msg.contains("CycleB") || msg.contains("circular") || msg.contains("cycle"),
        "expected circular import error, got: {}",
        msg
    );
}

#[test]
fn missing_module_gives_error() {
    let msg = err("
import DoesNotExist
fun main () -> ()
main () = print ()
");
    assert!(
        msg.contains("DoesNotExist"),
        "expected missing module error, got: {}",
        msg
    );
}
