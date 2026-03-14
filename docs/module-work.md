- [x] 1. Redundant re-parse/re-typecheck in cmd_build_project (the biggest one)

  In main.rs:217-228, each imported user module is re-parsed and re-typechecked with a fresh make_checker. The typechecker cache from the initial Main.dy pass (which already transitively checked everything) is not reused. The comment says "typechecker caches make this fast" but that's not true: each mod_checker is a brand new checker, so there's no cache hit. This means every module gets fully typechecked twice: once during Main.dy's transitive import resolution, and once during the build loop. For a project with N modules, this is O(N^2) in the worst case due to transitive re-checking.

  The fix: pass the already-populated checker.tc_codegen_info and cached data to the per-module elaboration step, or restructure so that the initial pass stores enough to skip the second typecheck entirely.

- [x] 2. compile_std_modules also re-typechecks redundantly

  In main.rs:122-126, each Std module gets a fresh make_checker(None) and is fully re-typechecked. Same issue as above. The main checker already typechecked these during import resolution.

- [x] 3. Script mode silently ignores imports

  In check_module.rs:67, when project_root is None and the import isn't a builtin Std module, typecheck_import returns Ok(()) silently. If someone writes import MyLib in a script, they get no error. It just silently doesn't import anything. Their code will then fail later with a confusing "unknown variable" error instead of "imports not supported in script mode".

- [x] 4. Script-mode build (cmd_build) prepends the full prelude AST

  In main.rs:302-304, script mode concatenates the entire prelude AST with the user program before elaboration. This means the emitted .core file contains all prelude functions, even unused ones. In project mode each module is self-contained and imports are inter-module calls. This asymmetry means script-mode .core files are bloated and don't match how project-mode works.

- [ ] 5. No emit command for project mode

  dylang emit <file> only works in script mode. There's no way to inspect the generated Core Erlang for a single module within a project. Adding dylang emit (no arg, project mode) or dylang emit --module Foo would be useful for debugging codegen.

- [ ] 6. Cache cloning in typecheck_import

  At check_module.rs:204-209, six HashMap caches are .clone()d into every module checker. For deep import trees this is a lot of allocation. The caches are read-heavy and append-only during module checking. Using Rc<RefCell<...>> or passing references would avoid the cloning, but this is a performance concern rather than a correctness one.
