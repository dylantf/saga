use std::collections::{BTreeSet, HashMap, HashSet};

use super::{header::ModuleHeader, scan::ModuleMap};

/// Explicit module dependency graph built from import declarations.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ModuleGraph {
    pub adjacency: HashMap<String, Vec<String>>,
}

/// A strongly connected set of modules that must be processed together.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModuleScc {
    pub modules: Vec<String>,
}

impl ModuleScc {
    pub fn is_cycle(&self) -> bool {
        self.modules.len() > 1
    }
}

impl ModuleGraph {
    pub fn from_headers<'a>(headers: impl IntoIterator<Item = &'a ModuleHeader>) -> Self {
        let mut adjacency = HashMap::new();
        for header in headers {
            if let Some(module) = &header.module_name {
                adjacency.insert(module.clone(), header.import_modules());
            }
        }
        ModuleGraph { adjacency }
    }

    pub fn from_programs<'a>(
        programs: impl IntoIterator<Item = (&'a str, &'a [crate::ast::Decl])>,
    ) -> Self {
        let mut adjacency = HashMap::new();
        for (module, program) in programs {
            adjacency.insert(module.to_string(), import_modules_for_program(program));
        }
        ModuleGraph { adjacency }
    }

    pub fn dependencies(&self, module: &str) -> Option<&[String]> {
        self.adjacency.get(module).map(Vec::as_slice)
    }

    pub fn modules(&self) -> Vec<String> {
        let mut modules = BTreeSet::new();
        for (module, dependencies) in &self.adjacency {
            modules.insert(module.clone());
            modules.extend(dependencies.iter().cloned());
        }
        modules.into_iter().collect()
    }

    pub fn strongly_connected_components(&self) -> Vec<ModuleScc> {
        let mut state = TarjanState::new(self);
        for module in self.modules() {
            if !state.indices.contains_key(&module) {
                state.connect(module);
            }
        }
        state.components
    }

    /// Returns SCCs in dependency-first order: if A imports B, B's component
    /// appears before A's component unless they are in the same SCC.
    pub fn dependency_ordered_sccs(&self) -> Vec<ModuleScc> {
        let components = self.strongly_connected_components();
        if components.is_empty() {
            return Vec::new();
        }

        let mut module_to_component = HashMap::new();
        for (index, component) in components.iter().enumerate() {
            for module in &component.modules {
                module_to_component.insert(module.as_str(), index);
            }
        }

        let mut dependents: Vec<BTreeSet<usize>> = vec![BTreeSet::new(); components.len()];
        let mut indegree = vec![0usize; components.len()];
        for (module, dependencies) in &self.adjacency {
            let Some(&module_component) = module_to_component.get(module.as_str()) else {
                continue;
            };
            for dependency in dependencies {
                let Some(&dependency_component) = module_to_component.get(dependency.as_str())
                else {
                    continue;
                };
                if dependency_component != module_component
                    && dependents[dependency_component].insert(module_component)
                {
                    indegree[module_component] += 1;
                }
            }
        }

        let mut ready = BTreeSet::new();
        for (index, count) in indegree.iter().enumerate() {
            if *count == 0 {
                ready.insert((components[index].sort_key(), index));
            }
        }

        let mut ordered = Vec::with_capacity(components.len());
        let mut seen = HashSet::new();
        while let Some((_, index)) = ready.pop_first() {
            if !seen.insert(index) {
                continue;
            }
            ordered.push(components[index].clone());
            for dependent in &dependents[index] {
                indegree[*dependent] -= 1;
                if indegree[*dependent] == 0 {
                    ready.insert((components[*dependent].sort_key(), *dependent));
                }
            }
        }

        if ordered.len() != components.len() {
            let mut remaining: Vec<_> = components
                .into_iter()
                .enumerate()
                .filter(|(index, _)| !seen.contains(index))
                .map(|(_, component)| component)
                .collect();
            remaining.sort_by_key(ModuleScc::sort_key);
            ordered.extend(remaining);
        }

        ordered
    }

    fn sorted_dependencies(&self, module: &str) -> Vec<String> {
        let mut dependencies = self.adjacency.get(module).cloned().unwrap_or_default();
        dependencies.sort();
        dependencies.dedup();
        dependencies
    }
}

impl ModuleScc {
    fn sort_key(&self) -> String {
        self.modules.first().cloned().unwrap_or_default()
    }
}

impl ModuleHeader {
    fn import_modules(&self) -> Vec<String> {
        let mut modules: Vec<String> = self
            .imports
            .iter()
            .map(|import| import.module.clone())
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect();
        modules.sort();
        modules
    }
}

struct TarjanState<'a> {
    graph: &'a ModuleGraph,
    next_index: usize,
    stack: Vec<String>,
    indices: HashMap<String, usize>,
    lowlinks: HashMap<String, usize>,
    on_stack: HashSet<String>,
    components: Vec<ModuleScc>,
}

impl<'a> TarjanState<'a> {
    fn new(graph: &'a ModuleGraph) -> Self {
        TarjanState {
            graph,
            next_index: 0,
            stack: Vec::new(),
            indices: HashMap::new(),
            lowlinks: HashMap::new(),
            on_stack: HashSet::new(),
            components: Vec::new(),
        }
    }

    fn connect(&mut self, module: String) {
        let index = self.next_index;
        self.next_index += 1;
        self.indices.insert(module.clone(), index);
        self.lowlinks.insert(module.clone(), index);
        self.stack.push(module.clone());
        self.on_stack.insert(module.clone());

        for dependency in self.graph.sorted_dependencies(&module) {
            if !self.indices.contains_key(&dependency) {
                self.connect(dependency.clone());
                let dependency_lowlink = self.lowlinks[&dependency];
                let module_lowlink = self.lowlinks[&module];
                self.lowlinks
                    .insert(module.clone(), module_lowlink.min(dependency_lowlink));
            } else if self.on_stack.contains(&dependency) {
                let dependency_index = self.indices[&dependency];
                let module_lowlink = self.lowlinks[&module];
                self.lowlinks
                    .insert(module.clone(), module_lowlink.min(dependency_index));
            }
        }

        if self.lowlinks[&module] == self.indices[&module] {
            let mut modules = Vec::new();
            while let Some(member) = self.stack.pop() {
                self.on_stack.remove(&member);
                let done = member == module;
                modules.push(member);
                if done {
                    break;
                }
            }
            modules.sort();
            self.components.push(ModuleScc { modules });
        }
    }
}

pub fn import_modules_for_program(program: &[crate::ast::Decl]) -> Vec<String> {
    let mut modules = BTreeSet::new();
    for decl in program {
        if let crate::ast::Decl::Import { module_path, .. } = decl {
            modules.insert(module_path.join("."));
        }
    }
    modules.into_iter().collect()
}

pub fn build_module_graph(module_map: &ModuleMap) -> Result<ModuleGraph, String> {
    build_module_graph_with_sources(module_map, &HashMap::new())
}

pub fn build_module_graph_with_sources(
    module_map: &ModuleMap,
    source_overlay: &HashMap<std::path::PathBuf, String>,
) -> Result<ModuleGraph, String> {
    let mut adjacency = HashMap::new();
    for (module_name, path) in module_map {
        adjacency.insert(
            module_name.clone(),
            module_dependencies_from_file(module_name, path, source_overlay)?,
        );
    }
    Ok(ModuleGraph { adjacency })
}

pub fn build_reachable_module_graph_with_sources(
    module_map: &ModuleMap,
    root_module: &str,
    source_overlay: &HashMap<std::path::PathBuf, String>,
) -> Result<ModuleGraph, String> {
    let mut adjacency = HashMap::new();
    let mut stack = vec![root_module.to_string()];
    let mut seen = HashSet::new();
    while let Some(module_name) = stack.pop() {
        if !seen.insert(module_name.clone()) {
            continue;
        }
        let Some(path) = module_map.get(&module_name) else {
            adjacency.insert(module_name, Vec::new());
            continue;
        };
        let dependencies = module_dependencies_from_file(&module_name, path, source_overlay)?;
        for dependency in &dependencies {
            if module_map.contains_key(dependency) && !seen.contains(dependency) {
                stack.push(dependency.clone());
            }
        }
        adjacency.insert(module_name, dependencies);
    }
    Ok(ModuleGraph { adjacency })
}

fn module_dependencies_from_file(
    module_name: &str,
    path: &std::path::Path,
    source_overlay: &HashMap<std::path::PathBuf, String>,
) -> Result<Vec<String>, String> {
    let source = source_overlay
        .get(path)
        .cloned()
        .map(Ok)
        .unwrap_or_else(|| std::fs::read_to_string(path))
        .map_err(|e| format!("cannot read module '{}': {}", module_name, e))?;
    let tokens = crate::lexer::Lexer::new(&source)
        .lex()
        .map_err(|e| format!("lex error in module '{}': {}", module_name, e.message))?;
    let program = crate::parser::Parser::new(tokens)
        .parse_program()
        .map_err(|e| format!("parse error in module '{}': {}", module_name, e.message))?;
    Ok(import_modules_for_program(&program))
}

#[cfg(test)]
mod module_graph_tests {
    use super::*;

    fn parse(src: &str) -> crate::ast::Program {
        let tokens = crate::lexer::Lexer::new(src).lex().expect("lex");
        crate::parser::Parser::new(tokens)
            .parse_program()
            .expect("parse")
    }

    #[test]
    fn module_graph_records_import_edges_without_typechecking() {
        let a = parse("module A\nimport B\npub type AType = AType\n");
        let b = parse("module B\nimport A\nimport C (pub value)\npub type BType = BType\n");
        let c = parse("module C\npub fun value : Unit -> Unit\nvalue () = ()\n");

        let graph = ModuleGraph::from_programs([
            ("A", a.as_slice()),
            ("B", b.as_slice()),
            ("C", c.as_slice()),
        ]);

        assert_eq!(graph.dependencies("A"), Some(&["B".to_string()][..]));
        assert_eq!(
            graph.dependencies("B"),
            Some(&["A".to_string(), "C".to_string()][..])
        );
        assert_eq!(graph.dependencies("C"), Some(&[][..]));
    }

    #[test]
    fn strongly_connected_components_group_mutual_imports() {
        let graph = ModuleGraph {
            adjacency: HashMap::from([
                ("A".to_string(), vec!["B".to_string()]),
                ("B".to_string(), vec!["A".to_string(), "C".to_string()]),
                ("C".to_string(), vec![]),
            ]),
        };

        let mut components = graph.strongly_connected_components();
        components.sort_by_key(ModuleScc::sort_key);

        assert_eq!(
            components,
            vec![
                ModuleScc {
                    modules: vec!["A".to_string(), "B".to_string()],
                },
                ModuleScc {
                    modules: vec!["C".to_string()],
                },
            ]
        );
        assert!(components[0].is_cycle());
    }

    #[test]
    fn dependency_ordered_sccs_put_dependencies_first() {
        let graph = ModuleGraph {
            adjacency: HashMap::from([
                ("A".to_string(), vec!["B".to_string()]),
                ("B".to_string(), vec!["A".to_string(), "C".to_string()]),
                ("C".to_string(), vec!["D".to_string()]),
                ("D".to_string(), vec![]),
                ("E".to_string(), vec!["A".to_string()]),
            ]),
        };

        let ordered = graph.dependency_ordered_sccs();

        assert_eq!(
            ordered,
            vec![
                ModuleScc {
                    modules: vec!["D".to_string()],
                },
                ModuleScc {
                    modules: vec!["C".to_string()],
                },
                ModuleScc {
                    modules: vec!["A".to_string(), "B".to_string()],
                },
                ModuleScc {
                    modules: vec!["E".to_string()],
                },
            ]
        );
    }

    #[test]
    fn build_module_graph_reads_project_module_map() {
        let root = std::env::temp_dir().join(format!(
            "saga_module_graph_test_{}_{}",
            std::process::id(),
            crate::ast::NodeId::fresh().0
        ));
        std::fs::create_dir_all(&root).expect("create temp module dir");
        let a_path = root.join("A.saga");
        let b_path = root.join("B.saga");
        std::fs::write(&a_path, "module A\nimport B\npub type AType = AType\n").expect("write A");
        std::fs::write(&b_path, "module B\nimport A\npub type BType = BType\n").expect("write B");

        let mut map = ModuleMap::new();
        map.insert("A".to_string(), a_path);
        map.insert("B".to_string(), b_path);

        let graph = build_module_graph(&map).expect("graph");
        assert_eq!(graph.dependencies("A"), Some(&["B".to_string()][..]));
        assert_eq!(graph.dependencies("B"), Some(&["A".to_string()][..]));

        let _ = std::fs::remove_dir_all(root);
    }
}
