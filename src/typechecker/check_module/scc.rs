use super::{build_module_graph_with_sources, build_reachable_module_graph_with_sources};
use crate::typechecker::Checker;

impl Checker {
    pub(super) fn cyclic_component_containing(
        &mut self,
        module_name: &str,
    ) -> Result<Option<Vec<String>>, String> {
        let Some(map) = self.modules.map.as_ref() else {
            return Ok(None);
        };
        let reachable_graph;
        let graph = if let Some(graph) = self.modules.module_graph.as_ref() {
            graph
        } else {
            match build_module_graph_with_sources(map, &self.modules.source_overlay) {
                Ok(graph) => {
                    self.modules.module_graph = Some(graph);
                    self.modules
                        .module_graph
                        .as_ref()
                        .expect("cached module graph")
                }
                Err(_) => {
                    reachable_graph = build_reachable_module_graph_with_sources(
                        map,
                        module_name,
                        &self.modules.source_overlay,
                    )?;
                    &reachable_graph
                }
            }
        };
        Ok(graph
            .strongly_connected_components()
            .into_iter()
            .find(|component| {
                component.modules.iter().any(|module| module == module_name)
                    && (component.is_cycle()
                        || graph
                            .dependencies(module_name)
                            .is_some_and(|deps| deps.iter().any(|dep| dep == module_name)))
            })
            .map(|component| component.modules))
    }
}
