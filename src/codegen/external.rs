use crate::ast::{Annotation, Lit};

/// Extract the `(erl_module, erl_func)` pair from an
/// `@external("runtime", "<mod>", "<func>")` annotation list.
pub fn extract_external(annotations: &[Annotation]) -> Option<(String, String)> {
    annotations
        .iter()
        .find(|a| a.name == "external")
        .and_then(|a| {
            if a.args.len() >= 3
                && let (Lit::String(module, _), Lit::String(func, _)) = (&a.args[1], &a.args[2])
            {
                Some((module.clone(), func.clone()))
            } else {
                None
            }
        })
}
