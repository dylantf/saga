use std::collections::HashSet;

use tower_lsp::lsp_types::*;

use dylang::ast::Decl;
use dylang::typechecker::CheckResult;

use crate::line_index::LineIndex;

/// Generate code actions for the given diagnostics range.
/// Currently handles: adding missing handler arms.
pub fn collect_code_actions(
    tc_result: &CheckResult,
    program: &[Decl],
    line_index: &LineIndex,
    source: &str,
    uri: &Url,
    range: Range,
) -> Vec<CodeActionOrCommand> {
    let mut actions = Vec::new();

    // Find handler defs whose diagnostics overlap the requested range
    for decl in program {
        if let Decl::HandlerDef {
            name,
            effects,
            arms,
            recovered_arms,
            span,
            ..
        } = decl
        {
            let handler_start = line_index.offset_to_line_col(span.start, source);
            let handler_end = line_index.offset_to_line_col(span.end, source);
            let handler_range = Range {
                start: Position::new(handler_start.0 as u32, handler_start.1 as u32),
                end: Position::new(handler_end.0 as u32, handler_end.1 as u32),
            };

            // Only offer actions if the cursor/range overlaps this handler
            if !ranges_overlap(&range, &handler_range) {
                continue;
            }

            let handled: HashSet<&str> = arms
                .iter()
                .chain(recovered_arms.iter())
                .map(|a| a.op_name.as_str())
                .collect();

            // Collect all missing ops across all effects
            let mut all_missing: Vec<(String, String)> = Vec::new(); // (effect_name, arm_text)
            for effect_ref in effects {
                if let Some(info) = tc_result.effects.get(&effect_ref.name) {
                    for op in &info.ops {
                        if handled.contains(op.name.as_str()) {
                            continue;
                        }
                        let arm_text = format_arm(op);
                        all_missing.push((effect_ref.name.clone(), arm_text));
                    }
                }
            }

            if all_missing.is_empty() {
                continue;
            }

            // Find insertion point: just before the closing `}`
            let insert_offset = span.end;
            let (insert_line, _) = line_index.offset_to_line_col(insert_offset, source);
            let insert_pos = Position::new(insert_line as u32, 0);

            // Detect indentation from existing arms, or default to 2 spaces
            let indent = if let Some(first_arm) = arms.first() {
                let (_, col) = line_index.offset_to_line_col(first_arm.span.start, source);
                " ".repeat(col)
            } else {
                "  ".to_string()
            };

            // "Add all missing arms" action (first, so it appears at top)
            if all_missing.len() > 1 {
                let all_text: String = all_missing
                    .iter()
                    .map(|(_, arm)| format!("{}{}\n", indent, arm))
                    .collect();

                let edit = TextEdit {
                    range: Range {
                        start: insert_pos,
                        end: insert_pos,
                    },
                    new_text: all_text,
                };

                actions.push(CodeActionOrCommand::CodeAction(CodeAction {
                    title: format!(
                        "Add all missing arms to '{}'",
                        name
                    ),
                    kind: Some(CodeActionKind::QUICKFIX),
                    edit: Some(WorkspaceEdit {
                        changes: Some([(uri.clone(), vec![edit])].into_iter().collect()),
                        ..Default::default()
                    }),
                    diagnostics: None,
                    is_preferred: Some(true),
                    ..Default::default()
                }));
            }

            // Individual "Add missing arm: X" actions
            for (effect_name, arm_text) in &all_missing {
                let op_name = arm_text.split_whitespace().next().unwrap_or("?");
                let text = format!("{}{}\n", indent, arm_text);

                let edit = TextEdit {
                    range: Range {
                        start: insert_pos,
                        end: insert_pos,
                    },
                    new_text: text,
                };

                actions.push(CodeActionOrCommand::CodeAction(CodeAction {
                    title: format!("Add missing arm: {} ({})", op_name, effect_name),
                    kind: Some(CodeActionKind::QUICKFIX),
                    edit: Some(WorkspaceEdit {
                        changes: Some([(uri.clone(), vec![edit])].into_iter().collect()),
                        ..Default::default()
                    }),
                    diagnostics: None,
                    is_preferred: Some(false),
                    ..Default::default()
                }));
            }
        }
    }

    actions
}

/// Format a handler arm from an effect op signature.
/// Produces: `op_name arg1 arg2 = todo`
fn format_arm(op: &dylang::typechecker::EffectOpSig) -> String {
    if op.params.is_empty() {
        format!("{} () = todo", op.name)
    } else {
        let params: Vec<String> = op
            .params
            .iter()
            .enumerate()
            .map(|(i, (label, _))| {
                if label.starts_with('_') {
                    format!("arg{}", i + 1)
                } else {
                    label.clone()
                }
            })
            .collect();
        format!("{} {} = todo", op.name, params.join(" "))
    }
}

fn ranges_overlap(a: &Range, b: &Range) -> bool {
    a.start <= b.end && b.start <= a.end
}
