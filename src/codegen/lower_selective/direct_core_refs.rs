use super::*;

pub(super) fn core_expr_mentions_var(source_name: &str, expr: &CExpr) -> bool {
    let var = core_var(source_name);
    core_expr_mentions_core_var(&var, expr)
}

pub(super) fn core_expr_mentions_core_var(var: &str, expr: &CExpr) -> bool {
    match expr {
        CExpr::Var(name) => name == var,
        CExpr::Lit(_) | CExpr::Nil | CExpr::FunRef(_, _) => false,
        CExpr::Fun(params, body) => {
            !params.iter().any(|param| param == var) && core_expr_mentions_core_var(var, body)
        }
        CExpr::Let(name, value, body) => {
            core_expr_mentions_core_var(var, value)
                || (name != var && core_expr_mentions_core_var(var, body))
        }
        CExpr::Apply(head, args) => {
            core_expr_mentions_core_var(var, head)
                || args.iter().any(|arg| core_expr_mentions_core_var(var, arg))
        }
        CExpr::Call(_, _, args) | CExpr::Tuple(args) | CExpr::Values(args) => {
            args.iter().any(|arg| core_expr_mentions_core_var(var, arg))
        }
        CExpr::Case(scrutinee, arms) => {
            core_expr_mentions_core_var(var, scrutinee)
                || arms.iter().any(|arm| core_arm_mentions_core_var(var, arm))
        }
        CExpr::Cons(head, tail) => {
            core_expr_mentions_core_var(var, head) || core_expr_mentions_core_var(var, tail)
        }
        CExpr::LetRec(bindings, body) => {
            bindings
                .iter()
                .any(|(_, _, binding)| core_expr_mentions_core_var(var, binding))
                || core_expr_mentions_core_var(var, body)
        }
        CExpr::Receive(arms, timeout, body) => {
            arms.iter().any(|arm| core_arm_mentions_core_var(var, arm))
                || core_expr_mentions_core_var(var, timeout)
                || core_expr_mentions_core_var(var, body)
        }
        CExpr::Try {
            expr,
            ok_var,
            ok_body,
            catch_vars,
            catch_body,
        } => {
            core_expr_mentions_core_var(var, expr)
                || (ok_var != var && core_expr_mentions_core_var(var, ok_body))
                || (catch_vars.0 != var
                    && catch_vars.1 != var
                    && catch_vars.2 != var
                    && core_expr_mentions_core_var(var, catch_body))
        }
        CExpr::Binary(segments) => segments
            .iter()
            .any(|segment| core_expr_bin_segment_mentions_core_var(var, segment)),
        CExpr::Annotated { expr, .. } => core_expr_mentions_core_var(var, expr),
    }
}

fn core_arm_mentions_core_var(var: &str, arm: &CArm) -> bool {
    core_pat_size_mentions_core_var(var, &arm.pat)
        || arm
            .guard
            .as_ref()
            .is_some_and(|guard| core_expr_mentions_core_var(var, guard))
        || (!core_pat_binds_core_var(var, &arm.pat) && core_expr_mentions_core_var(var, &arm.body))
}

fn core_expr_bin_segment_mentions_core_var(var: &str, segment: &CBinSeg<CExpr>) -> bool {
    match segment {
        CBinSeg::Byte(_) => false,
        CBinSeg::BinaryAll(value) => core_expr_mentions_core_var(var, value),
        CBinSeg::Segment { value, size, .. } => {
            core_expr_mentions_core_var(var, value)
                || matches!(size, BinSegSize::Expr(size) if core_expr_mentions_core_var(var, size))
        }
    }
}

fn core_pat_binds_core_var(var: &str, pat: &CPat) -> bool {
    match pat {
        CPat::Var(name) => name == var,
        CPat::Alias(name, pat) => name == var || core_pat_binds_core_var(var, pat),
        CPat::Lit(_) | CPat::Wildcard | CPat::Nil => false,
        CPat::Tuple(fields) | CPat::Values(fields) => fields
            .iter()
            .any(|field| core_pat_binds_core_var(var, field)),
        CPat::Cons(head, tail) => {
            core_pat_binds_core_var(var, head) || core_pat_binds_core_var(var, tail)
        }
        CPat::Binary(segments) => segments
            .iter()
            .any(|segment| core_pat_bin_segment_binds_core_var(var, segment)),
    }
}

fn core_pat_bin_segment_binds_core_var(var: &str, segment: &CBinSeg<CPat>) -> bool {
    match segment {
        CBinSeg::Byte(_) => false,
        CBinSeg::BinaryAll(value) => core_pat_binds_core_var(var, value),
        CBinSeg::Segment { value, .. } => core_pat_binds_core_var(var, value),
    }
}

fn core_pat_size_mentions_core_var(var: &str, pat: &CPat) -> bool {
    match pat {
        CPat::Var(_) | CPat::Lit(_) | CPat::Wildcard | CPat::Nil => false,
        CPat::Alias(_, pat) => core_pat_size_mentions_core_var(var, pat),
        CPat::Tuple(fields) | CPat::Values(fields) => fields
            .iter()
            .any(|field| core_pat_size_mentions_core_var(var, field)),
        CPat::Cons(head, tail) => {
            core_pat_size_mentions_core_var(var, head) || core_pat_size_mentions_core_var(var, tail)
        }
        CPat::Binary(segments) => segments
            .iter()
            .any(|segment| core_pat_bin_segment_size_mentions_core_var(var, segment)),
    }
}

fn core_pat_bin_segment_size_mentions_core_var(var: &str, segment: &CBinSeg<CPat>) -> bool {
    match segment {
        CBinSeg::Byte(_) => false,
        CBinSeg::BinaryAll(value) => core_pat_size_mentions_core_var(var, value),
        CBinSeg::Segment { value, size, .. } => {
            core_pat_size_mentions_core_var(var, value)
                || matches!(size, BinSegSize::Expr(size) if core_expr_mentions_core_var(var, size))
        }
    }
}
