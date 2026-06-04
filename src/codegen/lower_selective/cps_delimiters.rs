use super::*;

impl<'a, 'info> DirectLowerer<'a, 'info> {
    pub(super) fn delimited_perform_k(&mut self, effect: &str, return_k: CExpr) -> CExpr {
        if !self
            .result_delimiter_stack
            .iter()
            .any(|frame| frame.handles_effect(effect))
        {
            return return_k;
        }

        let arg = self.fresh_cps_temp("_DelimitedKArg");
        let applied = CExpr::Apply(Box::new(return_k), vec![CExpr::Var(arg.clone())]);
        let body = self.wrap_result_delimiter_stack_until(applied, effect);
        CExpr::Fun(vec![arg], Box::new(body))
    }

    pub(super) fn wrap_result_delimiter_stack_until(
        &mut self,
        mut body: CExpr,
        effect: &str,
    ) -> CExpr {
        let frames = self.result_delimiter_stack.clone();
        for frame in frames.iter().rev() {
            body = self.wrap_with_result_delimiter_raw(body, &frame.abort_marker);
            if frame.handles_effect(effect) {
                break;
            }
        }
        body
    }
}
