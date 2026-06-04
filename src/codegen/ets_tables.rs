use crate::codegen::cerl::{CArm, CExpr, CLit, CPat};

pub(crate) const ETS_REF_TABLE: &str = "saga_ref_store";
pub(crate) const ETS_VEC_TABLE: &str = "saga_vec_store";
pub(crate) const ETS_TABLE_OPTIONS: &[&str] = &["set", "public", "named_table"];

pub(crate) fn ets_table_atom_core(table_name: &str) -> CExpr {
    CExpr::Lit(CLit::Atom(table_name.to_string()))
}

pub(crate) fn ets_table_options_core() -> CExpr {
    ETS_TABLE_OPTIONS
        .iter()
        .rev()
        .fold(CExpr::Nil, |tail, atom| {
            CExpr::Cons(
                Box::new(CExpr::Lit(CLit::Atom((*atom).to_string()))),
                Box::new(tail),
            )
        })
}

pub(crate) fn wrap_ets_table_init_core(body: CExpr, table_name: &str, bind_name: &str) -> CExpr {
    let table = ets_table_atom_core(table_name);
    let init_expr = CExpr::Case(
        Box::new(CExpr::Call(
            "ets".to_string(),
            "info".to_string(),
            vec![table.clone()],
        )),
        vec![
            CArm {
                pat: CPat::Lit(CLit::Atom("undefined".to_string())),
                guard: None,
                body: CExpr::Call(
                    "ets".to_string(),
                    "new".to_string(),
                    vec![table, ets_table_options_core()],
                ),
            },
            CArm {
                pat: CPat::Wildcard,
                guard: None,
                body: CExpr::Lit(CLit::Atom("unit".to_string())),
            },
        ],
    );
    CExpr::Let(bind_name.to_string(), Box::new(init_expr), Box::new(body))
}
