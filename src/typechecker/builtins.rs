use super::{Checker, ImplInfo, Scheme, TraitInfo, Type};

impl Checker {
    pub(crate) fn register_builtins(&mut self) {
        // Note: Show and Ord traits are defined in Std.dy (loaded before
        // stdlib modules). Eq is built-in (BEAM BIF dispatch).

        // Built-in Num trait (arithmetic: +, -, *, /, %, unary -)
        self.traits.insert(
            "Num".into(),
            TraitInfo {
                type_param: "a".into(),
                supertraits: vec![],
                methods: vec![],
            },
        );
        for prim in &["Int", "Float"] {
            self.trait_impls.insert(
                ("Num".into(), prim.to_string()),
                ImplInfo {
                    param_constraints: vec![],
                    span: None,
                },
            );
        }

        // Built-in Eq trait (==, !=)
        self.traits.insert(
            "Eq".into(),
            TraitInfo {
                type_param: "a".into(),
                supertraits: vec![],
                methods: vec![],
            },
        );
        for prim in &["Int", "Float", "String", "Bool", "Unit"] {
            self.trait_impls.insert(
                ("Eq".into(), prim.to_string()),
                ImplInfo {
                    param_constraints: vec![],
                    span: None,
                },
            );
        }

        // Ord impls for primitives are defined in Std.Int, Std.Float, Std.String
        // (they provide real dict constructors for `compare`).

        // panic : String -> Never (crashes at runtime)
        self.env.insert(
            "panic".into(),
            Scheme {
                forall: vec![],
                constraints: vec![],
                ty: Type::Arrow(Box::new(Type::string()), Box::new(Type::Never)),
            },
        );

        // todo : Unit -> Never (type hole, crashes at runtime with "not implemented")
        self.env.insert(
            "todo".into(),
            Scheme {
                forall: vec![],
                constraints: vec![],
                ty: Type::Arrow(Box::new(Type::unit()), Box::new(Type::Never)),
            },
        );

        // List constructors
        let a = self.fresh_var();
        let a_id = match &a {
            Type::Var(id) => *id,
            _ => unreachable!(),
        };
        self.constructors.insert(
            "Nil".into(),
            Scheme {
                forall: vec![a_id],
                constraints: vec![],
                ty: Type::Con("List".into(), vec![a.clone()]),
            },
        );

        let a = self.fresh_var();
        let a_id = match &a {
            Type::Var(id) => *id,
            _ => unreachable!(),
        };
        let list_a = Type::Con("List".into(), vec![a.clone()]);
        self.constructors.insert(
            "Cons".into(),
            Scheme {
                forall: vec![a_id],
                constraints: vec![],
                ty: Type::Arrow(
                    Box::new(a),
                    Box::new(Type::Arrow(Box::new(list_a.clone()), Box::new(list_a))),
                ),
            },
        );

        // Bool constructors
        self.constructors.insert(
            "True".into(),
            Scheme {
                forall: vec![],
                constraints: vec![],
                ty: Type::bool(),
            },
        );
        self.constructors.insert(
            "False".into(),
            Scheme {
                forall: vec![],
                constraints: vec![],
                ty: Type::bool(),
            },
        );

        // Built-in ADT variant maps (for exhaustiveness checking)
        self.adt_variants
            .insert("List".into(), vec![("Nil".into(), 0), ("Cons".into(), 2)]);
        self.adt_variants
            .insert("Bool".into(), vec![("True".into(), 0), ("False".into(), 0)]);

        // Built-in type arities
        for name in &["Int", "Float", "String", "Bool", "Unit"] {
            self.type_arity.insert(name.to_string(), 0);
        }
        self.type_arity.insert("List".into(), 1);

        // Show, Debug, and Eq for Tuple (any arity -- all params must satisfy the trait)
        // We use "Tuple" as the type name; param_constraints are checked dynamically
        // based on actual type args at constraint resolution time
        self.trait_impls.insert(
            ("Show".into(), "Tuple".into()),
            ImplInfo {
                param_constraints: vec![],
                span: None,
            }, // handled specially in check_pending_constraints
        );
        self.trait_impls.insert(
            ("Debug".into(), "Tuple".into()),
            ImplInfo {
                param_constraints: vec![],
                span: None,
            }, // handled specially in check_pending_constraints
        );
        self.trait_impls.insert(
            ("Eq".into(), "Tuple".into()),
            ImplInfo {
                param_constraints: vec![],
                span: None,
            }, // handled specially in check_pending_constraints
        );

        // --- Dict type ---

        // Eq for Dict k v: requires Eq on both k and v
        self.trait_impls.insert(
            ("Eq".into(), "Dict".into()),
            ImplInfo {
                param_constraints: vec![("Eq".into(), 0), ("Eq".into(), 1)],
                span: None,
            },
        );

        // Dict.empty : forall k v. Dict k v
        {
            let k = self.fresh_var();
            let k_id = match &k {
                Type::Var(id) => *id,
                _ => unreachable!(),
            };
            let v = self.fresh_var();
            let v_id = match &v {
                Type::Var(id) => *id,
                _ => unreachable!(),
            };
            self.env.insert(
                "Dict.empty".into(),
                Scheme {
                    forall: vec![k_id, v_id],
                    constraints: vec![],
                    ty: Type::Con("Dict".into(), vec![k, v]),
                },
            );
        }

        // Dict.get : forall k v. Eq k => k -> Dict k v -> Maybe v
        {
            let k = self.fresh_var();
            let k_id = match &k {
                Type::Var(id) => *id,
                _ => unreachable!(),
            };
            let v = self.fresh_var();
            let v_id = match &v {
                Type::Var(id) => *id,
                _ => unreachable!(),
            };
            let dict_kv = Type::Con("Dict".into(), vec![k.clone(), v.clone()]);
            let maybe_v = Type::Con("Maybe".into(), vec![v]);
            self.env.insert(
                "Dict.get".into(),
                Scheme {
                    forall: vec![k_id, v_id],
                    constraints: vec![("Eq".into(), k_id)],
                    ty: Type::Arrow(
                        Box::new(k),
                        Box::new(Type::Arrow(Box::new(dict_kv), Box::new(maybe_v))),
                    ),
                },
            );
        }

        // --- Conversion builtins ---

        // Int.parse : String -> Maybe Int
        self.env.insert(
            "Int.parse".into(),
            Scheme {
                forall: vec![],
                constraints: vec![],
                ty: Type::Arrow(
                    Box::new(Type::string()),
                    Box::new(Type::Con("Maybe".into(), vec![Type::int()])),
                ),
            },
        );

        // Float.parse : String -> Maybe Float
        self.env.insert(
            "Float.parse".into(),
            Scheme {
                forall: vec![],
                constraints: vec![],
                ty: Type::Arrow(
                    Box::new(Type::string()),
                    Box::new(Type::Con("Maybe".into(), vec![Type::float()])),
                ),
            },
        );
    }
}
