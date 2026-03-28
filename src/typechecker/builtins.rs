use super::{Checker, ImplInfo, Scheme, TraitInfo, Type};

impl Checker {
    pub(crate) fn register_builtins(&mut self) {
        // Note: Show and Ord traits are defined in Std.Base
        // (loaded before stdlib modules).
        // Num, Semigroup, and Eq are built-in marker traits (operator dispatch,
        // no dictionary passing).

        // Built-in Num trait (arithmetic: +, -, *, /, %, unary -)
        self.trait_state.traits.insert(
            "Num".into(),
            TraitInfo {
                type_params: vec!["a".into()],
                supertraits: vec![],
                methods: vec![],
            },
        );
        for prim in &["Int", "Float"] {
            self.trait_state.impls.insert(
                ("Num".into(), vec![], prim.to_string()),
                ImplInfo {
                    param_constraints: vec![],
                    trait_type_args: vec![],
                    span: None,
                },
            );
        }

        // Built-in Semigroup trait (<>)
        self.trait_state.traits.insert(
            "Semigroup".into(),
            TraitInfo {
                type_params: vec!["a".into()],
                supertraits: vec![],
                methods: vec![],
            },
        );
        for prim in &["String", "List"] {
            self.trait_state.impls.insert(
                ("Semigroup".into(), vec![], prim.to_string()),
                ImplInfo {
                    param_constraints: vec![],
                    trait_type_args: vec![],
                    span: None,
                },
            );
        }

        // Built-in Eq trait (==, !=)
        self.trait_state.traits.insert(
            "Eq".into(),
            TraitInfo {
                type_params: vec!["a".into()],
                supertraits: vec![],
                methods: vec![],
            },
        );
        for prim in &["Int", "Float", "String", "Bool", "Unit"] {
            self.trait_state.impls.insert(
                ("Eq".into(), vec![], prim.to_string()),
                ImplInfo {
                    param_constraints: vec![],
                    trait_type_args: vec![],
                    span: None,
                },
            );
        }

        // Ord impls for primitives are defined in Std.Int, Std.Float, Std.String
        // (they provide real dict constructors for `compare`).

        // panic : forall a. String -> a (crashes at runtime)
        {
            let a_id = self.next_var;
            self.next_var += 1;
            self.env.insert(
                "panic".into(),
                Scheme {
                    forall: vec![a_id],
                    constraints: vec![],
                    ty: Type::arrow(Type::string(), Type::Var(a_id)),
                },
            );
        }

        // todo : forall a. Unit -> a (type hole, crashes at runtime with "not implemented")
        {
            let a_id = self.next_var;
            self.next_var += 1;
            self.env.insert(
                "todo".into(),
                Scheme {
                    forall: vec![a_id],
                    constraints: vec![],
                    ty: Type::arrow(Type::unit(), Type::Var(a_id)),
                },
            );
        }

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
                ty: Type::arrow(
                    a,
                    Type::arrow(list_a.clone(), list_a),
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
        self.trait_state.impls.insert(
            ("Show".into(), vec![], "Tuple".into()),
            ImplInfo {
                param_constraints: vec![],
                trait_type_args: vec![],
                span: None,
            }, // handled specially in check_pending_constraints
        );
        self.trait_state.impls.insert(
            ("Debug".into(), vec![], "Tuple".into()),
            ImplInfo {
                param_constraints: vec![],
                trait_type_args: vec![],
                span: None,
            }, // handled specially in check_pending_constraints
        );
        self.trait_state.impls.insert(
            ("Eq".into(), vec![], "Tuple".into()),
            ImplInfo {
                param_constraints: vec![],
                trait_type_args: vec![],
                span: None,
            }, // handled specially in check_pending_constraints
        );

        // --- Dict type ---

        // Eq for Dict k v: requires Eq on both k and v
        self.trait_state.impls.insert(
            ("Eq".into(), vec![], "Dict".into()),
            ImplInfo {
                param_constraints: vec![("Eq".into(), 0), ("Eq".into(), 1)],
                trait_type_args: vec![],
                span: None,
            },
        );



    }
}
