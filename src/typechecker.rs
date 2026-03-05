use std::collections::HashMap;

use crate::ast::{self, BinOp, Decl, Expr, Lit, Pat, Stmt};

// --- Type representation ---

/// Internal type representation used during inference.
/// Separate from ast::TypeExpr, which is surface syntax.
#[derive(Debug, Clone, PartialEq)]
pub enum Type {
    Int,
    Float,
    String,
    Bool,
    Unit,
    /// Unification variable, solved during inference
    Var(u32),
    /// Function type: a -> b
    Arrow(Box<Type>, Box<Type>),
    /// Named type constructor with args: Option Int, Result String Int, List a
    Con(std::string::String, Vec<Type>),
}

impl std::fmt::Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::Int => write!(f, "Int"),
            Type::Float => write!(f, "Float"),
            Type::String => write!(f, "String"),
            Type::Bool => write!(f, "Bool"),
            Type::Unit => write!(f, "Unit"),
            Type::Var(id) => write!(f, "?{}", id),
            Type::Arrow(a, b) => match a.as_ref() {
                Type::Arrow(_, _) => write!(f, "({}) -> {}", a, b),
                _ => write!(f, "{} -> {}", a, b),
            },
            Type::Con(name, args) => {
                if args.is_empty() {
                    write!(f, "{}", name)
                } else {
                    write!(f, "{}", name)?;
                    for arg in args {
                        write!(f, " {}", arg)?;
                    }
                    Ok(())
                }
            }
        }
    }
}

// --- Substitution ---

/// Maps type variable IDs to their solved types.
#[derive(Debug, Default)]
pub struct Substitution {
    map: HashMap<u32, Type>,
}

impl Substitution {
    pub fn new() -> Self {
        Self::default()
    }

    /// Apply the substitution to a type, following chains of variables.
    pub fn apply(&self, ty: &Type) -> Type {
        match ty {
            Type::Var(id) => {
                if let Some(resolved) = self.map.get(id) {
                    self.apply(resolved)
                } else {
                    ty.clone()
                }
            }
            Type::Arrow(a, b) => Type::Arrow(Box::new(self.apply(a)), Box::new(self.apply(b))),
            Type::Con(name, args) => {
                Type::Con(name.clone(), args.iter().map(|a| self.apply(a)).collect())
            }
            _ => ty.clone(),
        }
    }

    /// Bind a type variable to a type, with occurs check.
    fn bind(&mut self, id: u32, ty: &Type) -> Result<(), TypeError> {
        if let Type::Var(other) = ty
            && *other == id
        {
            return Ok(());
        }

        if self.occurs(id, ty) {
            return Err(TypeError {
                message: format!("infinite type: ?{} occurs in {}", id, ty),
            });
        }
        self.map.insert(id, ty.clone());
        Ok(())
    }

    /// Check if a type variable occurs inside a type (prevents infinite types).
    fn occurs(&self, id: u32, ty: &Type) -> bool {
        match ty {
            Type::Var(other) => {
                if *other == id {
                    return true;
                }
                if let Some(resolved) = self.map.get(other) {
                    self.occurs(id, resolved)
                } else {
                    false
                }
            }
            Type::Arrow(a, b) => self.occurs(id, a) || self.occurs(id, b),
            Type::Con(_, args) => args.iter().any(|a| self.occurs(id, a)),
            _ => false,
        }
    }
}

// --- Type scheme (polymorphism) ---

/// A polymorphic type: forall [vars]. ty
/// e.g. `forall a. a -> a` for the identity function
#[derive(Debug, Clone)]
pub struct Scheme {
    pub forall: Vec<u32>,
    pub ty: Type,
}

// --- Type environment ---

/// Maps variable names to their type schemes.
#[derive(Debug, Clone, Default)]
pub struct TypeEnv {
    bindings: HashMap<std::string::String, Scheme>,
}

impl TypeEnv {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn insert(&mut self, name: std::string::String, scheme: Scheme) {
        self.bindings.insert(name, scheme);
    }

    pub fn get(&self, name: &str) -> Option<&Scheme> {
        self.bindings.get(name)
    }

    pub fn remove(&mut self, name: &str) {
        self.bindings.remove(name);
    }

    /// Free type variables in the environment (used for generalization).
    fn free_vars(&self, sub: &Substitution) -> Vec<u32> {
        let mut vars = Vec::new();
        for scheme in self.bindings.values() {
            free_vars_in_type(&sub.apply(&scheme.ty), &scheme.forall, &mut vars);
        }
        vars
    }
}

fn free_vars_in_type(ty: &Type, bound: &[u32], out: &mut Vec<u32>) {
    match ty {
        Type::Var(id) => {
            if !bound.contains(id) && !out.contains(id) {
                out.push(*id);
            }
        }
        Type::Arrow(a, b) => {
            free_vars_in_type(a, bound, out);
            free_vars_in_type(b, bound, out);
        }
        Type::Con(_, args) => {
            for arg in args {
                free_vars_in_type(arg, bound, out);
            }
        }
        _ => {}
    }
}

// --- Errors ---

#[derive(Debug, Clone)]
pub struct TypeError {
    pub message: std::string::String,
}

impl std::fmt::Display for TypeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.message)
    }
}

// --- Inference engine ---

pub struct Checker {
    next_var: u32,
    pub sub: Substitution,
    pub env: TypeEnv,
    /// Constructor types from type definitions: name -> (arity, type scheme)
    constructors: HashMap<std::string::String, Scheme>,
    /// Record definitions: record name -> vec of (field_name, field_type)
    records: HashMap<std::string::String, Vec<(std::string::String, Type)>>,
}

impl Checker {
    pub fn new() -> Self {
        let mut checker = Checker {
            next_var: 0,
            sub: Substitution::new(),
            env: TypeEnv::new(),
            constructors: HashMap::new(),
            records: HashMap::new(),
        };
        checker.register_builtins();
        checker
    }

    fn fresh_var(&mut self) -> Type {
        let id = self.next_var;
        self.next_var += 1;
        Type::Var(id)
    }

    fn register_builtins(&mut self) {
        // print : a -> Unit (polymorphic, accepts anything)
        let a = self.fresh_var();
        let a_id = match &a {
            Type::Var(id) => *id,
            _ => unreachable!(),
        };
        self.env.insert(
            "print".into(),
            Scheme {
                forall: vec![a_id],
                ty: Type::Arrow(Box::new(a), Box::new(Type::Unit)),
            },
        );

        // show : a -> String
        let a = self.fresh_var();
        let a_id = match &a {
            Type::Var(id) => *id,
            _ => unreachable!(),
        };
        self.env.insert(
            "show".into(),
            Scheme {
                forall: vec![a_id],
                ty: Type::Arrow(Box::new(a), Box::new(Type::String)),
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
                ty: Type::Bool,
            },
        );
        self.constructors.insert(
            "False".into(),
            Scheme {
                forall: vec![],
                ty: Type::Bool,
            },
        );
    }

    // --- Unification ---

    pub fn unify(&mut self, a: &Type, b: &Type) -> Result<(), TypeError> {
        let a = self.sub.apply(a);
        let b = self.sub.apply(b);

        match (&a, &b) {
            _ if a == b => Ok(()),

            (Type::Var(id), _) => self.sub.bind(*id, &b),
            (_, Type::Var(id)) => self.sub.bind(*id, &a),

            (Type::Arrow(a1, a2), Type::Arrow(b1, b2)) => {
                self.unify(a1, b1)?;
                self.unify(a2, b2)
            }

            (Type::Con(n1, args1), Type::Con(n2, args2))
                if n1 == n2 && args1.len() == args2.len() =>
            {
                for (a, b) in args1.iter().zip(args2.iter()) {
                    self.unify(a, b)?;
                }
                Ok(())
            }

            _ => Err(TypeError {
                message: format!("type mismatch: expected {}, got {}", a, b),
            }),
        }
    }

    // --- Instantiation & Generalization ---

    /// Replace forall'd variables with fresh type variables.
    fn instantiate(&mut self, scheme: &Scheme) -> Type {
        let mapping: HashMap<u32, Type> = scheme
            .forall
            .iter()
            .map(|&id| (id, self.fresh_var()))
            .collect();
        self.replace_vars(&scheme.ty, &mapping)
    }

    fn replace_vars(&self, ty: &Type, mapping: &HashMap<u32, Type>) -> Type {
        match ty {
            Type::Var(id) => mapping.get(id).cloned().unwrap_or_else(|| ty.clone()),
            Type::Arrow(a, b) => Type::Arrow(
                Box::new(self.replace_vars(a, mapping)),
                Box::new(self.replace_vars(b, mapping)),
            ),
            Type::Con(name, args) => Type::Con(
                name.clone(),
                args.iter().map(|a| self.replace_vars(a, mapping)).collect(),
            ),
            _ => ty.clone(),
        }
    }

    /// Generalize a type over variables not free in the environment.
    fn generalize(&self, ty: &Type) -> Scheme {
        let resolved = self.sub.apply(ty);
        let env_vars = self.env.free_vars(&self.sub);
        let mut forall = Vec::new();
        collect_free_vars(&resolved, &mut forall);
        forall.retain(|v| !env_vars.contains(v));
        Scheme {
            forall,
            ty: resolved,
        }
    }

    // --- Inference ---

    pub fn infer_expr(&mut self, expr: &Expr) -> Result<Type, TypeError> {
        match expr {
            Expr::Lit { value, .. } => Ok(match value {
                Lit::Int(_) => Type::Int,
                Lit::Float(_) => Type::Float,
                Lit::String(_) => Type::String,
                Lit::Bool(_) => Type::Bool,
                Lit::Unit => Type::Unit,
            }),

            Expr::Var { name, .. } => {
                if let Some(scheme) = self.env.get(name) {
                    let scheme = scheme.clone();
                    Ok(self.instantiate(&scheme))
                } else {
                    Err(TypeError {
                        message: format!("undefined variable: {}", name),
                    })
                }
            }

            Expr::Constructor { name, .. } => {
                if let Some(scheme) = self.constructors.get(name) {
                    let scheme = scheme.clone();
                    Ok(self.instantiate(&scheme))
                } else {
                    Err(TypeError {
                        message: format!("undefined constructor: {}", name),
                    })
                }
            }

            Expr::App { func, arg, .. } => {
                let func_ty = self.infer_expr(func)?;
                let arg_ty = self.infer_expr(arg)?;
                let ret_ty = self.fresh_var();
                self.unify(
                    &func_ty,
                    &Type::Arrow(Box::new(arg_ty), Box::new(ret_ty.clone())),
                )?;
                Ok(ret_ty)
            }

            Expr::BinOp {
                op, left, right, ..
            } => {
                let left_ty = self.infer_expr(left)?;
                let right_ty = self.infer_expr(right)?;
                match op {
                    BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Mod => {
                        // Numeric: both sides must match, result is same type
                        // Allows Int or Float (proper Num constraint comes with traits)
                        self.unify(&left_ty, &right_ty)?;
                        Ok(left_ty)
                    }
                    BinOp::Eq | BinOp::NotEq => {
                        self.unify(&left_ty, &right_ty)?;
                        Ok(Type::Bool)
                    }
                    BinOp::Lt | BinOp::Gt | BinOp::LtEq | BinOp::GtEq => {
                        self.unify(&left_ty, &right_ty)?;
                        Ok(Type::Bool)
                    }
                    BinOp::And | BinOp::Or => {
                        self.unify(&left_ty, &Type::Bool)?;
                        self.unify(&right_ty, &Type::Bool)?;
                        Ok(Type::Bool)
                    }
                    BinOp::Concat => {
                        self.unify(&left_ty, &Type::String)?;
                        self.unify(&right_ty, &Type::String)?;
                        Ok(Type::String)
                    }
                }
            }

            Expr::UnaryMinus { expr, .. } => {
                let ty = self.infer_expr(expr)?;
                Ok(ty)
            }

            Expr::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => {
                let cond_ty = self.infer_expr(cond)?;
                self.unify(&cond_ty, &Type::Bool)?;
                let then_ty = self.infer_expr(then_branch)?;
                let else_ty = self.infer_expr(else_branch)?;
                self.unify(&then_ty, &else_ty)?;
                Ok(then_ty)
            }

            Expr::Block { stmts, .. } => self.infer_block(stmts),

            Expr::Lambda { params, body, .. } => {
                // For now, handle single-arm lambdas with simple var patterns
                let mut param_types = Vec::new();
                for pat in params {
                    let ty = self.fresh_var();
                    self.bind_pattern(pat, &ty)?;
                    param_types.push(ty);
                }
                let body_ty = self.infer_expr(body)?;
                // Build curried arrow: a -> b -> c -> ret
                let mut result = body_ty;
                for param_ty in param_types.into_iter().rev() {
                    result = Type::Arrow(Box::new(param_ty), Box::new(result));
                }
                Ok(result)
            }

            Expr::Case {
                scrutinee, arms, ..
            } => {
                let scrut_ty = self.infer_expr(scrutinee)?;
                let result_ty = self.fresh_var();

                for arm in arms {
                    let saved_env = self.env.clone();

                    self.bind_pattern(&arm.pattern, &scrut_ty)?;

                    if let Some(guard) = &arm.guard {
                        let guard_ty = self.infer_expr(guard)?;
                        self.unify(&guard_ty, &Type::Bool)?;
                    }

                    let body_ty = self.infer_expr(&arm.body)?;
                    self.unify(&result_ty, &body_ty)?;

                    self.env = saved_env;
                }

                Ok(result_ty)
            }

            Expr::RecordCreate { name, fields, .. } => {
                let def = self.records.get(name).cloned().ok_or_else(|| TypeError {
                    message: format!("undefined record type: {}", name),
                })?;

                for (fname, fexpr) in fields {
                    let expected =
                        def.iter()
                            .find(|(n, _)| n == fname)
                            .ok_or_else(|| TypeError {
                                message: format!("unknown field '{}' on record {}", fname, name),
                            })?;
                    let actual = self.infer_expr(fexpr)?;
                    self.unify(&expected.1, &actual)?;
                }

                Ok(Type::Con(name.clone(), vec![]))
            }

            Expr::FieldAccess { expr, field, .. } => {
                let expr_ty = self.infer_expr(expr)?;
                let resolved = self.sub.apply(&expr_ty);

                match &resolved {
                    Type::Con(name, _) => {
                        let def = self.records.get(name).cloned().ok_or_else(|| TypeError {
                            message: format!("type {} is not a record", name),
                        })?;
                        let (_, field_ty) =
                            def.iter()
                                .find(|(n, _)| n == field)
                                .ok_or_else(|| TypeError {
                                    message: format!("no field '{}' on record {}", field, name),
                                })?;
                        Ok(field_ty.clone())
                    }
                    Type::Var(_) => {
                        // Type not yet resolved -- find records that have this field
                        let candidates: Vec<_> = self
                            .records
                            .iter()
                            .filter_map(|(rname, fields)| {
                                fields
                                    .iter()
                                    .find(|(n, _)| n == field)
                                    .map(|(_, ty)| (rname.clone(), ty.clone()))
                            })
                            .collect();
                        match candidates.len() {
                            1 => {
                                let (rname, field_ty) = &candidates[0];
                                self.unify(&resolved, &Type::Con(rname.clone(), vec![]))?;
                                Ok(field_ty.clone())
                            }
                            0 => Err(TypeError {
                                message: format!("no record has field '{}'", field),
                            }),
                            _ => Err(TypeError {
                                message: format!(
                                    "ambiguous field '{}': found in multiple records",
                                    field
                                ),
                            }),
                        }
                    }
                    _ => Err(TypeError {
                        message: format!("cannot access field '{}' on type {}", field, resolved),
                    }),
                }
            }

            Expr::RecordUpdate { record, fields, .. } => {
                let rec_ty = self.infer_expr(record)?;
                let mut resolved = self.sub.apply(&rec_ty);

                // If type is still a var, try to infer record from first updated field
                if matches!(&resolved, Type::Var(_))
                    && let Some((fname, _)) = fields.first()
                {
                    let candidates: Vec<_> = self
                        .records
                        .iter()
                        .filter(|(_, flds)| flds.iter().any(|(n, _)| n == fname))
                        .map(|(rname, _)| rname.clone())
                        .collect();
                    if candidates.len() == 1 {
                        self.unify(&resolved, &Type::Con(candidates[0].clone(), vec![]))?;
                        resolved = self.sub.apply(&rec_ty);
                    }
                }

                match &resolved {
                    Type::Con(name, _) => {
                        let def = self.records.get(name).cloned().ok_or_else(|| TypeError {
                            message: format!("type {} is not a record", name),
                        })?;
                        for (fname, fexpr) in fields {
                            let expected =
                                def.iter()
                                    .find(|(n, _)| n == fname)
                                    .ok_or_else(|| TypeError {
                                        message: format!(
                                            "unknown field '{}' on record {}",
                                            fname, name
                                        ),
                                    })?;
                            let actual = self.infer_expr(fexpr)?;
                            self.unify(&expected.1, &actual)?;
                        }
                        Ok(resolved.clone())
                    }
                    _ => Err(TypeError {
                        message: format!("cannot update non-record type {}", resolved),
                    }),
                }
            }

            // TODO: EffectCall, With, Resume
            _ => {
                let ty = self.fresh_var();
                Ok(ty) // placeholder: return unknown type
            }
        }
    }

    fn infer_block(&mut self, stmts: &[Stmt]) -> Result<Type, TypeError> {
        let mut last_ty = Type::Unit;
        for stmt in stmts {
            match stmt {
                Stmt::Let { name, value, .. } => {
                    let ty = self.infer_expr(value)?;
                    let scheme = self.generalize(&ty);
                    self.env.insert(name.clone(), scheme);
                    last_ty = Type::Unit;
                }
                Stmt::Assign { value, .. } => {
                    self.infer_expr(value)?;
                    last_ty = Type::Unit;
                }
                Stmt::Expr(expr) => {
                    last_ty = self.infer_expr(expr)?;
                }
            }
        }
        Ok(last_ty)
    }

    /// Bind a pattern to a type, adding variables to the environment.
    fn bind_pattern(&mut self, pat: &Pat, ty: &Type) -> Result<(), TypeError> {
        match pat {
            Pat::Wildcard { .. } => Ok(()),
            Pat::Var { name, .. } => {
                self.env.insert(
                    name.clone(),
                    Scheme {
                        forall: vec![],
                        ty: ty.clone(),
                    },
                );
                Ok(())
            }
            Pat::Lit { value, .. } => {
                let lit_ty = match value {
                    Lit::Int(_) => Type::Int,
                    Lit::Float(_) => Type::Float,
                    Lit::String(_) => Type::String,
                    Lit::Bool(_) => Type::Bool,
                    Lit::Unit => Type::Unit,
                };
                self.unify(ty, &lit_ty)
            }
            Pat::Constructor { name, args, .. } => {
                let ctor_scheme =
                    self.constructors
                        .get(name)
                        .cloned()
                        .ok_or_else(|| TypeError {
                            message: format!("undefined constructor in pattern: {}", name),
                        })?;
                let ctor_ty = self.instantiate(&ctor_scheme);
                // Peel off arrow types for each argument
                let mut current = ctor_ty;
                for arg_pat in args {
                    match current {
                        Type::Arrow(param_ty, ret_ty) => {
                            self.bind_pattern(arg_pat, &param_ty)?;
                            current = *ret_ty;
                        }
                        _ => {
                            return Err(TypeError {
                                message: format!(
                                    "constructor {} applied to too many arguments",
                                    name
                                ),
                            });
                        }
                    }
                }
                self.unify(ty, &current)
            }
            Pat::Record { name, fields, .. } => {
                let def = self.records.get(name).cloned().ok_or_else(|| TypeError {
                    message: format!("undefined record type in pattern: {}", name),
                })?;
                // Unify scrutinee with this record type
                self.unify(ty, &Type::Con(name.clone(), vec![]))?;

                for (fname, alias_pat) in fields {
                    let (_, field_ty) =
                        def.iter()
                            .find(|(n, _)| n == fname)
                            .ok_or_else(|| TypeError {
                                message: format!("unknown field '{}' on record {}", fname, name),
                            })?;
                    match alias_pat {
                        Some(pat) => self.bind_pattern(pat, field_ty)?,
                        // No alias: bind field name as variable
                        None => {
                            self.env.insert(
                                fname.clone(),
                                Scheme {
                                    forall: vec![],
                                    ty: field_ty.clone(),
                                },
                            );
                        }
                    }
                }
                Ok(())
            }
        }
    }

    // --- Top-level declarations ---

    pub fn check_program(&mut self, program: &[Decl]) -> Result<(), TypeError> {
        // First pass: register type definitions and record definitions
        for decl in program {
            match decl {
                Decl::TypeDef {
                    name,
                    type_params,
                    variants,
                    ..
                } => {
                    self.register_type_def(name, type_params, variants)?;
                }
                Decl::RecordDef { name, fields, .. } => {
                    self.register_record_def(name, fields)?;
                }
                _ => {}
            }
        }

        // Collect function annotations: name -> declared type
        let mut annotations: HashMap<std::string::String, Type> = HashMap::new();
        for decl in program {
            if let Decl::FunAnnotation {
                name,
                params,
                return_type,
                ..
            } = decl
            {
                let mut params_list: Vec<(String, u32)> = vec![];
                let mut fun_ty = self.convert_type_expr(return_type, &mut params_list);
                for (_, texpr) in params.iter().rev() {
                    let param_ty = self.convert_type_expr(texpr, &mut params_list);
                    fun_ty = Type::Arrow(Box::new(param_ty), Box::new(fun_ty));
                }
                annotations.insert(name.clone(), fun_ty);
            }
        }

        // Second pass: pre-bind all function names with fresh vars (enables mutual recursion)
        let mut fun_vars: HashMap<std::string::String, Type> = HashMap::new();
        for decl in program {
            if let Decl::FunBinding { name, .. } = decl
                && !fun_vars.contains_key(name)
            {
                let var = self.fresh_var();
                fun_vars.insert(name.clone(), var.clone());
                self.env.insert(
                    name.clone(),
                    Scheme {
                        forall: vec![],
                        ty: var,
                    },
                );
            }
        }

        // Third pass: group multi-clause function bindings, then check everything
        let mut i = 0;
        while i < program.len() {
            if let Decl::FunBinding { name, .. } = &program[i] {
                // Collect all consecutive clauses with the same name
                let name = name.clone();
                let start = i;
                while i < program.len() {
                    if let Decl::FunBinding { name: n, .. } = &program[i]
                        && *n == name
                    {
                        i += 1;
                        continue;
                    }
                    break;
                }
                let clauses: Vec<&Decl> = program[start..i].iter().collect();
                let fun_var = fun_vars[&name].clone();
                let annotation = annotations.get(&name).cloned();
                self.check_fun_clauses(&name, &clauses, &fun_var, annotation.as_ref())?;
            } else {
                self.check_decl(&program[i])?;
                i += 1;
            }
        }
        Ok(())
    }

    fn register_type_def(
        &mut self,
        name: &str,
        type_params: &[String],
        variants: &[ast::TypeConstructor],
    ) -> Result<(), TypeError> {
        // Create fresh type variables for the type parameters
        let mut param_vars: Vec<(String, u32)> = type_params
            .iter()
            .map(|p| {
                let var = self.next_var;
                self.next_var += 1;
                (p.clone(), var)
            })
            .collect();

        let result_type = Type::Con(
            name.into(),
            param_vars.iter().map(|(_, id)| Type::Var(*id)).collect(),
        );

        let forall: Vec<u32> = param_vars.iter().map(|(_, id)| *id).collect();

        for variant in variants {
            let ctor_ty = if variant.fields.is_empty() {
                result_type.clone()
            } else {
                // Build: field1 -> field2 -> ... -> ResultType
                let mut ty = result_type.clone();
                for field in variant.fields.iter().rev() {
                    let field_ty = self.convert_type_expr(field, &mut param_vars);
                    ty = Type::Arrow(Box::new(field_ty), Box::new(ty));
                }
                ty
            };

            self.constructors.insert(
                variant.name.clone(),
                Scheme {
                    forall: forall.clone(),
                    ty: ctor_ty,
                },
            );
        }

        Ok(())
    }

    fn register_record_def(
        &mut self,
        name: &str,
        fields: &[(String, ast::TypeExpr)],
    ) -> Result<(), TypeError> {
        let mut params: Vec<(String, u32)> = vec![];
        let field_types: Vec<(std::string::String, Type)> = fields
            .iter()
            .map(|(fname, texpr)| (fname.clone(), self.convert_type_expr(texpr, &mut params)))
            .collect();
        self.records.insert(name.into(), field_types);
        Ok(())
    }

    /// Convert a surface TypeExpr to our internal Type representation.
    fn convert_type_expr(
        &mut self,
        texpr: &ast::TypeExpr,
        params: &mut Vec<(String, u32)>,
    ) -> Type {
        match texpr {
            ast::TypeExpr::Named(name) => match name.as_str() {
                "Int" => Type::Int,
                "Float" => Type::Float,
                "String" => Type::String,
                "Bool" => Type::Bool,
                "Unit" => Type::Unit,
                _ => Type::Con(name.clone(), vec![]),
            },
            ast::TypeExpr::Var(name) => {
                if let Some((_, id)) = params.iter().find(|(n, _)| n == name) {
                    Type::Var(*id)
                } else {
                    // New type variable -- create fresh and remember for reuse
                    let id = self.next_var;
                    self.next_var += 1;
                    params.push((name.clone(), id));
                    Type::Var(id)
                }
            }
            ast::TypeExpr::App(func, arg) => {
                let func_ty = self.convert_type_expr(func, params);
                let arg_ty = self.convert_type_expr(arg, params);
                // Type application: push arg into Con's args list
                match func_ty {
                    Type::Con(name, mut args) => {
                        args.push(arg_ty);
                        Type::Con(name, args)
                    }
                    _ => {
                        // Shouldn't happen with well-formed type exprs
                        Type::Con("?".into(), vec![func_ty, arg_ty])
                    }
                }
            }
            ast::TypeExpr::Arrow(a, b) => {
                let a_ty = self.convert_type_expr(a, params);
                let b_ty = self.convert_type_expr(b, params);
                Type::Arrow(Box::new(a_ty), Box::new(b_ty))
            }
        }
    }

    fn check_decl(&mut self, decl: &Decl) -> Result<(), TypeError> {
        match decl {
            Decl::Let { name, value, .. } => {
                let ty = self.infer_expr(value)?;
                let scheme = self.generalize(&ty);
                self.env.insert(name.clone(), scheme);
                Ok(())
            }

            Decl::FunBinding { .. } => {
                // Multi-clause functions are handled in check_program
                Ok(())
            }

            // Type annotations, type defs (already registered), effects, handlers, traits, impls,
            // imports, modules -- skip for now
            _ => Ok(()),
        }
    }

    /// Check a group of function clauses that share the same name.
    /// Handles recursion (pre-binds name) and multi-clause pattern matching.
    fn check_fun_clauses(
        &mut self,
        name: &str,
        clauses: &[&Decl],
        fun_var: &Type,
        annotation: Option<&Type>,
    ) -> Result<(), TypeError> {
        // All clauses must have the same arity
        let arity = match clauses[0] {
            Decl::FunBinding { params, .. } => params.len(),
            _ => unreachable!(),
        };

        let result_ty = self.fresh_var();
        let param_types: Vec<Type> = (0..arity).map(|_| self.fresh_var()).collect();

        // If there's a type annotation, unify param/result types with it upfront
        // so annotation constraints guide inference (important for polymorphic recursion).
        // Also unify the pre-bound var so recursive calls see the correct type.
        if let Some(ann_ty) = annotation {
            let mut ann_current = ann_ty.clone();
            for param_ty in &param_types {
                match ann_current {
                    Type::Arrow(ann_param, ann_ret) => {
                        self.unify(param_ty, &ann_param)?;
                        ann_current = *ann_ret;
                    }
                    _ => break,
                }
            }
            self.unify(&result_ty, &ann_current)?;

            // Build the function type from annotation-constrained params and unify with pre-bound var
            let mut pre_ty = result_ty.clone();
            for param_ty in param_types.iter().rev() {
                pre_ty = Type::Arrow(Box::new(param_ty.clone()), Box::new(pre_ty));
            }
            self.unify(fun_var, &pre_ty)?;
        }

        for clause in clauses {
            let Decl::FunBinding {
                params,
                guard,
                body,
                ..
            } = clause
            else {
                unreachable!()
            };

            if params.len() != arity {
                return Err(TypeError {
                    message: format!(
                        "clause for '{}' has {} params, expected {}",
                        name,
                        params.len(),
                        arity
                    ),
                });
            }

            let saved_env = self.env.clone();

            for (pat, ty) in params.iter().zip(param_types.iter()) {
                self.bind_pattern(pat, ty)?;
            }

            if let Some(guard) = guard {
                let guard_ty = self.infer_expr(guard)?;
                self.unify(&guard_ty, &Type::Bool)?;
            }

            let body_ty = self.infer_expr(body)?;
            self.unify(&result_ty, &body_ty)?;

            self.env = saved_env;
        }

        // Build curried function type
        let mut fun_ty = result_ty;
        for param_ty in param_types.into_iter().rev() {
            fun_ty = Type::Arrow(Box::new(param_ty), Box::new(fun_ty));
        }

        // Unify with the pre-bound variable (resolves recursive uses)
        self.unify(fun_var, &fun_ty)?;

        // Check against type annotation if present
        if let Some(ann_ty) = annotation {
            self.unify(&fun_ty, ann_ty).map_err(|e| TypeError {
                message: format!("type annotation mismatch for '{}': {}", name, e.message),
            })?;
        }

        // Remove the function's own pre-bound entry before generalizing,
        // otherwise its type vars appear in env_vars and block generalization
        self.env.remove(name);
        let scheme = self.generalize(&fun_ty);
        self.env.insert(name.into(), scheme);
        Ok(())
    }
}

fn collect_free_vars(ty: &Type, out: &mut Vec<u32>) {
    match ty {
        Type::Var(id) => {
            if !out.contains(id) {
                out.push(*id);
            }
        }
        Type::Arrow(a, b) => {
            collect_free_vars(a, out);
            collect_free_vars(b, out);
        }
        Type::Con(_, args) => {
            for arg in args {
                collect_free_vars(arg, out);
            }
        }
        _ => {}
    }
}

// --- Tests ---

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lexer::Lexer;
    use crate::parser::Parser;

    fn check(src: &str) -> Result<Checker, TypeError> {
        let mut lexer = Lexer::new(src);
        let tokens = lexer.lex().expect("lex error");
        let mut parser = Parser::new(tokens);
        let program = parser.parse_program().expect("parse error");
        let mut checker = Checker::new();
        checker.check_program(&program)?;
        Ok(checker)
    }

    fn infer_expr_type(src: &str) -> Result<Type, TypeError> {
        // Wrap expression in a let binding so we can pull its type
        let wrapped = format!("let _result = {}", src);
        let checker = check(&wrapped)?;
        let scheme = checker.env.get("_result").expect("_result not in env");
        Ok(checker.sub.apply(&scheme.ty))
    }

    #[test]
    fn literal_int() {
        let ty = infer_expr_type("42").unwrap();
        assert_eq!(ty, Type::Int);
    }

    #[test]
    fn literal_float() {
        let ty = infer_expr_type("3.14").unwrap();
        assert_eq!(ty, Type::Float);
    }

    #[test]
    fn literal_string() {
        let ty = infer_expr_type("\"hello\"").unwrap();
        assert_eq!(ty, Type::String);
    }

    #[test]
    fn literal_bool() {
        let ty = infer_expr_type("True").unwrap();
        assert_eq!(ty, Type::Bool);
    }

    #[test]
    fn literal_unit() {
        let ty = infer_expr_type("()").unwrap();
        assert_eq!(ty, Type::Unit);
    }

    #[test]
    fn variable_lookup() {
        let checker = check("let x = 42\nlet y = x").unwrap();
        let ty = checker.sub.apply(&checker.env.get("y").unwrap().ty);
        assert_eq!(ty, Type::Int);
    }

    #[test]
    fn undefined_variable() {
        let result = check("let x = y");
        assert!(result.is_err());
    }

    #[test]
    fn binary_add() {
        let ty = infer_expr_type("1 + 2").unwrap();
        assert_eq!(ty, Type::Int);
    }

    #[test]
    fn binary_comparison() {
        let ty = infer_expr_type("1 < 2").unwrap();
        assert_eq!(ty, Type::Bool);
    }

    #[test]
    fn binary_concat() {
        let ty = infer_expr_type("\"a\" <> \"b\"").unwrap();
        assert_eq!(ty, Type::String);
    }

    #[test]
    fn if_expression() {
        let ty = infer_expr_type("if True then 1 else 2").unwrap();
        assert_eq!(ty, Type::Int);
    }

    #[test]
    fn if_branch_mismatch() {
        let result = infer_expr_type("if True then 1 else \"hello\"");
        assert!(result.is_err());
    }

    #[test]
    fn function_identity() {
        let checker = check("id x = x").unwrap();
        let scheme = checker.env.get("id").unwrap();
        let ty = checker.sub.apply(&scheme.ty);
        // Should be ?a -> ?a (polymorphic)
        match ty {
            Type::Arrow(a, b) => assert_eq!(a, b),
            _ => panic!("expected arrow type, got {}", ty),
        }
    }

    #[test]
    fn function_application() {
        let checker = check("id x = x\nlet y = id 42").unwrap();
        let ty = checker.sub.apply(&checker.env.get("y").unwrap().ty);
        assert_eq!(ty, Type::Int);
    }

    #[test]
    fn type_mismatch_in_addition() {
        let result = infer_expr_type("1 + \"hello\"");
        assert!(result.is_err());
    }

    #[test]
    fn lambda_simple() {
        let ty = infer_expr_type("fun x -> x + 1").unwrap();
        assert_eq!(ty, Type::Arrow(Box::new(Type::Int), Box::new(Type::Int)));
    }

    #[test]
    fn block_returns_last() {
        let ty = infer_expr_type("{\n  let x = 1\n  x + 2\n}").unwrap();
        assert_eq!(ty, Type::Int);
    }

    #[test]
    fn constructor_type() {
        let checker = check("type Maybe a {\n  Just(a)\n  Nothing\n}\nlet x = Just 42").unwrap();
        let ty = checker.sub.apply(&checker.env.get("x").unwrap().ty);
        assert_eq!(ty, Type::Con("Maybe".into(), vec![Type::Int]));
    }

    #[test]
    fn case_literal_patterns() {
        let ty = infer_expr_type("case 1 {\n  0 -> \"zero\"\n  _ -> \"other\"\n}").unwrap();
        assert_eq!(ty, Type::String);
    }

    #[test]
    fn case_constructor_patterns() {
        let checker =
            check("type Maybe a {\n  Just(a)\n  Nothing\n}\nlet x = case Just 42 {\n  Just(n) -> n + 1\n  Nothing -> 0\n}")
                .unwrap();
        let ty = checker.sub.apply(&checker.env.get("x").unwrap().ty);
        assert_eq!(ty, Type::Int);
    }

    #[test]
    fn case_branch_type_mismatch() {
        let result = check(
            "type Maybe a {\n  Just(a)\n  Nothing\n}\nlet x = case Just 42 {\n  Just(n) -> n\n  Nothing -> \"nope\"\n}",
        );
        assert!(result.is_err());
    }

    #[test]
    fn case_binds_pattern_vars() {
        let checker =
            check("type Maybe a {\n  Just(a)\n  Nothing\n}\nlet x = case Just \"hello\" {\n  Just(s) -> s <> \" world\"\n  Nothing -> \"default\"\n}")
                .unwrap();
        let ty = checker.sub.apply(&checker.env.get("x").unwrap().ty);
        assert_eq!(ty, Type::String);
    }

    #[test]
    fn case_with_guard() {
        let ty =
            infer_expr_type("case 5 {\n  x if x > 0 -> \"positive\"\n  _ -> \"non-positive\"\n}")
                .unwrap();
        assert_eq!(ty, Type::String);
    }

    #[test]
    fn case_pattern_vars_dont_leak() {
        let result = check(
            "type Maybe a {\n  Just(a)\n  Nothing\n}\nlet x = case Just 42 {\n  Just(n) -> n\n  Nothing -> n\n}",
        );
        assert!(result.is_err());
    }

    #[test]
    fn constructor_no_args() {
        let checker = check("type Maybe a {\n  Just(a)\n  Nothing\n}\nlet x = Nothing").unwrap();
        let ty = checker.sub.apply(&checker.env.get("x").unwrap().ty);
        match ty {
            Type::Con(name, args) => {
                assert_eq!(name, "Maybe");
                assert_eq!(args.len(), 1);
                // The type param is unresolved -- it's a free variable
                assert!(matches!(args[0], Type::Var(_)));
            }
            _ => panic!("expected Con, got {}", ty),
        }
    }

    #[test]
    fn recursive_function() {
        let checker = check("factorial n = if n == 0 then 1 else n * factorial (n - 1)").unwrap();
        let scheme = checker.env.get("factorial").unwrap();
        let ty = checker.sub.apply(&scheme.ty);
        assert_eq!(ty, Type::Arrow(Box::new(Type::Int), Box::new(Type::Int)));
    }

    #[test]
    fn multi_clause_with_guards() {
        let checker = check("abs n | n < 0 = 0 - n\nabs n = n").unwrap();
        let scheme = checker.env.get("abs").unwrap();
        let ty = checker.sub.apply(&scheme.ty);
        assert_eq!(ty, Type::Arrow(Box::new(Type::Int), Box::new(Type::Int)));
    }

    #[test]
    fn multi_clause_literal_patterns() {
        let checker = check("fib 0 = 0\nfib 1 = 1\nfib n = fib (n - 1) + fib (n - 2)").unwrap();
        let scheme = checker.env.get("fib").unwrap();
        let ty = checker.sub.apply(&scheme.ty);
        assert_eq!(ty, Type::Arrow(Box::new(Type::Int), Box::new(Type::Int)));
    }

    #[test]
    fn mutual_recursion() {
        let checker = check("is_even n = if n == 0 then True else is_odd (n - 1)\nis_odd n = if n == 0 then False else is_even (n - 1)").unwrap();
        let even_ty = checker.sub.apply(&checker.env.get("is_even").unwrap().ty);
        assert_eq!(
            even_ty,
            Type::Arrow(Box::new(Type::Int), Box::new(Type::Bool))
        );
        let odd_ty = checker.sub.apply(&checker.env.get("is_odd").unwrap().ty);
        assert_eq!(
            odd_ty,
            Type::Arrow(Box::new(Type::Int), Box::new(Type::Bool))
        );
    }

    #[test]
    fn list_cons_expression() {
        let checker = check("let xs = 1 :: 2 :: Nil").unwrap();
        let ty = checker.sub.apply(&checker.env.get("xs").unwrap().ty);
        assert_eq!(ty, Type::Con("List".into(), vec![Type::Int]));
    }

    #[test]
    fn record_create() {
        let checker =
            check("record Point { x: Int, y: Int }\nlet p = Point { x: 3, y: 4 }").unwrap();
        let ty = checker.sub.apply(&checker.env.get("p").unwrap().ty);
        assert_eq!(ty, Type::Con("Point".into(), vec![]));
    }

    #[test]
    fn record_field_access() {
        let checker =
            check("record Point { x: Int, y: Int }\nlet p = Point { x: 3, y: 4 }\nlet a = p.x")
                .unwrap();
        let ty = checker.sub.apply(&checker.env.get("a").unwrap().ty);
        assert_eq!(ty, Type::Int);
    }

    #[test]
    fn record_field_type_mismatch() {
        let result = check("record Point { x: Int, y: Int }\nlet p = Point { x: \"bad\", y: 4 }");
        assert!(result.is_err());
    }

    #[test]
    fn record_unknown_field() {
        let result = check("record Point { x: Int, y: Int }\nlet p = Point { x: 1, z: 2 }");
        assert!(result.is_err());
    }

    #[test]
    fn record_update() {
        let checker = check(
            "record Point { x: Int, y: Int }\nlet p = Point { x: 3, y: 4 }\nlet q = { p | x: 10 }",
        )
        .unwrap();
        let ty = checker.sub.apply(&checker.env.get("q").unwrap().ty);
        assert_eq!(ty, Type::Con("Point".into(), vec![]));
    }

    #[test]
    fn record_update_type_mismatch() {
        let result = check(
            "record Point { x: Int, y: Int }\nlet p = Point { x: 3, y: 4 }\nlet q = { p | x: \"bad\" }",
        );
        assert!(result.is_err());
    }

    #[test]
    fn record_pattern() {
        let checker =
            check("record Point { x: Int, y: Int }\nget_x p = case p {\n  Point { x, y } -> x\n}")
                .unwrap();
        let ty = checker.sub.apply(&checker.env.get("get_x").unwrap().ty);
        assert_eq!(
            ty,
            Type::Arrow(
                Box::new(Type::Con("Point".into(), vec![])),
                Box::new(Type::Int)
            )
        );
    }

    #[test]
    fn record_pattern_with_alias() {
        let checker = check(
            "record User { name: String, age: Int }\nget_name u = case u {\n  User { name: n, age } -> n\n}",
        )
        .unwrap();
        let ty = checker.sub.apply(&checker.env.get("get_name").unwrap().ty);
        assert_eq!(
            ty,
            Type::Arrow(
                Box::new(Type::Con("User".into(), vec![])),
                Box::new(Type::String)
            )
        );
    }

    #[test]
    fn annotation_correct() {
        let checker = check(
            "fun fib (n: Int) -> Int\nfib 0 = 0\nfib 1 = 1\nfib n = fib (n - 1) + fib (n - 2)",
        )
        .unwrap();
        let ty = checker.sub.apply(&checker.env.get("fib").unwrap().ty);
        assert_eq!(ty, Type::Arrow(Box::new(Type::Int), Box::new(Type::Int)));
    }

    #[test]
    fn annotation_mismatch() {
        let result = check("fun add (a: Int) (b: Int) -> String\nadd a b = a + b");
        assert!(result.is_err());
    }

    #[test]
    fn annotation_multi_param() {
        let checker = check("fun add (a: Int) (b: Int) -> Int\nadd a b = a + b").unwrap();
        let ty = checker.sub.apply(&checker.env.get("add").unwrap().ty);
        assert_eq!(
            ty,
            Type::Arrow(
                Box::new(Type::Int),
                Box::new(Type::Arrow(Box::new(Type::Int), Box::new(Type::Int)))
            )
        );
    }

    #[test]
    fn annotation_constrains_polymorphism() {
        // id without annotation is polymorphic; with annotation it's constrained to Int -> Int
        let checker = check("fun myid (x: Int) -> Int\nmyid x = x").unwrap();
        let ty = checker.sub.apply(&checker.env.get("myid").unwrap().ty);
        assert_eq!(ty, Type::Arrow(Box::new(Type::Int), Box::new(Type::Int)));
    }

    #[test]
    fn annotation_polymorphic() {
        // fun id (x: a) -> a should work with the polymorphic identity
        let checker = check("fun id (x: a) -> a\nid x = x").unwrap();
        let scheme = checker.env.get("id").unwrap();
        let ty = checker.sub.apply(&scheme.ty);
        match ty {
            Type::Arrow(a, b) => assert_eq!(a, b),
            _ => panic!("expected arrow, got {}", ty),
        }
    }

    #[test]
    fn pipe_operator() {
        let checker = check("let x = 42 |> show").unwrap();
        let ty = checker.sub.apply(&checker.env.get("x").unwrap().ty);
        assert_eq!(ty, Type::String);
    }
}
