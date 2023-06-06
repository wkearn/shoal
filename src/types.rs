//! Type inference for shoal

use crate::error::Error;
use crate::parser::Expr;

use std::collections::{HashMap, HashSet};

// TODO: additional numeric types
/// The set of valid types for a shoal expression
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    Boolean,
    Integer,
    Float32,
    Float64,
    TypeVar(Box<str>, HashSet<Box<str>>),
    Function(Box<Type>, Box<Type>),
    BinaryFunction(Box<Type>, Box<Type>, Box<Type>),
    Array(Box<Type>),
    Pair(Box<Type>, Box<Type>),
}

impl std::fmt::Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        match self {
            Self::Boolean => write!(f, "Boolean"),
            Self::Integer => write!(f, "Integer"),
            Self::Float32 => write!(f, "Float32"),
            Self::Float64 => write!(f, "Float64"),
            Self::TypeVar(s, ops) => write!(
                f,
                "{s}_{{{}}}",
                ops.iter().cloned().collect::<Vec<Box<str>>>().join(","),
            ),
            Self::Function(arg, body) => write!(f, "{arg} -> {body}"),
            Self::BinaryFunction(arg0, arg1, body) => write!(f, "{arg0} x {arg1} -> {body}"),
            Self::Array(body) => write!(f, "[{body}]"),
            Self::Pair(t1, t2) => write!(f, "({t1},{t2})"),
        }
    }
}

impl Type {
    /// Check whether a type variable appears in another type constructor
    fn occurs_check(&self, other: &Type) -> bool {
        if let Type::TypeVar(s, _) = self {
            match other {
                Type::Function(arg, body) => self.occurs_check(arg) || self.occurs_check(body),
                Type::BinaryFunction(arg0, arg1, body) => {
                    self.occurs_check(arg0) || self.occurs_check(arg1) || self.occurs_check(body)
                }
                Type::Array(body) => self.occurs_check(body),
                Type::Pair(t1, t2) => self.occurs_check(t1) || self.occurs_check(t2),
                Type::TypeVar(t, _) => s == t,
                _ => false,
            }
        } else {
            false
        }
    }

    fn free_vars(&self) -> HashMap<Box<str>, HashSet<Box<str>>> {
        match self {
            Type::Boolean => HashMap::new(),
            Type::Integer => HashMap::new(),
            Type::Float32 => HashMap::new(),
            Type::Float64 => HashMap::new(),
            Type::TypeVar(s, ops) => {
                let mut fvs = HashMap::new();
                fvs.insert(s.clone(), ops.clone());
                fvs
            }
            Type::Array(body) => body.free_vars(),
            Type::Pair(t1, t2) => {
                let mut u = t1.free_vars();
                let v = t2.free_vars();
                u.extend(v);
                u
            }
            Type::Function(arg, body) => {
                let mut u = arg.free_vars();
                let v = body.free_vars();
                u.extend(v);
                u
            }
            Type::BinaryFunction(arg0, arg1, body) => {
                let mut u = arg0.free_vars();
                let v = arg1.free_vars();
                let w = body.free_vars();
                u.extend(v);
                u.extend(w);
                u
            }
        }
    }

    fn generalize(self, env: &TypeEnv) -> TypeScheme {
        let fvs = self.free_vars();
        let evs = env.free_vars();
        let mut qts = Vec::new();

        for (k, v) in fvs {
            if !evs.contains_key(&k) {
                qts.push(Type::TypeVar(k.clone(), v.clone()))
            }
        }
        TypeScheme::QuantifiedType(qts, self)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
/// A type scheme universally quantifies Types
pub enum TypeScheme {
    PlainType(Type),
    QuantifiedType(Vec<Type>, Type),
}

impl std::fmt::Display for TypeScheme {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        match self {
            Self::PlainType(t) => write!(f, "{t}"),
            Self::QuantifiedType(vars, t) => write!(
                f,
                "∀{} . {t}",
                vars.iter()
                    .map(|x| x.to_string())
                    .collect::<Vec<String>>()
                    .join(" "),
            ),
        }
    }
}

impl TypeScheme {
    fn free_vars(&self) -> HashMap<Box<str>, HashSet<Box<str>>> {
        match self {
            TypeScheme::PlainType(t) => t.free_vars(),
            TypeScheme::QuantifiedType(fvs, t) => {
                let mut tvs = t.free_vars();
                let qts: HashMap<Box<str>, HashSet<Box<str>>> = fvs
                    .iter()
                    .cloned()
                    .filter_map(|t| match t {
                        Type::TypeVar(u, ops) => Some((u, ops)),
                        _ => None,
                    })
                    .collect();

                for k in qts.keys() {
                    tvs.remove(k);
                }
                tvs
            }
        }
    }
}

#[derive(Debug, Default)]
pub struct TypeEnv(HashMap<Box<str>, TypeScheme>);

impl TypeEnv {
    pub fn new() -> Self {
        Self::default()
    }

    fn free_vars(&self) -> HashMap<Box<str>, HashSet<Box<str>>> {
        let mut fvs = HashMap::new();
        for t in self.0.values() {
            fvs.extend(t.free_vars().into_iter());
        }
        fvs
    }

    pub fn insert(&mut self, k: Box<str>, v: TypeScheme) -> Option<TypeScheme> {
        self.0.insert(k, v)
    }
}

/// A type substitution maps type variables to type schemes
#[derive(Debug, Default)]
pub struct TypeSubstitution {
    fresh_vars: u32,
    substitution: HashMap<Box<str>, Type>,
    overloads: HashMap<Box<str>, Vec<Box<str>>>,
}

impl TypeSubstitution {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn clear(&mut self) {
        self.substitution.clear();

        // The standard library uses different type variables,
        // so resetting fresh_vars should work.
        self.fresh_vars = 0;
    }
    /// Generate a fresh type variable with no overloading constraints
    pub fn genvar(&mut self) -> Type {
        self.genvar_with_ops(None)
    }

    /// Generate a fresh type variable with a set of overloading constraints
    pub fn genvar_with_ops<I>(&mut self, ops: I) -> Type
    where
        I: IntoIterator<Item = Box<str>>,
    {
        self.fresh_vars += 1;
        let s = format!("?X{}", self.fresh_vars);

        let ops_hs = ops.into_iter().collect();
        Type::TypeVar(s.into(), ops_hs)
    }

    pub fn insert_overload(&mut self, k: Box<str>, v: Vec<Box<str>>) -> Option<Vec<Box<str>>> {
        self.overloads.insert(k, v)
    }

    /// Apply the type substitution to a Type
    fn get(&self, t: &Type) -> Type {
        match t {
            // Primitive types return the same type
            Type::Boolean => Type::Boolean,
            Type::Integer => Type::Integer,
            Type::Float32 => Type::Float32,
            Type::Float64 => Type::Float64,
            Type::Function(arg, body) => {
                let at = self.get(arg);
                let ft = self.get(body);
                Type::Function(Box::new(at), Box::new(ft))
            }
            Type::BinaryFunction(arg0, arg1, body) => {
                let at0 = self.get(arg0);
                let at1 = self.get(arg1);
                let ft = self.get(body);
                Type::BinaryFunction(Box::new(at0), Box::new(at1), Box::new(ft))
            }
            Type::Array(body) => Type::Array(Box::new(self.get(body))),
            Type::Pair(t1, t2) => {
                let at1 = self.get(t1);
                let at2 = self.get(t2);
                Type::Pair(Box::new(at1), Box::new(at2))
            }
            Type::TypeVar(s, _) => match self.substitution.get(s) {
                Some(u) => self.get(u),
                //Some(bound) => bound.clone(),
                None => t.clone(),
            },
        }
    }

    fn is_valid_overloading(&self, xs: &HashSet<Box<str>>, t: &Type) -> bool {
        match t {
            Type::TypeVar(_, _) => false,
            Type::Function(_, _) => xs.is_empty(),
            Type::BinaryFunction(_, _, _) => xs.is_empty(),
            Type::Pair(_, _) => xs.is_empty(),
            Type::Array(_) => xs.is_empty(),
            Type::Boolean => {
                for x in xs.iter() {
                    match self.overloads.get(x) {
                        Some(ts) => {
                            if !ts.contains(&"Boolean".into()) {
                                return false;
                            }
                        }
                        None => return false,
                    }
                }
                return true;
            }
            Type::Integer => {
                for x in xs.iter() {
                    match self.overloads.get(x) {
                        Some(ts) => {
                            if !ts.contains(&"Integer".into()) {
                                return false;
                            }
                        }
                        None => return false,
                    }
                }
                return true;
            }
            Type::Float32 => {
                for x in xs.iter() {
                    match self.overloads.get(x) {
                        Some(ts) => {
                            if !ts.contains(&"Float64".into()) {
                                return false;
                            }
                        }
                        None => return false,
                    }
                }
                return true;
            }
            Type::Float64 => {
                for x in xs.iter() {
                    match self.overloads.get(x) {
                        Some(ts) => {
                            if !ts.contains(&"Float64".into()) {
                                return false;
                            }
                        }
                        None => return false,
                    }
                }
                return true;
            }
        }
    }

    fn cs(&mut self, xs: &HashSet<Box<str>>, right: &Type) -> Result<(), Error> {
        match right {
            Type::TypeVar(alpha, ops) => {
                let beta = self.genvar_with_ops(ops.union(xs).cloned());
                self.substitution.insert(alpha.clone(), beta);
                Ok(())
            }
            _ => {
                if self.is_valid_overloading(xs, right) {
                    Ok(())
                } else {
                    Err(Error::TypeError(format!(
                        "Invalid overloading of {{{}}} with {right}",
                        xs.iter().cloned().collect::<Vec<Box<str>>>().join(",")
                    )))
                }
            }
        }
    }

    /// Unify the left and right types in the given substitution
    fn unify(&mut self, left: &Type, right: &Type) -> Result<(), Error> {
        match left {
            Type::Boolean => match right {
                Type::Boolean => Ok(()),
                Type::TypeVar(_, _) => self.unify(right, left),
                _ => Err(Error::TypeError(format!("{left} != {right}"))),
            },
            Type::Integer => match right {
                Type::Integer => Ok(()),
                Type::TypeVar(_, _) => self.unify(right, left),
                _ => Err(Error::TypeError(format!("{left} != {right}"))),
            },
            Type::Float32 => match right {
                Type::Float32 => Ok(()),
                Type::TypeVar(_, _) => self.unify(right, left),
                _ => Err(Error::TypeError(format!("{left} != {right}"))),
            },
            Type::Float64 => match right {
                Type::Float64 => Ok(()),
                Type::TypeVar(_, _) => self.unify(right, left),
                _ => Err(Error::TypeError(format!("{left} != {right}"))),
            },
            Type::Array(body0) => match right {
                Type::TypeVar(_, _) => self.unify(right, left),
                Type::Array(body1) => self.unify(body0, body1),
                _ => Err(Error::TypeError(format!("{left} != {right}"))),
            },
            Type::Pair(t1, t2) => match right {
                Type::TypeVar(_, _) => self.unify(right, left),
                Type::Pair(u1, u2) => self.unify(t1, u1).and_then(|_| self.unify(t2, u2)),
                _ => Err(Error::TypeError(format!("{left} != {right}"))),
            },
            Type::Function(arg0, body0) => match right {
                Type::TypeVar(_, _) => self.unify(right, left),
                Type::Function(arg1, body1) => self
                    .unify(arg0, arg1)
                    .and_then(|_| self.unify(body0, body1)),
                _ => Err(Error::TypeError(format!("{left} != {right}"))),
            },
            Type::BinaryFunction(arg00, arg01, body0) => match right {
                Type::TypeVar(_, _) => self.unify(right, left),
                Type::BinaryFunction(arg10, arg11, body1) => self
                    .unify(arg00, arg10)
                    .and_then(|_| self.unify(arg01, arg11))
                    .and_then(|_| self.unify(body0, body1)),
                _ => Err(Error::TypeError(format!("{left} != {right}"))),
            },
            Type::TypeVar(x, ops) => {
                if left == right {
                    Ok(())
                } else if left.occurs_check(right) {
                    Err(Error::TypeError(format!(
                        "Recursive type found: {left} == {right}"
                    )))
                } else {
                    match self.substitution.get(x) {
                        Some(bound) => {
                            // If the left variable is already in the substitution,
                            // unify its substitution with the right variable
                            // Can we somehow avoid cloning left here?
                            self.unify(&bound.clone(), right)
                        }
                        None => {
                            // Substitute the right variable to make sure that it is reduced as far as possible
                            let new_right = self.get(right);
                            self.cs(ops, &new_right)?;
                            self.substitution.insert(x.clone(), new_right);
                            Ok(())
                        }
                    }
                }
            }
        }
    }
    pub fn reconstruct<T>(&mut self, expr: &Expr<T>, env: &TypeEnv) -> Result<Type, Error> {
        match expr {
            Expr::BooleanLiteral(_, _) => Ok(Type::Boolean),
            Expr::IntegerLiteral(_, _) => Ok(Type::Integer),
            Expr::FloatLiteral(_, _) => {
                // TODO: Literal overloading for Float64/Float32
                Ok(Type::Float64)
            }
            Expr::Identifier(_, s) => {
                let x = env
                    .0
                    .get(s)
                    .ok_or(Error::UndefinedVariableError(format!("{s}")))?;

                match x {
                    TypeScheme::PlainType(t) => Ok(t.clone()),
                    TypeScheme::QuantifiedType(vs, t) => {
                        let mut local_sub = TypeSubstitution::new();
                        for v in vs {
                            // TODO: instantiate TypeVars with appropriate ops for each v in vs
                            // QuantifiedType needs to hang on to the ops each v in vs,
                            // but right now it hangs on to just the name
                            match v {
                                Type::TypeVar(u, ops) => {
                                    local_sub
                                        .substitution
                                        .insert(u.clone(), self.genvar_with_ops(ops.clone()));
                                }
                                _ => {}
                            }
                        }
                        let tt = local_sub.get(t);
                        Ok(tt)
                    }
                }
            }
            Expr::Lambda(_, arg, body) => {
                // Extend the local environment
                let (arg_type, body_type) = {
                    let mut local_env = TypeEnv::new();
                    local_env
                        .0
                        .extend(env.0.iter().map(|(k, v)| (k.clone(), v.clone())));
                    let arg_type = self.genvar();
                    local_env
                        .0
                        .insert(arg.clone(), TypeScheme::PlainType(arg_type));

                    let body_type = self.reconstruct(body, &local_env)?;

                    // Since we destroy the local environment as soon as we finish reconstructing it,
                    // we can get the generated variable back by removing it from the HashMap.
                    let Some(TypeScheme::PlainType(arg_type)) = local_env.0.remove(arg) else {unreachable!()};
                    (arg_type, body_type)
                };

                let new_arg = self.get(&arg_type);
                let new_body = self.get(&body_type);

                Ok(Type::Function(Box::new(new_arg), Box::new(new_body)))
            }
            Expr::BinLambda(_, arg0, arg1, body) => {
                // Extend the local environment
                let (arg0_type, arg1_type, body_type) = {
                    let mut local_env = TypeEnv::new();
                    local_env
                        .0
                        .extend(env.0.iter().map(|(k, v)| (k.clone(), v.clone())));
                    let arg0_type = self.genvar();
                    let arg1_type = self.genvar();
                    local_env
                        .0
                        .insert(arg0.clone(), TypeScheme::PlainType(arg0_type));
                    local_env
                        .0
                        .insert(arg1.clone(), TypeScheme::PlainType(arg1_type));

                    let body_type = self.reconstruct(body, &local_env)?;

                    // Since we destroy the local environment as soon as we finish reconstructing it,
                    // we can get the generated variable back by removing it from the HashMap.
                    let Some(TypeScheme::PlainType(arg0_type)) = local_env.0.remove(arg0) else {unreachable!()};
                    let Some(TypeScheme::PlainType(arg1_type)) = local_env.0.remove(arg1) else {unreachable!()};
                    (arg0_type, arg1_type, body_type)
                };

                let new_arg0 = self.get(&arg0_type);
                let new_arg1 = self.get(&arg1_type);
                let new_body = self.get(&body_type);

                Ok(Type::BinaryFunction(
                    Box::new(new_arg0),
                    Box::new(new_arg1),
                    Box::new(new_body),
                ))
            }
            Expr::Let(_, arg, def, body) => {
                // Reconstruct the principal type of def
                let t1 = self.reconstruct(def, env)?;
                let t1 = self.get(&t1);

                // Generalize over the free variables in t1
                let t1 = t1.generalize(env);

                // Extend environment with arg -> t1
                let body_type = {
                    let mut local_env = TypeEnv::new();
                    local_env
                        .0
                        .extend(env.0.iter().map(|(k, v)| (k.clone(), v.clone())));
                    local_env.0.insert(arg.clone(), t1);

                    self.reconstruct(body, &local_env)?
                };

                Ok(self.get(&body_type))
            }
            Expr::App(_, fun, arg) => {
                // (f:(a -> b) arg: a):b
                let ft = self.reconstruct(fun, env)?;
                let at = self.reconstruct(arg, env)?;

                let rt = self.genvar();

                let tt = Type::Function(Box::new(at), Box::new(rt.clone()));

                self.unify(&ft, &tt)?;

                Ok(self.get(&rt))
            }
            Expr::BinApp(_, fun, arg0, arg1) => {
                let ft = self.reconstruct(fun, env)?;
                let at0 = self.reconstruct(arg0, env)?;
                let at1 = self.reconstruct(arg1, env)?;

                let rt = self.genvar();

                let tt = Type::BinaryFunction(Box::new(at0), Box::new(at1), Box::new(rt.clone()));

                self.unify(&ft, &tt)?;

                Ok(self.get(&rt))
            }
            Expr::If(_, pred, conseq, alt) => {
                // Predicate must be a Boolean
                let pt = self.reconstruct(pred, env)?;
                self.unify(&pt, &Type::Boolean)?;

                // Consequent and alternative must have the same type
                let ct = self.reconstruct(conseq, env)?;
                let at = self.reconstruct(alt, env)?;
                self.unify(&ct, &at)?;

                // Does it matter whether we return ct or at?
                Ok(self.get(&at))
            }
            Expr::Map(_, fun, arg) => {
                // map: ∀a b . (a -> b) -> [a] -> [b]
                let ft = self.reconstruct(fun, env)?;
                let at = self.reconstruct(arg, env)?;

                // at == [et]
                let et = self.genvar();
                self.unify(&at, &Type::Array(Box::new(et.clone())))?;

                // ft == el_type -> rt
                let rt = self.genvar();
                let tt = Type::Function(Box::new(et), Box::new(rt.clone()));
                self.unify(&ft, &tt)?;

                Ok(Type::Array(Box::new(self.get(&rt))))
            }
            Expr::Reduce(_, fun, init, arg) => {
                // reduce: ∀ a b . (b x a -> b) -> b -> [a] -> b

                let ft = self.reconstruct(fun, env)?;
                let it = self.reconstruct(init, env)?;
                let at = self.reconstruct(arg, env)?;

                // at == [et]
                let et = self.genvar();
                self.unify(&at, &Type::Array(Box::new(et.clone())))?;

                let rt = self.genvar();
                let tt =
                    Type::BinaryFunction(Box::new(rt.clone()), Box::new(et), Box::new(rt.clone()));

                // ft == rt x et -> rt
                self.unify(&ft, &tt)?;
                // it == rt
                self.unify(&it, &rt)?;

                Ok(self.get(&rt))
            }
            Expr::Scan(_, fun, init, arg) => {
                // scan: ∀ a b . (b x a -> b) -> b -> [a] -> b

                let ft = self.reconstruct(fun, env)?;
                let it = self.reconstruct(init, env)?;
                let at = self.reconstruct(arg, env)?;

                let et = self.genvar();

                self.unify(&at, &Type::Array(Box::new(et.clone())))?;

                let rt = self.genvar();
                let tt =
                    Type::BinaryFunction(Box::new(rt.clone()), Box::new(et), Box::new(rt.clone()));

                // ft == rt x et -> rt
                self.unify(&ft, &tt)?;
                // it == rt
                self.unify(&it, &rt)?;

                Ok(Type::Array(Box::new(self.get(&rt))))
            }
            Expr::Iota(_, n) => {
                let nt = self.reconstruct(n, env)?;
                self.unify(&nt, &Type::Integer)?;

                Ok(Type::Array(Box::new(Type::Integer)))
            }
            Expr::Pair(_, e1, e2) => {
                let t1 = self.reconstruct(e1, env)?;
                let t2 = self.reconstruct(e2, env)?;

                let tt = Type::Pair(Box::new(t1.clone()), Box::new(t2.clone()));

                Ok(tt)
            }
            Expr::Fst(_, p) => {
                let pt = self.reconstruct(p, env)?;

                let rt1 = self.genvar();
                let rt2 = self.genvar();
                let tt = Type::Pair(Box::new(rt1.clone()), Box::new(rt2));

                self.unify(&pt, &tt)?;
                Ok(self.get(&rt1))
            }
            Expr::Snd(_, p) => {
                let pt = self.reconstruct(p, env)?;

                let rt1 = self.genvar();
                let rt2 = self.genvar();
                let tt = Type::Pair(Box::new(rt1), Box::new(rt2.clone()));

                self.unify(&pt, &tt)?;
                Ok(self.get(&rt2))
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    use crate::parser::sexpr::parser::SExpr;
    use crate::parser::Expr;

    #[test]
    fn test1() {
        let expr = Expr::parse(
            &"(let ((f (lambda (x) x))) (f 1.0))"
                .parse::<SExpr>()
                .unwrap(),
        )
        .unwrap();

        let mut sub = TypeSubstitution::new();
        let env = TypeEnv::new();
        let t = sub.reconstruct(&expr, &env).unwrap();

        assert_eq!(t, Type::Float64);

        //
        let expr =
            Expr::parse(&"(let ((f (lambda (x) x))) (f 1))".parse::<SExpr>().unwrap()).unwrap();

        let mut sub = TypeSubstitution::new();
        let env = TypeEnv::new();
        let t = sub.reconstruct(&expr, &env).unwrap();

        assert_eq!(t, Type::Integer);

        //
        let expr = Expr::parse(
            &"(let ((f (lambda (x) x))) (f true))"
                .parse::<SExpr>()
                .unwrap(),
        )
        .unwrap();

        let mut sub = TypeSubstitution::new();
        let env = TypeEnv::new();
        let t = sub.reconstruct(&expr, &env).unwrap();

        assert_eq!(t, Type::Boolean);
    }

    #[test]
    fn test2() {
        let expr = Expr::parse(&"(if true 1.0 2.0)".parse::<SExpr>().unwrap()).unwrap();

        let mut sub = TypeSubstitution::new();
        let env = TypeEnv::new();
        let t = sub.reconstruct(&expr, &env).unwrap();

        assert_eq!(t, Type::Float64);

        //
        let expr = Expr::parse(&"(if true 1 2)".parse::<SExpr>().unwrap()).unwrap();

        let mut sub = TypeSubstitution::new();
        let env = TypeEnv::new();
        let t = sub.reconstruct(&expr, &env).unwrap();

        assert_eq!(t, Type::Integer);

        //
        let expr = Expr::parse(&"(if true false true)".parse::<SExpr>().unwrap()).unwrap();

        let mut sub = TypeSubstitution::new();
        let env = TypeEnv::new();
        let t = sub.reconstruct(&expr, &env).unwrap();

        assert_eq!(t, Type::Boolean);

        //
        let expr = Expr::parse(&"(if true 1.0 1)".parse::<SExpr>().unwrap()).unwrap();

        let mut sub = TypeSubstitution::new();
        let env = TypeEnv::new();
        match sub.reconstruct(&expr, &env).unwrap_err() {
            Error::TypeError(_) => {}
            _ => panic!("Expected test to throw TypeError"),
        }

        //
        let expr = Expr::parse(&"(if 2.0 1 2)".parse::<SExpr>().unwrap()).unwrap();

        let mut sub = TypeSubstitution::new();
        let env = TypeEnv::new();
        match sub.reconstruct(&expr, &env).unwrap_err() {
            Error::TypeError(_) => {}
            _ => panic!("Expected test to throw TypeError"),
        }
    }

    #[test]
    fn test3() {
        let expr = Expr::parse(
            &"(reduce (lambda (u v) v) 0 (iota 10))"
                .parse::<SExpr>()
                .unwrap(),
        )
        .unwrap();

        let mut sub = TypeSubstitution::new();
        let env = TypeEnv::new();
        let t = sub.reconstruct(&expr, &env).unwrap();

        assert_eq!(t, Type::Integer);

        let expr = Expr::parse(
            &"(scan (lambda (u v) v) 0 (iota 10))"
                .parse::<SExpr>()
                .unwrap(),
        )
        .unwrap();

        let mut sub = TypeSubstitution::new();
        let env = TypeEnv::new();
        let t = sub.reconstruct(&expr, &env).unwrap();

        assert_eq!(t, Type::Array(Box::new(Type::Integer)))
    }

    #[test]
    fn test4() {
        let expr = Expr::parse(
            &"(map (lambda (u) true) (iota 10))"
                .parse::<SExpr>()
                .unwrap(),
        )
        .unwrap();

        let mut sub = TypeSubstitution::new();
        let env = TypeEnv::new();
        let t = sub.reconstruct(&expr, &env).unwrap();

        assert_eq!(t, Type::Array(Box::new(Type::Boolean)));
    }

    #[test]
    fn test5() {
        // Direct expression
        let expr = Expr::parse(&"(reduce + 0 (iota 10))".parse::<SExpr>().unwrap()).unwrap();

        let (mut sub, env, _, _) = crate::stdlib::initialize();

        let t = sub.reconstruct(&expr, &env).unwrap();
        assert_eq!(t, Type::Integer);

        // Let expression
        let expr = Expr::parse(
            &"(let ((xs (iota 10))) (reduce + 0 xs))"
                .parse::<SExpr>()
                .unwrap(),
        )
        .unwrap();

        let (mut sub, env, _, _) = crate::stdlib::initialize();

        let t = sub.reconstruct(&expr, &env).unwrap();
        assert_eq!(t, Type::Integer);

        // Lambda application
        let expr = Expr::parse(
            &"((lambda (xs) (reduce + 0 xs)) (iota 10))"
                .parse::<SExpr>()
                .unwrap(),
        )
        .unwrap();

        let (mut sub, env, _, _) = crate::stdlib::initialize();

        let t = sub.reconstruct(&expr, &env).unwrap();
        assert_eq!(t, Type::Integer);
    }

    #[test]
    fn test6() {
        // Lambda application
        let expr = Expr::parse(
            &"((lambda (xs) (map (lambda (u) (+ u 1)) xs)) (iota 10))"
                .parse::<SExpr>()
                .unwrap(),
        )
        .unwrap();

        let (mut sub, env, _, _) = crate::stdlib::initialize();

        let t = sub.reconstruct(&expr, &env).unwrap();
        assert_eq!(t, Type::Array(Box::new(Type::Integer)));
    }

    #[test]
    fn test7() {
        let expr = Expr::parse(&"(lambda (xs) (reduce + 0 xs))".parse::<SExpr>().unwrap()).unwrap();

        let (mut sub, env, _, _) = crate::stdlib::initialize();

        let t = sub.reconstruct(&expr, &env).unwrap();
        assert_eq!(
            t,
            Type::Function(
                Box::new(Type::Array(Box::new(Type::Integer))),
                Box::new(Type::Integer)
            )
        );
    }

    #[test]
    fn pairs() {
        let expr = Expr::parse(
            &"(snd (fst (pair (pair 1.0 1) true)))"
                .parse::<SExpr>()
                .unwrap(),
        )
        .unwrap();
        let (mut sub, env, _, _) = crate::stdlib::initialize();
        let t = sub.reconstruct(&expr, &env).unwrap();

        assert_eq!(t, Type::Integer);
    }
}
