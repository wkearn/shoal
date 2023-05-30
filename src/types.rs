//! Type inference for shoal

use crate::error::Error;
use crate::parser::Expr;

use std::collections::{HashMap, HashSet};

// TODO: Product types, additional numeric types
/// The set of valid types for a shoal expression
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    Boolean,
    Integer,
    Float64,
    TypeVar(Box<str>, HashSet<Box<str>>),
    Function(Box<Type>, Box<Type>),
    BinaryFunction(Box<Type>, Box<Type>, Box<Type>),
    Array(Box<Type>),
}

impl std::fmt::Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        match self {
            Self::Boolean => write!(f, "Boolean"),
            Self::Integer => write!(f, "Integer"),
            Self::Float64 => write!(f, "Float64"),
            Self::TypeVar(s, ops) => write!(
                f,
                "{s}_{{{}}}",
                ops.iter().cloned().collect::<Vec<Box<str>>>().join(","),
            ),
            Self::Function(arg, body) => write!(f, "{arg} -> {body}"),
            Self::BinaryFunction(arg0, arg1, body) => write!(f, "{arg0} x {arg1} -> {body}"),
            Self::Array(body) => write!(f, "[{body}]"),
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
                Type::TypeVar(t, _) => s == t,
                _ => false,
            }
        } else {
            false
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
/// A type scheme universally quantifies Types
pub enum TypeScheme {
    PlainType(Type),
    QuantifiedType(HashSet<Box<str>>, Type),
}

impl std::fmt::Display for TypeScheme {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        match self {
            Self::PlainType(t) => write!(f, "{t}"),
            Self::QuantifiedType(vars, t) => write!(
                f,
                "∀{} . {t}",
                vars.iter().cloned().collect::<Vec<Box<str>>>().join(" "),
            ),
        }
    }
}

impl TypeScheme {
    /// Check whether a type variable occurs within another constructor
    ///
    /// panics if `other` is a QuantifiedType, which should never be reached.
    fn occurs_check(&self, other: &Self) -> bool {
        if let TypeScheme::PlainType(s @ Type::TypeVar(_, _)) = self {
            match other {
                Self::PlainType(t) => s.occurs_check(t),
                Self::QuantifiedType(_, _) => unreachable!(
                    "Quantified type should be instantiated before occurs check is called"
                ),
            }
        } else {
            false
        }
    }
}

#[derive(Debug, Default)]
pub struct TypeEnv(HashMap<Box<str>, TypeScheme>);

impl TypeEnv {
    pub fn new() -> Self {
        Self::default()
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
    fn new() -> Self {
        Self::default()
    }
    /// Generate a fresh type variable with no overloading constraints
    fn genvar(&mut self) -> Type {
        self.genvar_with_ops(None)
    }

    /// Generate a fresh type variable with a set of overloading constraints
    fn genvar_with_ops<I>(&mut self, ops: I) -> Type
    where
        I: IntoIterator<Item = Box<str>>,
    {
        self.fresh_vars += 1;
        let s = format!("?X{}", self.fresh_vars);

        let ops_hs = ops.into_iter().collect();
        Type::TypeVar(s.into(), ops_hs)
    }

    /// Apply the type substitution to a Type
    fn get(&self, t: &Type) -> Type {
        match t {
            // Primitive types return the same type
            Type::Boolean => Type::Boolean,
            Type::Integer => Type::Integer,
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
            Type::TypeVar(s, _) => match self.substitution.get(s) {
                Some(u @ Type::TypeVar(_, _)) => self.get(u),
                Some(bound) => bound.clone(),
                None => t.clone(),
            },
        }
    }

    fn is_valid_overloading(&self, xs: &HashSet<Box<str>>, t: &Type) -> bool {
        match t {
            Type::TypeVar(_, _) => false,
            Type::Function(_, _) => xs.is_empty(),
            Type::BinaryFunction(_, _, _) => xs.is_empty(),
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
            Type::Float64 => {
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
                    // Substitute the right variable to make sure that it is reduced as far as possible
                    let new_right = self.get(right);
                    self.cs(ops, &new_right)?;
                    self.substitution.insert(x.clone(), new_right);
                    Ok(())
                }
            }
        }
    }
    pub fn reconstruct(&mut self, expr: &Expr, env: &TypeEnv) -> Result<Type, Error> {
        match expr {
            Expr::BooleanLiteral(_) => Ok(Type::Boolean),
            Expr::IntegerLiteral(_) => Ok(Type::Integer),
            Expr::FloatLiteral(_) => Ok(Type::Float64),
            Expr::Identifier(s) => {
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
                            local_sub
                                .substitution
                                .insert(v.clone(), self.genvar_with_ops(None));
                        }
                        let tt = local_sub.get(t);
                        Ok(tt)
                    }
                }
            }
            Expr::Lambda(arg, body) => {
		// Extend the local environment
		let (arg_type,body_type) = {
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
		    (arg_type,body_type)
		};

                let new_arg = self.get(&arg_type);
                let new_body = self.get(&body_type);

                Ok(Type::Function(Box::new(new_arg), Box::new(new_body)))
            }
            Expr::BinLambda(arg0, arg1, body) => todo!(),
            Expr::App(fun, arg) => todo!(),
            Expr::BinApp(fun, arg0, arg1) => todo!(),
            Expr::Let(arg, def, body) => todo!(),
            Expr::If(pred, conseq, alt) => todo!(),
            Expr::Map(fun, arg) => todo!(),
            Expr::Reduce(fun, init, arg) => todo!(),
            Expr::Scan(fun, init, arg) => todo!(),
            Expr::Iota(n) => todo!(),
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    use crate::parser;
    use crate::parser::sexpr::SExpr;

    #[test]
    fn test1() {
        let expr = parser::parse(
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
            parser::parse(&"(let ((f (lambda (x) x))) (f 1))".parse::<SExpr>().unwrap()).unwrap();

        let mut sub = TypeSubstitution::new();
        let env = TypeEnv::new();
        let t = sub.reconstruct(&expr, &env).unwrap();

        assert_eq!(t, Type::Integer);

        //
        let expr = parser::parse(
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
}
