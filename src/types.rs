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
		Self::QuantifiedType(_,_) => unreachable!("Quantified type should be instantiated before occurs check is called")
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

pub fn reconstruct(expr: &Expr, env: &TypeEnv) -> Result<Type, Error> {
    Err(Error::TypeError("Type inference failed".into()))
}
