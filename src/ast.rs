use std::rc::Rc;

use crate::error::Error;
use crate::env::Env;

pub enum Expr {
    Atom(String),
    Boolean(bool),
    Number(f64),
    List(Vec<Rc<Expr>>),
    PrimitiveFunc(Box<dyn Fn(&[Rc<Expr>]) -> Result<Expr, Error>>),
    Func {
        params: Vec<String>,
        env: Env,
        body: Rc<Expr>,
    },
}

impl std::fmt::Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        match self {
            Expr::Atom(s) => write!(f, "{}", s),
            Expr::Boolean(s) => write!(f, "{}", s),
            Expr::Number(v) => write!(f, "{}", v),
            Expr::List(vs) => write!(
                f,
                "({})",
                vs.into_iter()
                    .map(|x| { x.to_string() })
                    .collect::<Vec<String>>()
                    .join(" ")
            ),
            Expr::PrimitiveFunc(_) => write!(f, "primitive"),
            Expr::Func { params, .. } => write!(f, "(lambda ({}))", params.join(" ")),
        }
    }
}
