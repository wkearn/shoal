use crate::error::Error;
use crate::parser::Expr;

#[derive(Debug)]
pub enum Value {
    Boolean(bool),
    Integer(i64),
    Float(f64),
}

impl std::fmt::Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        match self {
            Value::Boolean(v) => write!(f, "{v}"),
            Value::Integer(v) => write!(f, "{v}"),
            Value::Float(v) => write!(f, "{v}"),
        }
    }
}

pub struct Env;

pub fn eval(expr: &Expr, env: &Env) -> Result<Value, Error> {
    match expr {
        Expr::BooleanLiteral(v) => Ok(Value::Boolean(*v)),
        Expr::IntegerLiteral(v) => Ok(Value::Integer(*v)),
        Expr::FloatLiteral(v) => Ok(Value::Float(*v)),
        Expr::Identifier(s) => {
            todo!()
        }
        Expr::Lambda(arg, body) => {
            todo!()
        }
        Expr::BinLambda(arg0, arg1, body) => {
            todo!()
        }
        Expr::Let(arg, def, body) => {
            todo!()
        }
        Expr::App(fun, arg) => {
            todo!()
        }
        Expr::BinApp(fun, arg0, arg1) => {
            todo!()
        }
        Expr::If(pred, conseq, alt) => match eval(pred, env)? {
            Value::Boolean(true) => eval(conseq, env),
            Value::Boolean(false) => eval(alt, env),
            _ => Err(Error::RuntimeError(
                "if statement predicate evaluated to a value of incorrect type".into(),
            )),
        },
        Expr::Map(fun, arr) => {
            todo!()
        }
        Expr::Reduce(fun, init, arr) => {
            todo!()
        }
        Expr::Scan(fun, init, arr) => {
            todo!()
        }
        Expr::Iota(n) => {
            todo!()
        }
    }
}
