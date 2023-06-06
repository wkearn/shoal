pub mod primitives;

use crate::error::Error;
use crate::parser::{Expr,sexpr::lexer::Position};

use primitives::PrimitiveOp;

use std::collections::HashMap;

#[derive(Debug, Clone)]
pub enum Value {
    Nil,
    Boolean(bool),
    Integer(i64),
    Float(f64),
    Array(Box<[Value]>),
    Function(Box<str>, Expr<Position>, Env),
    BinaryFunction(Box<str>, Box<str>, Expr<Position>, Env),
    PrimitiveFunction(Box<str>),
    Pair(Box<Value>, Box<Value>),
}

impl std::fmt::Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        match self {
            Value::Nil => write!(f, "nil"),
            Value::Boolean(v) => write!(f, "{v}"),
            Value::Integer(v) => write!(f, "{v}"),
            Value::Float(v) => write!(f, "{v}"),
            Value::Array(v) => write!(
                f,
                "[{}]",
                v.iter()
                    .map(|x| x.to_string())
                    .collect::<Vec<String>>()
                    .join(",")
            ),
            Value::Function(_, _, _) => {
                write!(f, "lambda")
            }
            Value::BinaryFunction(_, _, _, _) => {
                write!(f, "binlambda")
            }
            Value::PrimitiveFunction(v) => {
                write!(f, "<{v}>")
            }
            Value::Pair(v1, v2) => {
                write!(f, "{{{v1},{v2}}}")
            }
        }
    }
}

#[derive(Debug, Default, Clone)]
pub struct Env(HashMap<Box<str>, Value>);

impl Env {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn insert(&mut self, k: Box<str>, v: Value) -> Option<Value> {
        self.0.insert(k, v)
    }
}

// The primitive table holds references to predefined primitive operators
#[derive(Default)]
pub struct PrimitiveTable(HashMap<Box<str>, Box<dyn PrimitiveOp>>);

impl PrimitiveTable {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn insert<P>(&mut self, k: Box<str>, v: P) -> Option<Box<dyn PrimitiveOp>>
    where
        P: PrimitiveOp + 'static,
    {
        self.0.insert(k, Box::new(v))
    }
}

pub fn eval(expr: &Expr, env: &Env, prims: &PrimitiveTable) -> Result<Value, Error> {
    match expr {
        Expr::BooleanLiteral(v) => Ok(Value::Boolean(*v)),
        Expr::IntegerLiteral(v) => Ok(Value::Integer(*v)),
        Expr::FloatLiteral(v) => Ok(Value::Float(*v)),
        Expr::Identifier(s) => env
            .0
            .get(s)
            .ok_or(Error::UndefinedVariableError(s.to_string()))
            .map(|x| x.clone()),
        Expr::Lambda(arg, body) => Ok(Value::Function(arg.clone(), *body.clone(), env.clone())),
        Expr::BinLambda(arg0, arg1, body) => Ok(Value::BinaryFunction(
            arg0.clone(),
            arg1.clone(),
            *body.clone(),
            env.clone(),
        )),
        Expr::Let(arg, def, body) => {
            let defval = eval(def, env, prims)?;
            let mut local_env = Env::new(); // Create a new local environment
                                            // Add existing environment entries
            local_env
                .0
                .extend(env.0.iter().map(|(k, v)| (k.clone(), v.clone())));
            local_env.0.insert(arg.clone(), defval); // Bind the function args

            eval(&body, &local_env, prims)
        }
        Expr::App(fun, arg) => {
            match eval(fun, env, prims)? {
                Value::Function(funarg, funbody, closure) => {
                    let argval = eval(arg, env, prims)?;
                    let mut local_env = Env::new(); // Create a new local environment
                                                    // Add existing environment entries
                    local_env
                        .0
                        .extend(closure.0.iter().map(|(k, v)| (k.clone(), v.clone())));
                    local_env.0.insert(funarg, argval); // Bind the function args

                    eval(&funbody, &local_env, prims)
                }
                Value::PrimitiveFunction(name) => {
                    let fun = prims
                        .0
                        .get(&name)
                        .ok_or(Error::UndefinedVariableError(name.to_string()))?;
                    let argval = eval(arg, env, prims)?;
                    fun.apply(&argval, &Value::Nil)
                }
                _ => Err(Error::RuntimeError(
                    "Application head evaluated to a value of incorrect type".into(),
                )),
            }
        }
        Expr::BinApp(fun, arg0, arg1) => {
            match eval(fun, env, prims)? {
                Value::BinaryFunction(funarg0, funarg1, funbody, closure) => {
                    let arg0val = eval(arg0, env, prims)?;
                    let arg1val = eval(arg1, env, prims)?;
                    let mut local_env = Env::new(); // Create a new local environment
                                                    // Add existing environment entries
                    local_env
                        .0
                        .extend(closure.0.iter().map(|(k, v)| (k.clone(), v.clone())));
                    local_env.0.insert(funarg0, arg0val); // Bind the function args
                    local_env.0.insert(funarg1, arg1val); // Bind the function args

                    eval(&funbody, &local_env, prims)
                }
                Value::PrimitiveFunction(name) => {
                    let fun = prims
                        .0
                        .get(&name)
                        .ok_or(Error::UndefinedVariableError(name.to_string()))?;
                    let arg0val = eval(arg0, env, prims)?;
                    let arg1val = eval(arg1, env, prims)?;
                    fun.apply(&arg0val, &arg1val)
                }
                _ => Err(Error::RuntimeError(
                    "Application head evaluated to a value of incorrect type".into(),
                )),
            }
        }
        Expr::If(pred, conseq, alt) => match eval(pred, env, prims)? {
            Value::Boolean(true) => eval(conseq, env, prims),
            Value::Boolean(false) => eval(alt, env, prims),
            _ => Err(Error::RuntimeError(
                "if statement predicate evaluated to a value of incorrect type".into(),
            )),
        },
        Expr::Map(fun, arr) => {
            match eval(fun, env, prims)? {
                Value::Function(funarg, funbody, closure) => {
                    match eval(arr, env, prims)? {
                        Value::Array(xs) => {
                            let mut local_env = Env::new(); // Create a new local environment
                                                            // Add existing environment entries
                            local_env
                                .0
                                .extend(closure.0.iter().map(|(k, v)| (k.clone(), v.clone())));
                            let ys = xs
                                .iter()
                                .map(|x| {
                                    local_env.0.insert(funarg.clone(), x.clone());
                                    eval(&funbody, &local_env, prims)
                                })
                                .collect::<Result<Box<[Value]>, Error>>()?;
                            Ok(Value::Array(ys))
                        }
                        _ => Err(Error::RuntimeError(
                            "Map argument evaluated to a value of incorrect type".into(),
                        )),
                    }
                }
                Value::PrimitiveFunction(name) => {
                    let fun = prims
                        .0
                        .get(&name)
                        .ok_or(Error::UndefinedVariableError(name.to_string()))?;
                    match eval(arr, env, prims)? {
                        Value::Array(xs) => {
                            let ys = xs
                                .iter()
                                .map(|x| fun.apply(x, &Value::Nil))
                                .collect::<Result<Box<[Value]>, Error>>()?;
                            Ok(Value::Array(ys))
                        }
                        _ => Err(Error::RuntimeError(
                            "Map argument evaluated to a value of incorrect type".into(),
                        )),
                    }
                }
                _ => Err(Error::RuntimeError(
                    "Map head evaluated to a value of incorrect type".into(),
                )),
            }
        }
        Expr::Reduce(fun, init, arr) => {
            match eval(fun, env, prims)? {
                Value::BinaryFunction(funarg0, funarg1, funbody, closure) => {
                    let initval = eval(init, env, prims)?;
                    match eval(arr, env, prims)? {
                        Value::Array(xs) => {
                            let mut local_env = Env::new(); // Create a new local environment
                                                            // Add existing environment entries
                            local_env
                                .0
                                .extend(closure.0.iter().map(|(k, v)| (k.clone(), v.clone())));
                            let y = xs.iter().try_fold(initval, |acc, x| {
                                local_env.0.insert(funarg0.clone(), acc.clone());
                                local_env.0.insert(funarg1.clone(), x.clone());
                                eval(&funbody, &local_env, prims)
                            })?;
                            Ok(y)
                        }
                        _ => Err(Error::RuntimeError(
                            "Reduce argument evaluated to a value of incorrect type".into(),
                        )),
                    }
                }
                Value::PrimitiveFunction(name) => {
                    let fun = prims
                        .0
                        .get(&name)
                        .ok_or(Error::UndefinedVariableError(name.to_string()))?;
                    let initval = eval(init, env, prims)?;
                    match eval(arr, env, prims)? {
                        Value::Array(xs) => {
                            let y = xs.iter().try_fold(initval, |acc, x| fun.apply(&acc, x))?;
                            Ok(y)
                        }
                        _ => Err(Error::RuntimeError(
                            "Map argument evaluated to a value of incorrect type".into(),
                        )),
                    }
                }
                _ => Err(Error::RuntimeError(
                    "Reduce head evaluated to a value of incorrect type".into(),
                )),
            }
        }
        Expr::Scan(fun, init, arr) => {
            match eval(fun, env, prims)? {
                Value::BinaryFunction(funarg0, funarg1, funbody, closure) => {
                    let initval = eval(init, env, prims)?;
                    match eval(arr, env, prims)? {
                        Value::Array(xs) => {
                            let mut local_env = Env::new(); // Create a new local environment
                                                            // Add existing environment entries
                            local_env
                                .0
                                .extend(closure.0.iter().map(|(k, v)| (k.clone(), v.clone())));
                            let ys = xs
                                .iter()
                                .scan(initval, |acc, x| {
                                    local_env.0.insert(funarg0.clone(), acc.clone());
                                    local_env.0.insert(funarg1.clone(), x.clone());
                                    match eval(&funbody, &local_env, prims) {
                                        Ok(v) => {
                                            *acc = v.clone();
                                            Some(v)
                                        }
                                        Err(_) => None,
                                    }
                                })
                                .collect();
                            Ok(Value::Array(ys))
                        }
                        _ => Err(Error::RuntimeError(
                            "Scan argument evaluated to a value of incorrect type".into(),
                        )),
                    }
                }
                Value::PrimitiveFunction(name) => {
                    let fun = prims
                        .0
                        .get(&name)
                        .ok_or(Error::UndefinedVariableError(name.to_string()))?;
                    let initval = eval(init, env, prims)?;
                    match eval(arr, env, prims)? {
                        Value::Array(xs) => {
                            let ys = xs
                                .iter()
                                .scan(initval, |acc, x| match fun.apply(&acc, x) {
                                    Ok(v) => {
                                        *acc = v.clone();
                                        Some(v)
                                    }
                                    Err(_) => None,
                                })
                                .collect();
                            Ok(Value::Array(ys))
                        }
                        _ => Err(Error::RuntimeError(
                            "Map argument evaluated to a value of incorrect type".into(),
                        )),
                    }
                }
                _ => Err(Error::RuntimeError(
                    "Scan head evaluated to a value of incorrect type".into(),
                )),
            }
        }
        Expr::Iota(num) => match eval(num, env, prims)? {
            Value::Integer(n) => Ok(Value::Array(
                (0..n)
                    .map(|i| Value::Integer(i))
                    .collect::<Vec<Value>>()
                    .into(),
            )),
            _ => Err(Error::RuntimeError(
                "iota argument evaluated to a value of incorrect type".into(),
            )),
        },
        Expr::Pair(e1, e2) => {
            let v1 = eval(e1, env, prims)?;
            let v2 = eval(e2, env, prims)?;

            Ok(Value::Pair(Box::new(v1), Box::new(v2)))
        }
        Expr::Fst(p) => match eval(p, env, prims)? {
            Value::Pair(v1, _) => Ok(*v1),
            _ => Err(Error::RuntimeError(
                "fst argument evaluated to a value of incorrect type".into(),
            )),
        },
        Expr::Snd(p) => match eval(p, env, prims)? {
            Value::Pair(_, v2) => Ok(*v2),
            _ => Err(Error::RuntimeError(
                "snd argument evaluated to a value of incorrect type".into(),
            )),
        },
    }
}
