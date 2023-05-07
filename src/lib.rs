pub mod error;
pub mod ops;
pub mod parser;

use error::Error;
use parser::{Env, Expr, Scope};

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

fn apply(e: &Expr, args: &[Rc<Expr>]) -> Result<Rc<Expr>, Error> {
    match e {
        Expr::PrimitiveFunc(f) => f(args).map(Rc::new),
        Expr::Func { params, body, env } => {
            env.borrow_bindings()
                .extend(params.iter().cloned().zip(args.iter().cloned()));
            eval(body, env)
        }
        _ => Err(Error::SyntaxError(format!(
            "head of call expression must be a function"
        ))),
    }
}

fn eval(e: &Expr, env: &Env) -> Result<Rc<Expr>, Error> {
    match e {
        Expr::Atom(v) => env
            .get(v)
            .map(|res| res.clone())
            .ok_or(Error::UndefinedVariableError(v.to_string())),
        Expr::Boolean(v) => Ok(Rc::new(Expr::Boolean(*v))), // This seems a bit wasteful
        Expr::Number(v) => Ok(Rc::new(Expr::Number(*v))),
        Expr::List(vs) => {
            let _: &Vec<Rc<Expr>> = vs;
            let head: &Expr = vs
                .get(0)
                .ok_or(Error::SyntaxError(format!("List needs a head")))?;

            match head {
                Expr::Atom(h) if h.as_str() == "if" => {
                    let pred = vs
                        .get(1)
                        .ok_or(Error::SyntaxError(format!("if requires a predicate")))?;
                    let conseq = vs
                        .get(2)
                        .ok_or(Error::SyntaxError(format!("if requires a consequent")))?;
                    let alt = vs
                        .get(3)
                        .ok_or(Error::SyntaxError(format!("if requires an alternative")))?;
                    match *eval(pred, env)? {
                        Expr::Boolean(true) => eval(conseq, env),
                        Expr::Boolean(false) => eval(alt, env),
                        _ => Err(Error::SyntaxError(format!(
                            "predicate must evaluate to a Boolean"
                        ))),
                    }
                }
                Expr::Atom(h) if h.as_str() == "quote" => vs
                    .get(1)
                    .map(|v| v.clone())
                    .ok_or(Error::SyntaxError(format!("quote requires an expression"))),
                Expr::Atom(h) if h.as_str() == "begin" => {
                    let mut expr = vs.iter().skip(1).map(|v| eval(v, env)).collect::<Result<
                        Vec<Rc<Expr>>,
                        Error,
                    >>(
                    )?;
                    expr.pop().ok_or(Error::SyntaxError(format!(
                        "begin requires at least one expression"
                    )))
                }
                Expr::Atom(h) if h.as_str() == "define" => {
                    let var: &Expr = vs.get(1).ok_or(Error::SyntaxError(format!(
                        "define requires a variable identifier"
                    )))?;
                    let val = vs
                        .get(2)
                        .ok_or(Error::SyntaxError(format!("define requires a value")))?;
                    let vale = eval(val, env)?;
                    match var {
                        Expr::Atom(v) => {
                            env.insert(v.to_string(), vale);
                            env.get(v)
                                .map(|res| res.clone())
                                .ok_or(Error::SyntaxError(format!(
                                    "Variable failed to set properly"
                                )))
                        }
                        _ => Err(Error::SyntaxError(format!(
                            "variable identifier should be an Atom"
                        ))),
                    }
                }
                Expr::Atom(h) if h.as_str() == "lambda" => {
                    let params: &Expr = vs.get(1).ok_or(Error::SyntaxError(format!(
                        "lambda requires a list of params"
                    )))?;
                    if let Expr::List(ps) = params {
                        // Get strings from params. This might get a little weird if each ps is
                        // not an Atom
                        let ps: Vec<String> = ps.iter().map(|p| p.to_string()).collect();
                        let body: Rc<Expr> = vs
                            .get(2)
                            .ok_or(Error::SyntaxError(format!("lambda requires a body")))?
                            .clone();

                        let new_env = Env::new(Rc::new(Scope::new(
                            RefCell::new(HashMap::new()),
                            Some(env.clone()),
                        )));

                        Ok(Rc::new(Expr::Func {
                            params: ps,
                            body,
                            env: new_env,
                        }))
                    } else {
                        Err(Error::SyntaxError(format!(
                            "lambda params should be a list"
                        )))
                    }
                }
                _ => {
                    // eval head
                    let func: Rc<Expr> = eval(head, env)?;
                    // eval the rest of the args
                    let args = vs
                        .iter()
                        .skip(1)
                        .map(|v| eval(v, env))
                        .collect::<Result<Vec<Rc<Expr>>, Error>>()?;

                    apply(&func, &args[..])
                }
            }
        }
        Expr::PrimitiveFunc(_) => Err(Error::SyntaxError(format!(
            "Primitive functions should not be returned from the parser"
        ))),
        Expr::Func { .. } => Err(Error::SyntaxError(format!(
            "Functions should not be returned from the parser"
        ))),
    }
}

pub fn run() -> Result<(), Error> {
    let global_env = {
        let mut map: HashMap<String, Rc<Expr>> = HashMap::new();
        map.insert(
            "+".to_string(),
            Rc::new(Expr::PrimitiveFunc(Box::new(|args| {
                ops::NumericBinaryOp::Add.apply(args)
            }))),
        );
        map.insert(
            "-".to_string(),
            Rc::new(Expr::PrimitiveFunc(Box::new(|args| {
                ops::NumericBinaryOp::Sub.apply(args)
            }))),
        );
        map.insert(
            "*".to_string(),
            Rc::new(Expr::PrimitiveFunc(Box::new(|args| {
                ops::NumericBinaryOp::Mul.apply(args)
            }))),
        );
        map.insert(
            "/".to_string(),
            Rc::new(Expr::PrimitiveFunc(Box::new(|args| {
                ops::NumericBinaryOp::Div.apply(args)
            }))),
        );
        map.insert(
            ">".to_string(),
            Rc::new(Expr::PrimitiveFunc(Box::new(|args| {
                ops::NumericBinaryOp::GreaterThan.apply(args)
            }))),
        );
        map.insert(
            ">=".to_string(),
            Rc::new(Expr::PrimitiveFunc(Box::new(|args| {
                ops::NumericBinaryOp::GreaterThanOrEqual.apply(args)
            }))),
        );
        map.insert(
            "<".to_string(),
            Rc::new(Expr::PrimitiveFunc(Box::new(|args| {
                ops::NumericBinaryOp::LessThan.apply(args)
            }))),
        );
        map.insert(
            "<=".to_string(),
            Rc::new(Expr::PrimitiveFunc(Box::new(|args| {
                ops::NumericBinaryOp::LessThanOrEqual.apply(args)
            }))),
        );
        map.insert(
            "min".to_string(),
            Rc::new(Expr::PrimitiveFunc(Box::new(|args| {
                ops::NumericBinaryOp::Min.apply(args)
            }))),
        );
        map.insert(
            "max".to_string(),
            Rc::new(Expr::PrimitiveFunc(Box::new(|args| {
                ops::NumericBinaryOp::Max.apply(args)
            }))),
        );
        map.insert(
            "exp".to_string(),
            Rc::new(Expr::PrimitiveFunc(Box::new(|args| {
                ops::NumericUnaryOp::Exp.apply(args)
            }))),
        );
        map.insert(
            "log".to_string(),
            Rc::new(Expr::PrimitiveFunc(Box::new(|args| {
                ops::NumericUnaryOp::Log.apply(args)
            }))),
        );
        map.insert(
            "inv".to_string(),
            Rc::new(Expr::PrimitiveFunc(Box::new(|args| {
                ops::NumericUnaryOp::Inv.apply(args)
            }))),
        );
        map.insert(
            "sin".to_string(),
            Rc::new(Expr::PrimitiveFunc(Box::new(|args| {
                ops::NumericUnaryOp::Sin.apply(args)
            }))),
        );
        map.insert(
            "cos".to_string(),
            Rc::new(Expr::PrimitiveFunc(Box::new(|args| {
                ops::NumericUnaryOp::Cos.apply(args)
            }))),
        );
        map.insert(
            "tan".to_string(),
            Rc::new(Expr::PrimitiveFunc(Box::new(|args| {
                ops::NumericUnaryOp::Tan.apply(args)
            }))),
        );
        map.insert(
            "abs".to_string(),
            Rc::new(Expr::PrimitiveFunc(Box::new(|args| {
                ops::NumericUnaryOp::Abs.apply(args)
            }))),
        );
        Env::new(Rc::new(Scope::new(RefCell::new(map), None)))
    };

    loop {
        let mut source = String::new();
        match std::io::stdin().read_line(&mut source) {
            Ok(_) => {}
            Err(e) => {
                eprintln!("{}", e);
                continue;
            }
        };

        match parser::lex(&source)
            .into_iter()
            .collect::<Result<Vec<parser::Token>, Error>>()
        {
            Ok(ts) => match parser::parse(ts) {
                Ok(ast) => match eval(&ast, &global_env) {
                    Ok(val) => println!("{}", val),
                    Err(e) => {
                        eprintln!("{}", e);
                        continue;
                    }
                },
                Err(e) => {
                    eprintln!("{}", e);
                    continue;
                }
            },
            Err(e) => {
                eprintln!("{}", e);
                continue;
            }
        }
    }
}
