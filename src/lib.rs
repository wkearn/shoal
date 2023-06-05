pub mod compiler;
pub mod error;
pub mod interpreter;
pub mod parser;
pub mod stdlib;
pub mod types;

use crate::error::Error;
use crate::parser::{Expr, Statement};

pub fn run(src: &str) -> Result<(), Error> {
    let ex: parser::sexpr::parser::SExpr = src.parse()?;
    let ast = Expr::parse(&ex)?;

    let (mut sub, type_env, _env, _prims) = stdlib::initialize();
    let t = sub.reconstruct(&ast, &type_env)?;

    println!("{ast:?}: {t}");

    let c = compiler::compile(&ast)?;

    println!("{c}");
    Ok(())
}

pub fn repl() -> Result<(), Error> {
    let (mut sub, mut type_env, mut env, prims) = stdlib::initialize();
    loop {
        let mut source = String::new();
        match std::io::stdin().read_line(&mut source) {
            Ok(_) => {}
            Err(e) => {
                eprintln!("{}", e);
                continue;
            }
        };

        match source.parse::<parser::sexpr::parser::SExpr>() {
            Ok(ex) => match Statement::parse(&ex) {
                Ok(Statement::Expression(ast)) => {
                    sub.clear(); // Clear the substitution
                    match sub.reconstruct(&ast, &type_env) {
                        Ok(t) => {
                            println!("{ast:?}: {t}");
                            match interpreter::eval(&ast, &env, &prims) {
                                Ok(v) => println!("{v}"),
                                Err(e) => {
                                    eprintln!("{}", e);
                                    continue;
                                }
                            }
                        }
                        Err(e) => {
                            eprintln!("{}", e);
                            continue;
                        }
                    }
                }
                Ok(Statement::Definition(var, def)) => {
                    sub.clear();
                    match sub.reconstruct(&def, &type_env) {
                        Ok(t) => {
                            println!("{def}: {t}");
                            match interpreter::eval(&def, &env, &prims) {
                                Ok(v) => {
                                    println!("{var} = {v}");
                                    env.insert(var.clone(), v);
                                    type_env.insert(var, types::TypeScheme::PlainType(t));
                                }
                                Err(e) => {
                                    eprintln!("{}", e);
                                    continue;
                                }
                            }
                        }
                        Err(e) => {
                            eprintln!("{}", e);
                            continue;
                        }
                    }
                }
                Err(e) => {
                    eprintln!("{}", e);
                    continue;
                }
            },
            Err(e) => {
                eprintln!("{}", e);
                continue;
            }
        };
    }
}
