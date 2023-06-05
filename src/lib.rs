pub mod compiler;
pub mod error;
pub mod interpreter;
pub mod parser;
pub mod stdlib;
pub mod types;

use crate::error::Error;
use crate::parser::Expr;

pub fn run(src: &str) -> Result<(), Error> {
    let ex: parser::sexpr::parser::SExpr = src.parse()?;
    let ast = Expr::parse(&ex)?;

    let (mut sub, type_env, env, prims) = stdlib::initialize();
    let t = sub.reconstruct(&ast, &type_env)?;

    println!("{ast:?}: {t}");

    let c = compiler::compile(&ast)?;

    println!("{c}");
    Ok(())
}

pub fn repl() -> Result<(), Error> {
    let (mut sub, type_env, env, prims) = stdlib::initialize();
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
            Ok(ex) => match Expr::parse(&ex) {
                Ok(ast) => {
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
