pub mod error;
pub mod interpreter;
pub mod parser;
pub mod stdlib;
pub mod types;

use crate::error::Error;

pub fn run(src: &str) -> Result<(), Error> {
    let ex: parser::sexpr::parser::SExpr = src.parse()?;
    let ast = parser::parse(&ex)?;

    let (mut sub, env) = stdlib::initialize_types();
    let t = sub.reconstruct(&ast, &env)?;

    let v = interpreter::eval(&ast, &interpreter::Env)?;

    println!("{v}");
    Ok(())
}

pub fn repl() -> Result<(), Error> {
    let (mut sub, env) = stdlib::initialize_types();
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
            Ok(ex) => match parser::parse(&ex) {
                Ok(ast) => {
                    sub.clear(); // Clear the substitution
                    match sub.reconstruct(&ast, &env) {
                        Ok(t) => {
                            println!("{ast:?}: {t}");
                            match interpreter::eval(&ast, &interpreter::Env) {
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
