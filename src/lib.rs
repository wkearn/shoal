pub mod error;
pub mod parser;
pub mod stdlib;
pub mod types;

use crate::error::Error;

pub fn run(src: &str) -> Result<(), Error> {
    let ex: parser::sexpr::SExpr = src.parse()?;
    let ast = parser::parse(&ex)?;

    let (mut sub,env) = stdlib::initialize_types();
    let t = sub.reconstruct(&ast, &env).unwrap();

    println!("{ast:?}: {t}");
    Ok(())
}

pub fn repl() -> Result<(), Error> {
    let (mut sub,env) = stdlib::initialize_types();
    loop {
        let mut source = String::new();
        match std::io::stdin().read_line(&mut source) {
            Ok(_) => {}
            Err(e) => {
                eprintln!("{}", e);
                continue;
            }
        };

        match source.parse::<parser::sexpr::SExpr>() {
            Ok(ex) => match parser::parse(&ex) {
                Ok(ast) => {
		    sub.clear(); // Clear the substitution
                    match sub.reconstruct(&ast, &env) {			
                        Ok(t) => {			    
                            println!("{ast:?}: {t}");
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
