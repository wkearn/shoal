pub mod error;
pub mod parser;

use crate::error::Error;

pub fn run(src: &str) -> Result<(), Error> {
    let ex: parser::sexpr::SExpr = src.parse()?;
    let ast = parser::parse(&ex)?;
    println!("{ast:?}");
    Ok(())
}

pub fn repl() -> Result<(),Error> {
    loop {
        let mut source = String::new();
        match std::io::stdin().read_line(&mut source) {
            Ok(_) => {}
            Err(e) => {
                eprintln!("{}", e);
                continue;
            }
        };

	let ex: parser::sexpr::SExpr = source.parse()?;
	let ast = parser::parse(&ex)?;
	println!("{ast:?}")
    }    
}
