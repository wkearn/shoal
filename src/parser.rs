pub mod sexpr;

use sexpr::SExpr;

use crate::error::Error;

/// shoal's abstract syntax tree
#[derive(Debug, Clone)]
pub enum Expr {
    BooleanLiteral(bool),
    IntegerLiteral(i64),
    FloatLiteral(f64),
    Identifier(Box<str>),
    Lambda(Box<str>, Box<Expr>),
    BinLambda(Box<str>, Box<str>, Box<Expr>),
    App(Box<Expr>, Box<Expr>),
    BinApp(Box<Expr>, Box<Expr>, Box<Expr>),
    Let(Box<str>, Box<Expr>, Box<Expr>),
}

pub fn parse(sexpr: &SExpr) -> Result<Expr, Error> {
    match sexpr {
        SExpr::Boolean(v, _, _) => Ok(Expr::BooleanLiteral(v.clone())),
        SExpr::Integer(v, _, _) => Ok(Expr::IntegerLiteral(v.clone())),
        SExpr::Float(v, _, _) => Ok(Expr::FloatLiteral(v.clone())),
        SExpr::Atom(s, _, _) => Ok(Expr::Identifier(s.clone())),
        SExpr::List(vs, start_pos, end_pos) => {
            let head: &SExpr = vs.get(0).ok_or(Error::SyntaxError(format!(
                "[{start_pos}]: Empty list form"
            )))?;

            match head {
                SExpr::Atom(s, head_start_pos, head_end_pos) => {
                    match &**s {
                        "lambda" => {
                            // Lambda abstraction
                            if vs.len() == 3 {
                                let args = vs.get(1).ok_or(Error::SyntaxError(format!(
                                    "[{start_pos}]: lambda abstraction missing arguments"
                                )))?;

                                let body = vs.get(2).ok_or(Error::SyntaxError(format!(
                                    "[{start_pos}]: lambda abstraction missing body"
                                )))?;

                                let body = parse(body)?;

                                match args {
                                    SExpr::List(arg_list, args_start, args_end) => {
                                        if arg_list.len() <= 2 {
                                            let arg0 = arg_list.get(0).ok_or(
                                                Error::SyntaxError(format!(
                                                "[{args_start}]: lambda args missing first element"
                                            )),
                                            )?;

                                            if let Some(arg1) = arg_list.get(1) {
                                                match (arg0, arg1) {
                                                    (
                                                        SExpr::Atom(s0, _, _),
                                                        SExpr::Atom(s1, _, _),
                                                    ) => Ok(Expr::BinLambda(
                                                        s0.clone(),
                                                        s1.clone(),
                                                        Box::new(body),
                                                    )),
                                                    _ => Err(Error::SyntaxError(format!(
							"[{args_start}]: Expected lambda args to be atoms"
						    ))),
                                                }
                                            } else {
                                                match arg0 {
                                                    SExpr::Atom(s, _, _) => {
                                                        Ok(Expr::Lambda(s.clone(), Box::new(body)))
                                                    }
                                                    _ => Err(Error::SyntaxError(format!(
							"[{args_start}]: Expected lambda arg to be an atom"
						    ))),
                                                }
                                            }
                                        } else {
                                            Err(Error::SyntaxError(format!(
						"[{args_start}]: Expected lambda args to have 1 or 2 elements"
					    )))
                                        }
                                    }
                                    _ => Err(Error::SyntaxError(format!(
                                        "[{start_pos}]: lambda args should be a list"
                                    ))),
                                }
                            } else {
                                Err(Error::SyntaxError(format!(
				    "[{start_pos}]: lambda form should be followed by two expressions"
				)))
                            }
                        }
                        "let" => {
                            // Let abstraction
                            if vs.len() == 3 {
                                let body = vs.get(2).ok_or(Error::SyntaxError(format!(
                                    "[{start_pos}]: lambda abstraction missing body"
                                )))?;

                                let body = parse(body)?;

                                if let Some(SExpr::List(letdefs, _, _)) = vs.get(1) {
                                    if let Some(SExpr::List(letdef0, def0start, _)) = letdefs.get(0)
                                    {
                                        if let Some(SExpr::Atom(arg, _, _)) = letdef0.get(0) {
                                            let def = parse(letdef0.get(1).ok_or(
                                                Error::SyntaxError(format!(
                                                    "[{def0start}]: let definition is missing body"
                                                )),
                                            )?)?;
                                            Ok(Expr::Let(
                                                arg.clone(),
                                                Box::new(def),
                                                Box::new(body),
                                            ))
                                        } else {
                                            Err(Error::SyntaxError(format!(
						"[{def0start}]: Variable in let definition should be an atom"
					    )))
                                        }
                                    } else {
                                        Err(Error::SyntaxError(format!(
                                            "[{start_pos}]: let expression needs one definition"
                                        )))
                                    }
                                } else {
                                    Err(Error::SyntaxError(format!(
                                    "[{start_pos}]: let expression is missing valid definition list"
                                )))
                                }
                            } else {
                                Err(Error::SyntaxError(format!(
                                    "[{start_pos}]: let form should be followed by two expressions"
                                )))
                            }
                        }
                        _ => {
                            // This is function application
                            if vs.len() <= 3 {
                                let arg0 = vs.get(1).ok_or(Error::SyntaxError(format!(
                                    "Function application needs at least one argument"
                                )))?;

                                let arg0 = parse(arg0)?;

                                if let Some(arg1) = vs.get(2) {
                                    let arg1 = parse(arg1)?;
                                    Ok(Expr::BinApp(
                                        Box::new(Expr::Identifier(s.clone())),
                                        Box::new(arg0),
                                        Box::new(arg1),
                                    ))
                                } else {
                                    Ok(Expr::App(
                                        Box::new(Expr::Identifier(s.clone())),
                                        Box::new(arg0),
                                    ))
                                }
                            } else {
                                Err(Error::SyntaxError(format!(
				    "[{start_pos}]: function application should be followed by two or three expressions"
				)))
                            }
                        }
                    }
                }
                SExpr::List(_, _, _) => {
                    // This is function application with an expression
		    let fun = parse(head)?;

                    if vs.len() <= 3 {
                        let arg0 = vs.get(1).ok_or(Error::SyntaxError(format!(
                            "Function application needs at least one argument"
                        )))?;

                        let arg0 = parse(arg0)?;

                        if let Some(arg1) = vs.get(2) {
                            let arg1 = parse(arg1)?;
                            Ok(Expr::BinApp(
                                Box::new(fun),
                                Box::new(arg0),
                                Box::new(arg1),
                            ))
                        } else {
                            Ok(Expr::App(
                                Box::new(fun),
                                Box::new(arg0),
                            ))
                        }
                    } else {
                        Err(Error::SyntaxError(format!(
				    "[{start_pos}]: function application should be followed by two or three expressions"
				)))
                    }
                }
                _ => Err(Error::SyntaxError(format!(
                    "[{start_pos}]: Invalid list head"
                ))),
            }
        }
    }
}

mod test {
    use super::*;

    #[test]
    fn test1() {
        let src: SExpr = "(+ 1 2)".parse().unwrap();
        let ex = parse(&src).unwrap();
    }

    #[test]
    fn test2() {
        let src: SExpr = "((lambda (u v w) (+ u v)) 1 2)".parse().unwrap();
        parse(&src).unwrap_err();
    }

    #[test]
    fn test3() {
	// This should parse successfully, but it will be a type error later
	let src: SExpr = "((lambda (u) (+ u v)) 1 2)".parse().unwrap();
        let ex = parse(&src).unwrap();
    }

    #[test]
    fn test4() {
	let src: SExpr = "(let ((f (lambda (u v) (let ((m (max u v))) (+ (exp (- u m)) (exp (- v m))))))) (f 1.0 2.0))".parse().unwrap();
        let ex = parse(&src).unwrap();
    }
}
