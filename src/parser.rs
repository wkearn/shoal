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
    If(Box<Expr>, Box<Expr>, Box<Expr>),
    Map(Box<Expr>, Box<Expr>),
    Reduce(Box<Expr>, Box<Expr>, Box<Expr>),
    Iota(Box<Expr>),
}

impl std::fmt::Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
	match self {
	    Expr::BooleanLiteral(v) => write!(f,"{v}"),
	    Expr::IntegerLiteral(v) => write!(f,"{v}"),
	    Expr::FloatLiteral(v) => write!(f,"{v}"),
	    Expr::Identifier(s) => write!(f,"{s}"),
	    Expr::Lambda(arg,body) => write!(f,"(lambda ({arg}) {body})"),
	    Expr::BinLambda(arg0, arg1, body) => write!(f,"(lambda ({arg0} {arg1}) {body})"),
	    Expr::App(fun,arg) => write!(f,"({fun} {arg})"),
	    Expr::BinApp(fun,arg0,arg1) => write!(f,"({fun} {arg0} {arg1})"),
	    Expr::Let(arg,def,body) => write!(f,"(let (({arg} {def})) {body})"),
	    Expr::If(cond,conseq,alt) => write!(f,"(if {cond} {conseq} {alt})"),
	    Expr::Map(fun,arr) => write!(f,"(map {fun} {arr})"),
	    Expr::Reduce(fun,init,arr) => write!(f,"(reduce {fun} {init} {arr})"),
	    Expr::Iota(n) => write!(f,"(iota {n})"),
	}
    }
}

pub fn parse(sexpr: &SExpr) -> Result<Expr, Error> {
    match sexpr {
        SExpr::Boolean(v, _, _) => Ok(Expr::BooleanLiteral(v.clone())),
        SExpr::Integer(v, _, _) => Ok(Expr::IntegerLiteral(v.clone())),
        SExpr::Float(v, _, _) => Ok(Expr::FloatLiteral(v.clone())),
        SExpr::Atom(s, _, _) => Ok(Expr::Identifier(s.clone())),
        SExpr::List(vs, start_pos, _) => {
            let head: &SExpr = vs.get(0).ok_or(Error::SyntaxError(format!(
                "[{start_pos}]: Empty list form"
            )))?;

            match head {
                SExpr::Atom(s, _, _) => {
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
                                    SExpr::List(arg_list, args_start, _) => {
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
                        "if" => {
                            if vs.len() == 4 {
                                // (if cond conseq alt)
                                let cond = vs.get(1).ok_or(Error::SyntaxError(format!(
                                    "[{start_pos}]: If statement expects a condition"
                                )))?;
                                let cond = parse(cond)?;

                                let conseq = vs.get(2).ok_or(Error::SyntaxError(format!(
                                    "[{start_pos}]: If statement expects a then expression"
                                )))?;
                                let conseq = parse(conseq)?;

                                let alt = vs.get(3).ok_or(Error::SyntaxError(format!(
                                    "[{start_pos}]: If statement expects an else expression"
                                )))?;
                                let alt = parse(alt)?;

                                Ok(Expr::If(Box::new(cond), Box::new(conseq), Box::new(alt)))
                            } else {
                                Err(Error::SyntaxError(format!("[{start_pos}]: if statement should be applied to three expressions")))
                            }
                        }
                        "map" => {
                            if vs.len() == 3 {
                                let fun = vs.get(1).ok_or(Error::SyntaxError(format!(
                                    "[{start_pos}]: map statement expects a function"
                                )))?;
                                let fun = parse(fun)?;

                                let arr = vs.get(2).ok_or(Error::SyntaxError(format!(
                                    "[{start_pos}]: map statement expects an argument"
                                )))?;
                                let arr = parse(arr)?;

                                Ok(Expr::Map(Box::new(fun), Box::new(arr)))
                            } else {
                                Err(Error::SyntaxError(format!("[{start_pos}]: map statement expects two expressions: (map f xs)")))
                            }
                        }
                        "reduce" => {
                            if vs.len() == 4 {
                                let fun = vs.get(1).ok_or(Error::SyntaxError(format!(
                                    "[{start_pos}]: reduce statement expects a function: (reduce f init arg)"
                                )))?;
                                let fun = parse(fun)?;

				let init = vs.get(2).ok_or(Error::SyntaxError(format!(
                                    "[{start_pos}]: reduce statement expects an initial value: (reduce f init arg)"
                                )))?;
                                let init = parse(init)?;
				
                                let arr = vs.get(3).ok_or(Error::SyntaxError(format!(
                                    "[{start_pos}]: reduce statement expects an argument: (reduce f init arg)"
                                )))?;
                                let arr = parse(arr)?;

                                Ok(Expr::Reduce(Box::new(fun), Box::new(init), Box::new(arr)))
                            } else {
                                Err(Error::SyntaxError(format!("[{start_pos}]: reduce statement expects three expressions: (reduce f init arg)")))
                            }
                        }
                        "iota" => {
			    if vs.len() == 2 {				
                                let arg = vs.get(1).ok_or(Error::SyntaxError(format!(
                                    "[{start_pos}]: iota statement expects an argument: (iota n)"
                                )))?;
                                let arg = parse(arg)?;

                                Ok(Expr::Iota(Box::new(arg)))
                            } else {
                                Err(Error::SyntaxError(format!("[{start_pos}]: iota statement expects one expression: (iota n)")))
                            }
                        }
                        _ => {
                            // This is function application
                            if vs.len() <= 3 {
                                let arg0 = vs.get(1).ok_or(Error::SyntaxError(format!(
                                    "[{start_pos}]: Function application needs at least one argument"
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
                            Ok(Expr::BinApp(Box::new(fun), Box::new(arg0), Box::new(arg1)))
                        } else {
                            Ok(Expr::App(Box::new(fun), Box::new(arg0)))
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

#[cfg(test)]
mod test {
    use super::{parse, SExpr};

    #[test]
    fn test1() {
        let src: SExpr = "(+ 1 2)".parse().unwrap();
        parse(&src).unwrap();
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
        parse(&src).unwrap();
    }

    #[test]
    fn test4() {
        let src: SExpr = "(let ((f (lambda (u v) (let ((m (max u v))) (+ (exp (- u m)) (exp (- v m))))))) (f 1.0 2.0))".parse().unwrap();
        parse(&src).unwrap();
    }

    #[test]
    fn test5() {
        let src: SExpr = "(if (== 1.0 2.0) 2.0 3.0)".parse().unwrap();
        parse(&src).unwrap();
    }

    #[test]
    fn test6() {
        let src: SExpr = "(reduce + 0 (map (lambda (u) (+ u 1)) (iota 10)))".parse().unwrap();
        parse(&src).unwrap();
    }
}
