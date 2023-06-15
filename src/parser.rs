pub mod sexpr;

use crate::error::Error;
use crate::parser::sexpr::{
    lexer::Position,
    parser::{SExpr, SExprs},
};

use std::collections::HashSet;

/// A program is a collection of statements
#[derive(Debug)]
pub struct Program<T>(Vec<Statement<T>>);

impl<T> Program<T> {
    pub fn new(vs: Vec<Statement<T>>) -> Self {
        Self(vs)
    }
    pub fn statements(&self) -> &Vec<Statement<T>> {
        &self.0
    }
}

impl TryFrom<SExprs> for Program<Position> {
    type Error = Error;
    fn try_from(vs: SExprs) -> Result<Self, Error> {
        let statements: Result<Vec<Statement<Position>>, Error> =
            vs.list().iter().map(Statement::parse).collect();
        Ok(Program(statements?))
    }
}

/// A statement in a shoal program is either a definition or an expression
#[derive(Debug)]
pub enum Statement<T> {
    Definition(T, Box<str>, Expr<T>),
    Expression(Expr<T>),
}

impl TryFrom<SExpr> for Statement<Position> {
    type Error = Error;

    fn try_from(sexpr: SExpr) -> Result<Self, Error> {
        Statement::parse(&sexpr)
    }
}

impl Statement<Position> {
    pub fn parse(sexpr: &SExpr) -> Result<Self, Error> {
        match sexpr {
            SExpr::List(vs, start_pos, _) => {
                let head: &SExpr = vs.get(0).ok_or(Error::SyntaxError(format!(
                    "[{start_pos}]: Empty list form"
                )))?;

                match head {
                    SExpr::Atom(s, head_start, _) => match &**s {
                        "define" => {
                            let var = vs.get(1).ok_or(Error::SyntaxError(format!(
                                "[{start_pos}]: define statement missing variable identifier"
                            )))?;

                            match var {
				    SExpr::Atom(v,_, _) => {
					let def = vs.get(2).ok_or(Error::SyntaxError(format!("[{head_start}]: define statement missing body")))?;
					let ex = Expr::parse(def)?;
					Ok(Statement::Definition(start_pos.clone(),v.clone(), ex))
				    }
				    _ => Err(Error::SyntaxError(format!("[{head_start}]: Expected identifier in first argument to define")))
				}
                        }
                        _ => {
                            let ex = Expr::parse(sexpr)?;
                            Ok(Statement::Expression(ex))
                        }
                    },
                    _ => {
                        let ex = Expr::parse(sexpr)?;
                        Ok(Statement::Expression(ex))
                    }
                }
            }
            _ => {
                let ex = Expr::parse(sexpr)?;
                Ok(Statement::Expression(ex))
            }
        }
    }
}

/// shoal's abstract syntax tree
#[derive(Debug, Clone)]
pub enum Expr<T> {
    BooleanLiteral(T, bool),
    IntegerLiteral(T, i64),
    FloatLiteral(T, f64),
    Identifier(T, Box<str>),
    Lambda(T, Box<str>, Box<Expr<T>>),
    BinLambda(T, Box<str>, Box<str>, Box<Expr<T>>),
    App(T, Box<Expr<T>>, Box<Expr<T>>),
    BinApp(T, Box<Expr<T>>, Box<Expr<T>>, Box<Expr<T>>),
    Let(T, Box<str>, Box<Expr<T>>, Box<Expr<T>>),
    If(T, Box<Expr<T>>, Box<Expr<T>>, Box<Expr<T>>),
    Map(T, Box<Expr<T>>, Box<Expr<T>>),
    Reduce(T, Box<Expr<T>>, Box<Expr<T>>, Box<Expr<T>>),
    Scan(T, Box<Expr<T>>, Box<Expr<T>>, Box<Expr<T>>),
    Iota(T, Box<Expr<T>>),
    Pair(T, Box<Expr<T>>, Box<Expr<T>>),
    Fst(T, Box<Expr<T>>),
    Snd(T, Box<Expr<T>>),
}

impl<T> std::fmt::Display for Expr<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        match self {
            Expr::BooleanLiteral(_, v) => write!(f, "{v}"),
            Expr::IntegerLiteral(_, v) => write!(f, "{v}"),
            Expr::FloatLiteral(_, v) => write!(f, "{v}"),
            Expr::Identifier(_, s) => write!(f, "{s}"),
            Expr::Lambda(_, arg, body) => write!(f, "(lambda ({arg}) {body})"),
            Expr::BinLambda(_, arg0, arg1, body) => write!(f, "(lambda ({arg0} {arg1}) {body})"),
            Expr::App(_, fun, arg) => write!(f, "({fun} {arg})"),
            Expr::BinApp(_, fun, arg0, arg1) => write!(f, "({fun} {arg0} {arg1})"),
            Expr::Let(_, arg, def, body) => write!(f, "(let (({arg} {def})) {body})"),
            Expr::If(_, cond, conseq, alt) => write!(f, "(if {cond} {conseq} {alt})"),
            Expr::Map(_, fun, arr) => write!(f, "(map {fun} {arr})"),
            Expr::Reduce(_, fun, init, arr) => write!(f, "(reduce {fun} {init} {arr})"),
            Expr::Scan(_, fun, init, arr) => write!(f, "(scan {fun} {init} {arr})"),
            Expr::Iota(_, n) => write!(f, "(iota {n})"),
            Expr::Pair(_, e1, e2) => write!(f, "(pair {e1} {e2})"),
            Expr::Fst(_, e) => write!(f, "(fst {e})"),
            Expr::Snd(_, e) => write!(f, "(snd {e})"),
        }
    }
}

impl<T> Expr<T> {
    pub fn tag(&self) -> &T {
        match self {
            Expr::BooleanLiteral(tag, _) => tag,
            Expr::IntegerLiteral(tag, _) => tag,
            Expr::FloatLiteral(tag, _) => tag,
            Expr::Identifier(tag, _) => tag,
            Expr::Lambda(tag, _, _) => tag,
            Expr::BinLambda(tag, _, _, _) => tag,
            Expr::App(tag, _, _) => tag,
            Expr::BinApp(tag, _, _, _) => tag,
            Expr::Let(tag, _, _, _) => tag,
            Expr::If(tag, _, _, _) => tag,
            Expr::Map(tag, _, _) => tag,
            Expr::Reduce(tag, _, _, _) => tag,
            Expr::Scan(tag, _, _, _) => tag,
            Expr::Iota(tag, _) => tag,
            Expr::Pair(tag, _, _) => tag,
            Expr::Fst(tag, _) => tag,
            Expr::Snd(tag, _) => tag,
        }
    }

    pub fn free_vars(&self) -> HashSet<Box<str>> {
        match self {
            Expr::BooleanLiteral(_, _) | Expr::IntegerLiteral(_, _) | Expr::FloatLiteral(_, _) => {
                HashSet::new()
            }
            Expr::Identifier(_, s) => Some(s.clone()).into_iter().collect(),
            Expr::Lambda(_, arg, body) => {
                let mut fvs = body.free_vars();
                fvs.remove(arg);
                fvs
            }
            Expr::BinLambda(_, arg0, arg1, body) => {
                let mut fvs = body.free_vars();
                fvs.remove(arg0);
                fvs.remove(arg1);
                fvs
            }
            Expr::App(_, fun, arg) => {
                let mut fvs = arg.free_vars();
                fvs.extend(fun.free_vars());
                fvs
            }
            Expr::BinApp(_, fun, arg0, arg1) => {
                let mut fvs = arg1.free_vars();
                fvs.extend(arg0.free_vars());
                fvs.extend(fun.free_vars());
                fvs
            }
            Expr::Let(_, var, def, body) => {
                let mut fvs = body.free_vars();
                fvs.remove(var);
                fvs.extend(def.free_vars());
                fvs
            }
            Expr::If(_, pred, conseq, alt) => {
                let mut fvs = alt.free_vars();
                fvs.extend(conseq.free_vars());
                fvs.extend(pred.free_vars());
                fvs
            }
            Expr::Map(_, fun, arr) => {
                let mut fvs = fun.free_vars();
                fvs.extend(arr.free_vars());
                fvs
            }
            Expr::Reduce(_, fun, init, arr) => {
                let mut fvs = arr.free_vars();
                fvs.extend(init.free_vars());
                fvs.extend(fun.free_vars());
                fvs
            }
            Expr::Scan(_, fun, init, arr) => {
                let mut fvs = arr.free_vars();
                fvs.extend(init.free_vars());
                fvs.extend(fun.free_vars());
                fvs
            }
            Expr::Iota(_, n) => n.free_vars(),
            Expr::Pair(_, e1, e2) => {
                let mut fvs = e1.free_vars();
                fvs.extend(e2.free_vars());
                fvs
            }
            Expr::Fst(_, p) => p.free_vars(),
            Expr::Snd(_, p) => p.free_vars(),
        }
    }
}

impl Expr<Position> {
    pub fn parse(sexpr: &SExpr) -> Result<Self, Error> {
        match sexpr {
            SExpr::Boolean(v, start_pos, _) => {
                Ok(Expr::BooleanLiteral(start_pos.clone(), v.clone()))
            }
            SExpr::Integer(v, start_pos, _) => {
                Ok(Expr::IntegerLiteral(start_pos.clone(), v.clone()))
            }
            SExpr::Float(v, start_pos, _) => Ok(Expr::App(
                start_pos.clone(),
                Box::new(Expr::Identifier(start_pos.clone(), "fromFloating".into())),
                Box::new(Expr::FloatLiteral(start_pos.clone(), v.clone())),
            )),
            SExpr::Atom(s, start_pos, _) => Ok(Expr::Identifier(start_pos.clone(), s.clone())),
            SExpr::List(vs, start_pos, _) => {
                let head: &SExpr = vs.get(0).ok_or(Error::SyntaxError(format!(
                    "[{start_pos}]: Empty list form"
                )))?;

                match head {
                    SExpr::Atom(s, head_start, _) => {
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

                                    let body: Expr<Position> = Expr::parse(body)?;

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
                                                            start_pos.clone(),
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
                                                        SExpr::Atom(s, _, _) => Ok(Expr::Lambda(
                                                            start_pos.clone(),
                                                            s.clone(),
                                                            Box::new(body),
                                                        )),
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

                                    let body = Expr::parse(body)?;

                                    if let Some(SExpr::List(letdefs, _, _)) = vs.get(1) {
                                        if let Some(SExpr::List(letdef0, def0start, _)) =
                                            letdefs.get(0)
                                        {
                                            if let Some(SExpr::Atom(arg, _, _)) = letdef0.get(0) {
                                                let def = Expr::parse(letdef0.get(1).ok_or(
                                                    Error::SyntaxError(format!(
                                                    "[{def0start}]: let definition is missing body"
                                                )),
                                                )?)?;
                                                Ok(Expr::Let(
                                                    start_pos.clone(),
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
                                    let cond = Expr::parse(cond)?;

                                    let conseq = vs.get(2).ok_or(Error::SyntaxError(format!(
                                        "[{start_pos}]: If statement expects a then expression"
                                    )))?;
                                    let conseq = Expr::parse(conseq)?;

                                    let alt = vs.get(3).ok_or(Error::SyntaxError(format!(
                                        "[{start_pos}]: If statement expects an else expression"
                                    )))?;
                                    let alt = Expr::parse(alt)?;

                                    Ok(Expr::If(
                                        start_pos.clone(),
                                        Box::new(cond),
                                        Box::new(conseq),
                                        Box::new(alt),
                                    ))
                                } else {
                                    Err(Error::SyntaxError(format!("[{start_pos}]: if statement should be applied to three expressions")))
                                }
                            }
                            "map" => {
                                if vs.len() == 3 {
                                    let fun = vs.get(1).ok_or(Error::SyntaxError(format!(
                                        "[{start_pos}]: map statement expects a function"
                                    )))?;
                                    let fun = Expr::parse(fun)?;

                                    let arr = vs.get(2).ok_or(Error::SyntaxError(format!(
                                        "[{start_pos}]: map statement expects an argument"
                                    )))?;
                                    let arr = Expr::parse(arr)?;

                                    Ok(Expr::Map(start_pos.clone(), Box::new(fun), Box::new(arr)))
                                } else {
                                    Err(Error::SyntaxError(format!("[{start_pos}]: map statement expects two expressions: (map f xs)")))
                                }
                            }
                            "reduce" => {
                                if vs.len() == 4 {
                                    let fun = vs.get(1).ok_or(Error::SyntaxError(format!(
                                    "[{start_pos}]: reduce statement expects a function: (reduce f init arg)"
                                )))?;
                                    let fun = Expr::parse(fun)?;

                                    let init = vs.get(2).ok_or(Error::SyntaxError(format!(
                                    "[{start_pos}]: reduce statement expects an initial value: (reduce f init arg)"
                                )))?;
                                    let init = Expr::parse(init)?;

                                    let arr = vs.get(3).ok_or(Error::SyntaxError(format!(
                                    "[{start_pos}]: reduce statement expects an argument: (reduce f init arg)"
                                )))?;
                                    let arr = Expr::parse(arr)?;

                                    Ok(Expr::Reduce(
                                        start_pos.clone(),
                                        Box::new(fun),
                                        Box::new(init),
                                        Box::new(arr),
                                    ))
                                } else {
                                    Err(Error::SyntaxError(format!("[{start_pos}]: reduce statement expects three expressions: (reduce f init arg)")))
                                }
                            }
                            "scan" => {
                                if vs.len() == 4 {
                                    let fun = vs.get(1).ok_or(Error::SyntaxError(format!(
                                    "[{start_pos}]: scan statement expects a function: (scan f init arg)"
                                )))?;
                                    let fun = Expr::parse(fun)?;

                                    let init = vs.get(2).ok_or(Error::SyntaxError(format!(
                                    "[{start_pos}]: scan statement expects an initial value: (scan f init arg)"
                                )))?;
                                    let init = Expr::parse(init)?;

                                    let arr = vs.get(3).ok_or(Error::SyntaxError(format!(
                                    "[{start_pos}]: scan statement expects an argument: (scan f init arg)"
                                )))?;
                                    let arr = Expr::parse(arr)?;

                                    Ok(Expr::Scan(
                                        start_pos.clone(),
                                        Box::new(fun),
                                        Box::new(init),
                                        Box::new(arr),
                                    ))
                                } else {
                                    Err(Error::SyntaxError(format!("[{start_pos}]: scan statement expects three expressions: (scan f init arg)")))
                                }
                            }
                            "iota" => {
                                if vs.len() == 2 {
                                    let arg = vs.get(1).ok_or(Error::SyntaxError(format!(
                                    "[{start_pos}]: iota statement expects an argument: (iota n)"
                                )))?;
                                    let arg = Expr::parse(arg)?;

                                    Ok(Expr::Iota(start_pos.clone(), Box::new(arg)))
                                } else {
                                    Err(Error::SyntaxError(format!("[{start_pos}]: iota statement expects one expression: (iota n)")))
                                }
                            }
                            "pair" => {
                                if vs.len() == 3 {
                                    let arg1 = vs.get(1).ok_or(Error::SyntaxError(format!(
					"[{start_pos}]: pair statement expects two arguments: (pair e1 e2)"
                                    )))?;
                                    let arg1 = Expr::parse(arg1)?;

                                    let arg2 = vs.get(2).ok_or(Error::SyntaxError(format!(
					"[{start_pos}]: pair statement expects two arguments: (pair e1 e2)"
                                    )))?;
                                    let arg2 = Expr::parse(arg2)?;

                                    Ok(Expr::Pair(
                                        start_pos.clone(),
                                        Box::new(arg1),
                                        Box::new(arg2),
                                    ))
                                } else {
                                    Err(Error::SyntaxError(format!("[{start_pos}]: pair statement expects two expressions: (pairs e1 e2)")))
                                }
                            }
                            "fst" => {
                                if vs.len() == 2 {
                                    let arg = vs.get(1).ok_or(Error::SyntaxError(format!(
                                        "[{start_pos}]: fst statement expects an argument: (fst p)"
                                    )))?;
                                    let arg = Expr::parse(arg)?;

                                    Ok(Expr::Fst(start_pos.clone(), Box::new(arg)))
                                } else {
                                    Err(Error::SyntaxError(format!("[{start_pos}]: fst statement expects one expression: (fst p)")))
                                }
                            }
                            "snd" => {
                                if vs.len() == 2 {
                                    let arg = vs.get(1).ok_or(Error::SyntaxError(format!(
                                        "[{start_pos}]: snd statement expects an argument: (snd p)"
                                    )))?;
                                    let arg = Expr::parse(arg)?;

                                    Ok(Expr::Snd(start_pos.clone(), Box::new(arg)))
                                } else {
                                    Err(Error::SyntaxError(format!("[{start_pos}]: fst statement expects one expression: (snd p)")))
                                }
                            }
                            _ => {
                                // This is function application
                                if vs.len() <= 3 {
                                    let arg0 = vs.get(1).ok_or(Error::SyntaxError(format!(
                                    "[{start_pos}]: Function application needs at least one argument"
                                )))?;

                                    let arg0 = Expr::parse(arg0)?;

                                    if let Some(arg1) = vs.get(2) {
                                        let arg1 = Expr::parse(arg1)?;
                                        Ok(Expr::BinApp(
                                            start_pos.clone(),
                                            Box::new(Expr::Identifier(
                                                head_start.clone(),
                                                s.clone(),
                                            )),
                                            Box::new(arg0),
                                            Box::new(arg1),
                                        ))
                                    } else {
                                        Ok(Expr::App(
                                            start_pos.clone(),
                                            Box::new(Expr::Identifier(
                                                head_start.clone(),
                                                s.clone(),
                                            )),
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
                        let fun = Expr::parse(head)?;

                        if vs.len() <= 3 {
                            let arg0 = vs.get(1).ok_or(Error::SyntaxError(format!(
                                "Function application needs at least one argument"
                            )))?;

                            let arg0 = Expr::parse(arg0)?;

                            if let Some(arg1) = vs.get(2) {
                                let arg1 = Expr::parse(arg1)?;
                                Ok(Expr::BinApp(
                                    start_pos.clone(),
                                    Box::new(fun),
                                    Box::new(arg0),
                                    Box::new(arg1),
                                ))
                            } else {
                                Ok(Expr::App(start_pos.clone(), Box::new(fun), Box::new(arg0)))
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
}

impl TryFrom<SExpr> for Expr<Position> {
    type Error = Error;

    fn try_from(sexpr: SExpr) -> Result<Self, Error> {
        Expr::parse(&sexpr)
    }
}

#[cfg(test)]
mod test {
    use super::{Expr, Position, Program, SExpr, SExprs, Statement};

    #[test]
    fn test1() {
        let src: SExpr = "(+ 1 2)".parse().unwrap();
        Expr::parse(&src).unwrap();
    }

    #[test]
    fn test2() {
        let src: SExpr = "((lambda (u v w) (+ u v)) 1 2)".parse().unwrap();
        Expr::parse(&src).unwrap_err();
    }

    #[test]
    fn test3() {
        // This should parse successfully, but it will be a type error later
        let src: SExpr = "((lambda (u) (+ u v)) 1 2)".parse().unwrap();
        Expr::parse(&src).unwrap();
    }

    #[test]
    fn test4() {
        let src: SExpr = "(let ((f (lambda (u v) (let ((m (max u v))) (+ (exp (- u m)) (exp (- v m))))))) (f 1.0 2.0))".parse().unwrap();
        Expr::parse(&src).unwrap();
    }

    #[test]
    fn test5() {
        let src: SExpr = "(if (== 1.0 2.0) 2.0 3.0)".parse().unwrap();
        Expr::parse(&src).unwrap();
    }

    #[test]
    fn test6() {
        let src: SExpr = "(reduce + 0 (scan + 0 (map (lambda (u) (+ u 1)) (iota 10))))"
            .parse()
            .unwrap();
        Expr::parse(&src).unwrap();
    }

    #[test]
    fn test7() {
        let src: SExpr = "(define incr (lambda (u) (+ u 1)))".parse().unwrap();
        let Statement::Definition(pos,var,def) = Statement::parse(&src).unwrap() else { panic!("Expected definition, found expression")};

        assert_eq!(pos, Position::new(1, 0));
        assert_eq!(var, "incr".into());

        match def {
            Expr::Lambda(_, _, _) => {}
            _ => panic!("Expected lambda found {def:?}"),
        }
    }

    #[test]
    fn test8() {
        let src: SExpr = "((lambda (u) (+ u 1)) 0)".parse().unwrap();
        let Statement::Expression(ex) = Statement::parse(&src).unwrap() else { panic!("Expected expression, found definition")};

        match ex {
            Expr::App(pos, fun, _) => {
                assert_eq!(pos, Position::new(1, 0));
                match *fun {
                    Expr::Lambda(tag, var, body) => {
                        assert_eq!(tag, Position::new(1, 1));
                        assert_eq!(var, "u".into());
                        match *body {
                            Expr::BinApp(_, _, _, _) => {}
                            _ => panic!("Expected binary application, found {body:?}"),
                        }
                    }
                    _ => panic!("Expected lambda found {fun:?}"),
                }
            }
            _ => panic!("Expected application found {ex:?}"),
        }
    }

    #[test]
    fn parse_program() {
        let prog: Program<Position> = "(define incr (lambda (u) (+ u 1)))\n(incr 0)"
            .parse::<SExprs>()
            .unwrap()
            .try_into()
            .unwrap();

        assert_eq!(2, prog.0.len())
    }

    #[test]
    fn free_vars() {
        let src: SExpr = "(lambda (rate) (lambda (x) (let ((x3 (log rate))) (let ((x4 (* rate x))) (- x3 x4)))))".parse().unwrap();
        let ex = Expr::parse(&src).unwrap();

        // Free variables are the global operators log, *, -
        assert_eq!(3, ex.free_vars().len());

        let src2: SExpr = "(lambda (x) (let ((x3 (log rate))) (let ((x4 (* rate x))) (- x3 x4))))"
            .parse()
            .unwrap();
        let ex2 = Expr::parse(&src2).unwrap();
        assert_eq!(4, ex2.free_vars().len());

        let src3: SExpr = "((lambda (xs) (reduce + 0 (map ((lambda (rate) (lambda (x) (let ((x3 (log rate))) (let ((x4 (* rate x))) (- x3 x4))))) 1.0) (scan + 0.0 (map (lambda (u) 1.0) xs))))) (iota n))".parse().unwrap();
        let ex = Expr::parse(&src3).unwrap();

        // Free variables are the global operators log, *, -, +, fromFloating, and the variable n
        assert_eq!(6, ex.free_vars().len());
    }
}
