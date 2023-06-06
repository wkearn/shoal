use crate::error::Error;
use crate::parser::Expr;

use std::cell::RefCell;

#[derive(Debug, Clone)]
pub enum AtomicExpr {
    BooleanLiteral(bool),
    IntegerLiteral(i64),
    FloatLiteral(f64),
    Identifier(Box<str>),
    Lambda(Box<str>, Box<NormalExpr>),
    BinLambda(Box<str>, Box<str>, Box<NormalExpr>),
}

impl From<AtomicExpr> for Expr<()> {
    fn from(atomic: AtomicExpr) -> Self {
        match atomic {
            AtomicExpr::BooleanLiteral(v) => Expr::BooleanLiteral((), v),
            AtomicExpr::IntegerLiteral(v) => Expr::IntegerLiteral((), v),
            AtomicExpr::FloatLiteral(v) => Expr::FloatLiteral((), v),
            AtomicExpr::Identifier(s) => Expr::Identifier((), s),
            AtomicExpr::Lambda(arg, body) => Expr::Lambda((), arg, Box::new(Expr::from(*body))),
            AtomicExpr::BinLambda(arg0, arg1, body) => {
                Expr::BinLambda((), arg0, arg1, Box::new(Expr::from(*body)))
            }
        }
    }
}

#[derive(Debug, Clone)]
pub enum ComplexExpr {
    App(Box<AtomicExpr>, Box<AtomicExpr>),
    BinApp(Box<AtomicExpr>, Box<AtomicExpr>, Box<AtomicExpr>),
    If(Box<AtomicExpr>, Box<NormalExpr>, Box<NormalExpr>),
    Map(Box<AtomicExpr>, Box<AtomicExpr>),
    Reduce(Box<AtomicExpr>, Box<AtomicExpr>, Box<AtomicExpr>),
    Scan(Box<AtomicExpr>, Box<AtomicExpr>, Box<AtomicExpr>),
    Iota(Box<AtomicExpr>),
    Pair(Box<AtomicExpr>, Box<AtomicExpr>),
    Fst(Box<AtomicExpr>),
    Snd(Box<AtomicExpr>),
}

impl From<ComplexExpr> for Expr<()> {
    fn from(c: ComplexExpr) -> Self {
        match c {
            ComplexExpr::App(fun, arg) => {
                Expr::App((), Box::new(Expr::from(*fun)), Box::new(Expr::from(*arg)))
            }
            ComplexExpr::BinApp(fun, arg0, arg1) => Expr::BinApp(
                (),
                Box::new(Expr::from(*fun)),
                Box::new(Expr::from(*arg0)),
                Box::new(Expr::from(*arg1)),
            ),
            ComplexExpr::If(pred, conseq, alt) => Expr::If(
                (),
                Box::new(Expr::from(*pred)),
                Box::new(Expr::from(*conseq)),
                Box::new(Expr::from(*alt)),
            ),
            ComplexExpr::Map(fun, arr) => {
                Expr::Map((), Box::new(Expr::from(*fun)), Box::new(Expr::from(*arr)))
            }
            ComplexExpr::Reduce(fun, init, arr) => Expr::Reduce(
                (),
                Box::new(Expr::from(*fun)),
                Box::new(Expr::from(*init)),
                Box::new(Expr::from(*arr)),
            ),
            ComplexExpr::Scan(fun, init, arr) => Expr::Scan(
                (),
                Box::new(Expr::from(*fun)),
                Box::new(Expr::from(*init)),
                Box::new(Expr::from(*arr)),
            ),
            ComplexExpr::Iota(n) => Expr::Iota((), Box::new(Expr::from(*n))),
            ComplexExpr::Pair(e1, e2) => {
                Expr::Pair((), Box::new(Expr::from(*e1)), Box::new(Expr::from(*e2)))
            }
            ComplexExpr::Fst(p) => Expr::Fst((), Box::new(Expr::from(*p))),
            ComplexExpr::Snd(p) => Expr::Snd((), Box::new(Expr::from(*p))),
        }
    }
}

#[derive(Debug, Clone)]
pub enum NormalExpr {
    Let(Box<str>, Box<NormalExpr>, Box<NormalExpr>),
    Complex(ComplexExpr),
    Atomic(AtomicExpr),
}

impl From<NormalExpr> for Expr<()> {
    fn from(normal: NormalExpr) -> Self {
        match normal {
            NormalExpr::Let(arg, def, body) => Expr::Let(
                (),
                arg,
                Box::new(Expr::from(*def)),
                Box::new(Expr::from(*body)),
            ),
            NormalExpr::Atomic(a) => Expr::from(a),
            NormalExpr::Complex(c) => Expr::from(c),
        }
    }
}

#[derive(Debug)]
pub struct ANormalizer {
    fresh_vars: RefCell<usize>,
}

impl ANormalizer {
    pub fn new() -> Self {
        Self {
            fresh_vars: RefCell::new(0),
        }
    }

    fn gensym(&self) -> Box<str> {
        let mut count = self.fresh_vars.borrow_mut();
        *count += 1;
        format!("?t{}", count).into()
    }

    pub fn normalize_term<T>(&self, expr: &Expr<T>) -> Result<NormalExpr, Error> {
        self.normalize(expr, &|n| Ok(n))
    }

    fn normalize_name<T>(
        &self,
        expr: &Expr<T>,
        k: &dyn Fn(AtomicExpr) -> Result<NormalExpr, Error>,
    ) -> Result<NormalExpr, Error> {
        self.normalize(expr, &|n| match n {
            NormalExpr::Atomic(c @ AtomicExpr::Lambda(_, _)) => {
                let t = self.gensym();
                let body = k(AtomicExpr::Identifier(t.clone()))?;
                Ok(NormalExpr::Let(
                    t.clone(),
                    Box::new(NormalExpr::Atomic(c)),
                    Box::new(body),
                ))
            }
            NormalExpr::Atomic(c @ AtomicExpr::BinLambda(_, _, _)) => {
                let t = self.gensym();
                let body = k(AtomicExpr::Identifier(t.clone()))?;
                Ok(NormalExpr::Let(
                    t.clone(),
                    Box::new(NormalExpr::Atomic(c)),
                    Box::new(body),
                ))
            }
            NormalExpr::Atomic(a) => k(a),
            NormalExpr::Complex(c) => {
                let t = self.gensym();
                let body = k(AtomicExpr::Identifier(t.clone()))?;
                Ok(NormalExpr::Let(
                    t.clone(),
                    Box::new(NormalExpr::Complex(c)),
                    Box::new(body),
                ))
            }
            NormalExpr::Let(_, _, _) => {
                todo!()
            }
        })
    }

    fn normalize<T>(
        &self,
        expr: &Expr<T>,
        k: &dyn Fn(NormalExpr) -> Result<NormalExpr, Error>,
    ) -> Result<NormalExpr, Error> {
        match expr {
            Expr::BooleanLiteral(_, v) => {
                k(NormalExpr::Atomic(AtomicExpr::BooleanLiteral(v.clone())))
            }
            Expr::IntegerLiteral(_, v) => {
                k(NormalExpr::Atomic(AtomicExpr::IntegerLiteral(v.clone())))
            }
            Expr::FloatLiteral(_, v) => k(NormalExpr::Atomic(AtomicExpr::FloatLiteral(v.clone()))),
            Expr::Identifier(_, s) => k(NormalExpr::Atomic(AtomicExpr::Identifier(s.clone()))),
            Expr::Lambda(_, arg, body) => {
                let new_body = self.normalize_term(body)?;
                k(NormalExpr::Atomic(AtomicExpr::Lambda(
                    arg.clone(),
                    Box::new(new_body),
                )))
            }
            Expr::BinLambda(_, arg0, arg1, body) => {
                let new_body = self.normalize_term(body)?;
                k(NormalExpr::Atomic(AtomicExpr::BinLambda(
                    arg0.clone(),
                    arg1.clone(),
                    Box::new(new_body),
                )))
            }
            Expr::App(_, fun, arg) => self.normalize_name(fun, &|t0| {
                self.normalize_name(arg, &|t1| {
                    k(NormalExpr::Complex(ComplexExpr::App(
                        Box::new(t0.clone()),
                        Box::new(t1.clone()),
                    )))
                })
            }),
            Expr::BinApp(_, fun, arg0, arg1) => self.normalize_name(fun, &|t0| {
                self.normalize_name(arg0, &|t1| {
                    self.normalize_name(arg1, &|t2| {
                        k(NormalExpr::Complex(ComplexExpr::BinApp(
                            Box::new(t0.clone()),
                            Box::new(t1.clone()),
                            Box::new(t2.clone()),
                        )))
                    })
                })
            }),
            Expr::Let(_, arg, def, body) => self.normalize(def, &|n| {
                let new_body = self.normalize(body, k)?;
                Ok(NormalExpr::Let(
                    arg.clone(),
                    Box::new(n),
                    Box::new(new_body),
                ))
            }),
            Expr::If(_, pred, conseq, alt) => self.normalize_name(pred, &|t| {
                let m2 = self.normalize_term(conseq)?;
                let m3 = self.normalize_term(alt)?;
                k(NormalExpr::Complex(ComplexExpr::If(
                    Box::new(t.clone()),
                    Box::new(m2),
                    Box::new(m3),
                )))
            }),
            Expr::Map(_, fun, arr) => self.normalize_name(fun, &|t0| {
                self.normalize_name(arr, &|t1| {
                    k(NormalExpr::Complex(ComplexExpr::Map(
                        Box::new(t0.clone()),
                        Box::new(t1.clone()),
                    )))
                })
            }),
            Expr::Reduce(_, fun, init, arr) => self.normalize_name(fun, &|t0| {
                self.normalize_name(init, &|t1| {
                    self.normalize_name(arr, &|t2| {
                        k(NormalExpr::Complex(ComplexExpr::Reduce(
                            Box::new(t0.clone()),
                            Box::new(t1.clone()),
                            Box::new(t2.clone()),
                        )))
                    })
                })
            }),
            Expr::Scan(_, fun, init, arr) => self.normalize_name(fun, &|t0| {
                self.normalize_name(init, &|t1| {
                    self.normalize_name(arr, &|t2| {
                        k(NormalExpr::Complex(ComplexExpr::Scan(
                            Box::new(t0.clone()),
                            Box::new(t1.clone()),
                            Box::new(t2.clone()),
                        )))
                    })
                })
            }),
            Expr::Iota(_, n) => self.normalize_name(n, &|t0| {
                k(NormalExpr::Complex(ComplexExpr::Iota(Box::new(t0.clone()))))
            }),
            Expr::Pair(_, e1, e2) => self.normalize_name(e1, &|t0| {
                self.normalize_name(e2, &|t1| {
                    k(NormalExpr::Complex(ComplexExpr::Pair(
                        Box::new(t0.clone()),
                        Box::new(t1.clone()),
                    )))
                })
            }),
            Expr::Fst(_, e) => self.normalize_name(e, &|t0| {
                k(NormalExpr::Complex(ComplexExpr::Fst(Box::new(t0.clone()))))
            }),
            Expr::Snd(_, e) => self.normalize_name(e, &|t0| {
                k(NormalExpr::Complex(ComplexExpr::Snd(Box::new(t0.clone()))))
            }),
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::parser::sexpr::parser::SExpr;
    use crate::parser::Expr;

    #[test]
    fn test1() {
        let src: SExpr = "(lambda (x) 1)".parse().unwrap();
        let ex = Expr::parse(&src).unwrap();
        let _tex: NormalExpr = ANormalizer::new().normalize_term(&ex).unwrap();
    }

    #[test]
    fn test2() {
        let src: SExpr = "((lambda (x) x) 0)".parse().unwrap();
        let ex = Expr::parse(&src).unwrap();
        let _tex: NormalExpr = ANormalizer::new().normalize_term(&ex).unwrap();
    }

    #[test]
    fn test3() {
        let src: SExpr = "(if (> 1 0) false true)".parse().unwrap();
        let ex = Expr::parse(&src).unwrap();
        let _tex: NormalExpr = ANormalizer::new().normalize_term(&ex).unwrap();
    }

    #[test]
    fn test4() {
        let src: SExpr = "(let ((f (lambda (x) x))) (f (foo 10)))".parse().unwrap();
        let ex = Expr::parse(&src).unwrap();
        let _tex: NormalExpr = ANormalizer::new().normalize_term(&ex).unwrap();
    }

    #[test]
    fn test5() {
        let src: SExpr = "(let ((incr (lambda (u) (+ u 1)))) (let ((factorial (lambda (n) (reduce * 1 (map incr (iota n)))))) (factorial 6)))".parse().unwrap();
        let ex = Expr::parse(&src).unwrap();
        let _tex: NormalExpr = ANormalizer::new().normalize_term(&ex).unwrap();
    }
}
