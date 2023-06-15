use crate::error::Error;
use crate::parser::{Expr, Program, Statement};

use std::collections::HashMap;

#[derive(Debug, Default)]
pub struct Alphatizer {
    fresh_vars: usize,
}

impl Alphatizer {
    pub fn new() -> Self {
        Self::default()
    }

    fn gensym(&mut self) -> Box<str> {
        self.fresh_vars += 1;
        format!("?a{}", self.fresh_vars).into()
    }

    pub fn alphatize<T: Clone>(
        &mut self,
        expr: &Expr<T>,
        env: &HashMap<Box<str>, Box<str>>,
    ) -> Expr<T> {
        match expr {
            Expr::BooleanLiteral(tag, v) => Expr::BooleanLiteral(tag.clone(), v.clone()),
            Expr::IntegerLiteral(tag, v) => Expr::IntegerLiteral(tag.clone(), v.clone()),
            Expr::FloatLiteral(tag, v) => Expr::FloatLiteral(tag.clone(), v.clone()),
            Expr::Identifier(tag, s) => {
                // Look up the identifier in the environment
                // If it is found, substitute it, otherwise leave it as is
                env.get(s)
                    .map_or(Expr::Identifier(tag.clone(), s.clone()), |v| {
                        Expr::Identifier(tag.clone(), v.clone())
                    })
            }
            Expr::Lambda(tag, arg, body) => {
                let t0 = self.gensym();
                let new_body = {
                    let mut local_env = HashMap::new(); // Create a new local environment
                                                        // Add existing environment entries
                    local_env.extend(env.iter().map(|(k, v)| (k.clone(), v.clone())));
                    local_env.insert(arg.clone(), t0.clone()); // Bind the function args
                    self.alphatize(body, &local_env)
                };

                Expr::Lambda(tag.clone(), t0, Box::new(new_body))
            }
            Expr::BinLambda(tag, arg0, arg1, body) => {
                let t0 = self.gensym();
                let t1 = self.gensym();
                let new_body = {
                    let mut local_env = HashMap::new(); // Create a new local environment
                                                        // Add existing environment entries
                    local_env.extend(env.iter().map(|(k, v)| (k.clone(), v.clone())));
                    local_env.insert(arg0.clone(), t0.clone()); // Bind the function args
                    local_env.insert(arg1.clone(), t1.clone()); // Bind the function args
                    self.alphatize(body, &local_env)
                };

                Expr::BinLambda(tag.clone(), t0, t1, Box::new(new_body))
            }
            Expr::App(tag, fun, arg) => Expr::App(
                tag.clone(),
                Box::new(self.alphatize(fun, env)),
                Box::new(self.alphatize(arg, env)),
            ),
            Expr::BinApp(tag, fun, arg0, arg1) => Expr::BinApp(
                tag.clone(),
                Box::new(self.alphatize(fun, env)),
                Box::new(self.alphatize(arg0, env)),
                Box::new(self.alphatize(arg1, env)),
            ),
            Expr::Let(tag, arg, def, body) => {
                let t0 = self.gensym();
                let new_def = self.alphatize(def, env);
                let new_body = {
                    let mut local_env = HashMap::new(); // Create a new local environment
                                                        // Add existing environment entries
                    local_env.extend(env.iter().map(|(k, v)| (k.clone(), v.clone())));
                    local_env.insert(arg.clone(), t0.clone()); // Bind the function args
                    self.alphatize(body, &local_env)
                };

                Expr::Let(tag.clone(), t0, Box::new(new_def), Box::new(new_body))
            }
            Expr::If(tag, pred, conseq, alt) => Expr::If(
                tag.clone(),
                Box::new(self.alphatize(pred, env)),
                Box::new(self.alphatize(conseq, env)),
                Box::new(self.alphatize(alt, env)),
            ),
            Expr::Map(tag, fun, arr) => Expr::Map(
                tag.clone(),
                Box::new(self.alphatize(fun, env)),
                Box::new(self.alphatize(arr, env)),
            ),
            Expr::Reduce(tag, fun, init, arr) => Expr::Reduce(
                tag.clone(),
                Box::new(self.alphatize(fun, env)),
                Box::new(self.alphatize(init, env)),
                Box::new(self.alphatize(arr, env)),
            ),
            Expr::Scan(tag, fun, init, arr) => Expr::Scan(
                tag.clone(),
                Box::new(self.alphatize(fun, env)),
                Box::new(self.alphatize(init, env)),
                Box::new(self.alphatize(arr, env)),
            ),
            Expr::Iota(tag, n) => Expr::Iota(tag.clone(), Box::new(self.alphatize(n, env))),
            Expr::Pair(tag, e1, e2) => Expr::Pair(
                tag.clone(),
                Box::new(self.alphatize(e1, env)),
                Box::new(self.alphatize(e2, env)),
            ),
            Expr::Fst(tag, e) => Expr::Fst(tag.clone(), Box::new(self.alphatize(e, env))),
            Expr::Snd(tag, e) => Expr::Snd(tag.clone(), Box::new(self.alphatize(e, env))),
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
        let _tex = Alphatizer::new().alphatize(&ex, &HashMap::new());
    }

    #[test]
    fn test2() {
        let src: SExpr = "((lambda (x) x) 0)".parse().unwrap();
        let ex = Expr::parse(&src).unwrap();
        let _tex = Alphatizer::new().alphatize(&ex, &HashMap::new());
    }

    #[test]
    fn test3() {
        let src: SExpr = "(let ((f (lambda (x) x))) (f (foo 10)))".parse().unwrap();
        let ex = Expr::parse(&src).unwrap();

        let _tex = Alphatizer::new().alphatize(&ex, &HashMap::new());
    }
}
