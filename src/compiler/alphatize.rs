use crate::error::Error;
use crate::parser::Expr;

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

    pub fn alphatize<T>(
        &mut self,
        expr: &Expr<T>,
        env: &HashMap<Box<str>, Box<str>>,
    ) -> Result<Expr<T>, Error> {
        match expr {
            Expr::BooleanLiteral(v) => Ok(Expr::BooleanLiteral(v.clone())),
            Expr::IntegerLiteral(v) => Ok(Expr::IntegerLiteral(v.clone())),
            Expr::FloatLiteral(v) => Ok(Expr::FloatLiteral(v.clone())),
            Expr::Identifier(s) => {
                // Look up the identifier in the environment
                // If it is found, substitute it, otherwise leave it as is
                env.get(s).map_or(Ok(Expr::Identifier(s.clone())), |v| {
                    Ok(Expr::Identifier(v.clone()))
                })
            }
            Expr::Lambda(arg, body) => {
                let t0 = self.gensym();
                let new_body = {
                    let mut local_env = HashMap::new(); // Create a new local environment
                                                        // Add existing environment entries
                    local_env.extend(env.iter().map(|(k, v)| (k.clone(), v.clone())));
                    local_env.insert(arg.clone(), t0.clone()); // Bind the function args
                    self.alphatize(body, &local_env)
                }?;

                Ok(Expr::Lambda(t0, Box::new(new_body)))
            }
            Expr::BinLambda(arg0, arg1, body) => {
                let t0 = self.gensym();
                let t1 = self.gensym();
                let new_body = {
                    let mut local_env = HashMap::new(); // Create a new local environment
                                                        // Add existing environment entries
                    local_env.extend(env.iter().map(|(k, v)| (k.clone(), v.clone())));
                    local_env.insert(arg0.clone(), t0.clone()); // Bind the function args
                    local_env.insert(arg1.clone(), t1.clone()); // Bind the function args
                    self.alphatize(body, &local_env)
                }?;

                Ok(Expr::BinLambda(t0, t1, Box::new(new_body)))
            }
            Expr::App(fun, arg) => Ok(Expr::App(
                Box::new(self.alphatize(fun, env)?),
                Box::new(self.alphatize(arg, env)?),
            )),
            Expr::BinApp(fun, arg0, arg1) => Ok(Expr::BinApp(
                Box::new(self.alphatize(fun, env)?),
                Box::new(self.alphatize(arg0, env)?),
                Box::new(self.alphatize(arg1, env)?),
            )),
            Expr::Let(arg, def, body) => {
                let t0 = self.gensym();
                let new_def = self.alphatize(def, env)?;
                let new_body = {
                    let mut local_env = HashMap::new(); // Create a new local environment
                                                        // Add existing environment entries
                    local_env.extend(env.iter().map(|(k, v)| (k.clone(), v.clone())));
                    local_env.insert(arg.clone(), t0.clone()); // Bind the function args
                    self.alphatize(body, &local_env)
                }?;

                Ok(Expr::Let(t0, Box::new(new_def), Box::new(new_body)))
            }
            Expr::If(pred, conseq, alt) => Ok(Expr::If(
                Box::new(self.alphatize(pred, env)?),
                Box::new(self.alphatize(conseq, env)?),
                Box::new(self.alphatize(alt, env)?),
            )),
            Expr::Map(fun, arr) => Ok(Expr::Map(
                Box::new(self.alphatize(fun, env)?),
                Box::new(self.alphatize(arr, env)?),
            )),
            Expr::Reduce(fun, init, arr) => Ok(Expr::Reduce(
                Box::new(self.alphatize(fun, env)?),
                Box::new(self.alphatize(init, env)?),
                Box::new(self.alphatize(arr, env)?),
            )),
            Expr::Scan(fun, init, arr) => Ok(Expr::Scan(
                Box::new(self.alphatize(fun, env)?),
                Box::new(self.alphatize(init, env)?),
                Box::new(self.alphatize(arr, env)?),
            )),
            Expr::Iota(n) => Ok(Expr::Iota(Box::new(self.alphatize(n, env)?))),
            Expr::Pair(e1, e2) => Ok(Expr::Pair(
                Box::new(self.alphatize(e1, env)?),
                Box::new(self.alphatize(e2, env)?),
            )),
            Expr::Fst(e) => Ok(Expr::Fst(Box::new(self.alphatize(e, env)?))),
            Expr::Snd(e) => Ok(Expr::Snd(Box::new(self.alphatize(e, env)?))),
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
        let ex: Expr = Expr::parse(&src).unwrap();
        let _tex: Expr = Alphatizer::new().alphatize(&ex, &HashMap::new()).unwrap();
    }

    #[test]
    fn test2() {
        let src: SExpr = "((lambda (x) x) 0)".parse().unwrap();
        let ex: Expr = Expr::parse(&src).unwrap();
        let _tex: Expr = Alphatizer::new().alphatize(&ex, &HashMap::new()).unwrap();
    }

    #[test]
    fn test3() {
        let src: SExpr = "(let ((f (lambda (x) x))) (f (foo 10)))".parse().unwrap();
        let ex: Expr = Expr::parse(&src).unwrap();

        let _tex: Expr = Alphatizer::new().alphatize(&ex, &HashMap::new()).unwrap();
    }
}
