pub mod alphatize;
pub mod anormalizer;

use crate::error::Error;
use crate::parser::Expr;

use alphatize::Alphatizer;
use anormalizer::ANormalizer;

use std::collections::HashMap;

pub fn compile(expr: &Expr) -> Result<Expr, Error> {
    let mut pass1 = Alphatizer::new();
    let a1 = pass1.alphatize(expr, &HashMap::new())?;

    let pass2 = ANormalizer::new();
    pass2.normalize_term(&a1).map(|x| Expr::from(x))
}
