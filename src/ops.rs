use crate::error::Error;
use crate::parser::Expr;

use std::rc::Rc;

pub enum NumericBinaryOp {
    Add,
    Sub,
    Mul,
    Div,
    GreaterThan,
    GreaterThanOrEqual,
    LessThan,
    LessThanOrEqual,
    Min,
    Max,
}

impl NumericBinaryOp {
    pub fn apply(&self, args: &[Rc<Expr>]) -> Result<Expr, Error> {
        let a1 = args.get(0).ok_or(Error::SyntaxError(format!(
            "Binary operator expects two arguments"
        )))?;
        let a2 = args.get(1).ok_or(Error::SyntaxError(format!(
            "Binary operator expects two arguments"
        )))?;
        if let Expr::Number(x) = **a1 {
            if let Expr::Number(y) = **a2 {
                match self {
                    NumericBinaryOp::Add => Ok(Expr::Number(x + y)),
                    NumericBinaryOp::Sub => Ok(Expr::Number(x - y)),
                    NumericBinaryOp::Mul => Ok(Expr::Number(x * y)),
                    NumericBinaryOp::Div => Ok(Expr::Number(x / y)),
                    NumericBinaryOp::GreaterThan => Ok(Expr::Boolean(x > y)),
                    NumericBinaryOp::GreaterThanOrEqual => Ok(Expr::Boolean(x >= y)),
                    NumericBinaryOp::LessThan => Ok(Expr::Boolean(x < y)),
                    NumericBinaryOp::LessThanOrEqual => Ok(Expr::Boolean(x <= y)),
                    NumericBinaryOp::Min => Ok(Expr::Number(x.min(y))),
                    NumericBinaryOp::Max => Ok(Expr::Number(x.max(y))),
                }
            } else {
                Err(Error::SyntaxError(format!(
                    "Second argument of binary operator should be numeric"
                )))
            }
        } else {
            Err(Error::SyntaxError(format!(
                "First argument of binary operator should be numeric"
            )))
        }
    }
}

pub enum NumericUnaryOp {
    Inv,
    Exp,
    Log,
    Sin,
    Cos,
    Tan,
    Abs,
}

impl NumericUnaryOp {
    pub fn apply(&self, args: &[Rc<Expr>]) -> Result<Expr, Error> {
        let a1 = args.get(0).ok_or(Error::SyntaxError(format!(
            "Unary operator expects one argument"
        )))?;
        if let Expr::Number(x) = **a1 {
            match self {
                NumericUnaryOp::Inv => Ok(Expr::Number(1.0 / x)),
                NumericUnaryOp::Exp => Ok(Expr::Number(x.exp())),
                NumericUnaryOp::Log => Ok(Expr::Number(x.ln())),
                NumericUnaryOp::Sin => Ok(Expr::Number(x.sin())),
                NumericUnaryOp::Cos => Ok(Expr::Number(x.cos())),
                NumericUnaryOp::Tan => Ok(Expr::Number(x.tan())),
                NumericUnaryOp::Abs => Ok(Expr::Number(x.abs())),
            }
        } else {
            Err(Error::SyntaxError(format!(
                "Argument of unary operator should be numeric"
            )))
        }
    }
}
