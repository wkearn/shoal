use crate::ast::Expr;
use crate::error::Error;

use std::rc::Rc;

#[derive(Debug)]
pub enum Token {
    LeftParen,
    RightParen,
    Number(f64),
    Atom(String),
}

impl std::str::FromStr for Token {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "(" => Ok(Token::LeftParen),
            ")" => Ok(Token::RightParen),
            _ => {
                if let Ok(v) = s.parse() {
                    Ok(Token::Number(v))
                } else {
                    Ok(Token::Atom(s.to_string()))
                }
            }
        }
    }
}

pub fn lex(s: &str) -> Vec<Result<Token, Error>> {
    s.replace('(', " ( ")
        .replace(')', " ) ")
        .split_whitespace()
        .map(|s| s.parse())
        .collect()
}

// Parsing

fn parse_token<I>(tokens: &mut std::iter::Peekable<I>) -> Result<Expr, Error>
where
    I: Iterator<Item = Token>,
{
    match tokens.next() {
        Some(Token::LeftParen) => {
            let mut v = Vec::new();
            while let Some(t2) = tokens.peek() {
                match t2 {
                    Token::RightParen => {
                        // Consume the right paren
                        tokens.next();

                        // Return the accumulated expression
                        return Ok(Expr::List(v));
                    }
                    _ => {
                        // Recursively parse the next token
                        let t = parse_token(tokens)?;

                        // Push the token onto the expression
                        v.push(Rc::new(t));
                    }
                }
            }
            Err(Error::ParseError)
        }
        Some(Token::RightParen) => Err(Error::ParseError),
        Some(Token::Number(v)) => Ok(Expr::Number(v)),
        Some(Token::Atom(s)) => match s.as_str() {
            "true" => Ok(Expr::Boolean(true)),
            "false" => Ok(Expr::Boolean(false)),
            _ => Ok(Expr::Atom(s)),
        },
        None => Err(Error::ParseError),
    }
}

pub fn parse(ts: Vec<Token>) -> Result<Expr, Error> {
    parse_token(&mut ts.into_iter().peekable())
}
