use crate::error::Error;

use std::cell::{RefMut,RefCell};
use std::collections::HashMap;
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

pub struct Env(Rc<Scope>);

impl Env {
    pub fn new(scope: Rc<Scope>) -> Self {
        Self(scope)
    }

    pub fn get(&self, k: &str) -> Option<Rc<Expr>> {
        self.0.get(k)
    }

    pub fn insert(&self, k: String, v: Rc<Expr>) {
        self.0.insert(k, v)
    }

    pub fn clone(&self) -> Self {
	Self(self.0.clone())
    }

    pub fn borrow_bindings(&self) -> RefMut<'_,HashMap<String,Rc<Expr>>> {
	self.0.bindings.borrow_mut()
    }
}

// A scope owns a set of bindings and holds a reference counted
// pointer to its parent environment.
// The hash map needs to store Rc pointers, because the expressions
// might get shared around.
// The hash map also needs to be in a RefCell, because we may want to
// update the bindings from a child scope.
pub struct Scope {
    bindings: RefCell<HashMap<String, Rc<Expr>>>,
    parent: Option<Env>,
}

impl Scope {
    pub fn new(bindings: RefCell<HashMap<String, Rc<Expr>>>, parent: Option<Env>) -> Self {
        Self { bindings, parent }
    }

    pub fn get(&self, k: &str) -> Option<Rc<Expr>> {
        match self.bindings.borrow().get(k) {
            Some(expr) => Some(expr.clone()),
            None => match &self.parent {
                Some(parent) => parent.get(k),
                None => None,
            },
        }
    }

    pub fn insert(&self, k: String, v: Rc<Expr>) {
        self.bindings.borrow_mut().insert(k, v);
    }
}

pub enum Expr {
    Atom(String),
    Boolean(bool),
    Number(f64),
    List(Vec<Rc<Expr>>),
    PrimitiveFunc(Box<dyn Fn(&[Rc<Expr>]) -> Result<Expr, Error>>),
    Func {
        params: Vec<String>,
        env: Env,
        body: Rc<Expr>,
    },
}

impl std::fmt::Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        match self {
            Expr::Atom(s) => write!(f, "{}", s),
            Expr::Boolean(s) => write!(f, "{}", s),
            Expr::Number(v) => write!(f, "{}", v),
            Expr::List(vs) => write!(
                f,
                "({})",
                vs.into_iter()
                    .map(|x| { x.to_string() })
                    .collect::<Vec<String>>()
                    .join(" ")
            ),
            Expr::PrimitiveFunc(_) => write!(f, "primitive"),
            Expr::Func { params, .. } => write!(f, "(lambda ({}))", params.join(" ")),
        }
    }
}

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
