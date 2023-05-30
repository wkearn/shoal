/// S-expression parsing
use crate::error::Error;

#[derive(Debug, PartialEq)]
pub enum SExpr {
    Atom(Box<str>),
    Boolean(bool),
    Integer(i64),
    Float(f64),
    List(Vec<SExpr>),
}

impl std::fmt::Display for SExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        match self {
            SExpr::Atom(s) => {
                write!(f, "{}", s)
            }
            SExpr::Boolean(v) => {
                write!(f, "{}", v)
            }
            SExpr::Integer(v) => {
                write!(f, "{}", v)
            }
            SExpr::Float(v) => {
                write!(f, "{}", v)
            }
            SExpr::List(vs) => {
                write!(
                    f,
                    "({})",
                    vs.iter()
                        .map(|x| { x.to_string() })
                        .collect::<Vec<String>>()
                        .join(" ")
                )
            }
        }
    }
}

impl std::str::FromStr for SExpr {
    type Err = Error;

    fn from_str(source: &str) -> Result<Self, Self::Err> {
        let mut tokens = source.chars().peekable();
        parse_token(&mut tokens)
    }
}

fn parse_token<I>(tokens: &mut std::iter::Peekable<I>) -> Result<SExpr, Error>
where
    I: Iterator<Item = char>,
{
    match tokens.next() {
        Some('(') => {
            // Start a new expression
            let mut v = Vec::new();
            while let Some(t2) = tokens.peek() {
                match t2 {
                    ')' => {
                        // Consume the right paren
                        tokens.next();
                        return Ok(SExpr::List(v));
                    }
                    _ => {
                        let t = parse_token(tokens)?;
                        v.push(t);
                    }
                }
            }
            Err(Error::SyntaxError("Unclosed s-expression".into()))
        }
        Some(')') => Err(Error::SyntaxError("Unmatched right parenthesis".into())),
        Some(c) => {
            if c.is_whitespace() {
                // Move to the next token
                parse_token(tokens)
            } else {
                let mut s = String::new();
                s.push(c);
                while let Some(t2) = tokens.peek() {
                    match t2 {
                        '(' => {
                            break;
                        }
                        ')' => {
                            break;
                        }
                        c => {
                            if c.is_whitespace() {
                                break;
                            } else {
                                s.push(*c);
                                // Consume token
                                tokens.next();
                            }
                        }
                    }
                }
		if let Ok(v) = s.parse() {
                    Ok(SExpr::Integer(v))
                } else if let Ok(v) = s.parse() {
                    Ok(SExpr::Float(v))
                } else {
                    match s.as_str() {
                        "true" => Ok(SExpr::Boolean(true)),
                        "false" => Ok(SExpr::Boolean(false)),
                        _ => Ok(SExpr::Atom(Box::from(s))),
                    }
                }
            }
        }
        None => Err(Error::SyntaxError("EOF".into())),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test1() {
        let SExpr::List(v) = "(foo 1 2.0)".parse().unwrap() else { panic!("Expected a list") };

        assert_eq!(SExpr::Atom("foo".into()), v[0]);
        assert_eq!(SExpr::Integer(1), v[1]);
        assert_eq!(SExpr::Float(2.0), v[2]);
    }

    #[test]
    fn test2() {
        let SExpr::List(v) = "(lambda (u v) (+ u v))".parse().unwrap() else { panic!("Expected a list") };

        assert_eq!(SExpr::Atom("lambda".into()), v[0]);

        match &v[1] {
            SExpr::List(w) => {
                assert_eq!(SExpr::Atom("u".into()), w[0]);
                assert_eq!(SExpr::Atom("v".into()), w[1]);
            }
            _ => panic!("Expected a list"),
        }

        match &v[2] {
            SExpr::List(w) => {
                assert_eq!(SExpr::Atom("+".into()), w[0]);
                assert_eq!(SExpr::Atom("u".into()), w[1]);
                assert_eq!(SExpr::Atom("v".into()), w[2]);
            }
            _ => panic!("Expected a list"),
        }
    }

    #[test]
    fn test3() {
        let SExpr::List(s) = "(let ((m 1.0))
                                   (+ m 2.0))".parse().unwrap() else { panic!("Expected a list") };

        assert_eq!(SExpr::Atom("let".into()), s[0]);

        match &s[1] {
            SExpr::List(t) => match &t[0] {
                SExpr::List(u) => {
                    assert_eq!(SExpr::Atom("m".into()), u[0]);
                    assert_eq!(SExpr::Float(1.0), u[1]);
                }
                _ => panic!("Expected a list"),
            },
            _ => panic!("Expected a list"),
        }

        match &s[2] {
            SExpr::List(t) => {
                assert_eq!(SExpr::Atom("+".into()), t[0]);
                assert_eq!(SExpr::Atom("m".into()), t[1]);
                assert_eq!(SExpr::Float(2.0), t[2]);
            }
            _ => panic!("Expected a list"),
        }
    }
}



