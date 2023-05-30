/// S-expression parsing
use crate::error::Error;

#[derive(Debug, PartialEq, Clone, Copy)]
pub struct Position {
    line: usize,
    col: usize,
}

impl Position {
    fn new(line: usize, col: usize) -> Self {
        Position { line, col }
    }

    fn increment_column(&mut self) {
        self.col += 1;
    }

    fn increment_line(&mut self) {
        self.line += 1;
        self.col = 0;
    }
}

impl std::fmt::Display for Position {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(f, "{}:{}", self.line, self.col)
    }
}

#[derive(Debug, PartialEq)]
pub enum SExpr {
    Atom(Box<str>, Position, Position),
    Boolean(bool, Position, Position),
    Integer(i64, Position, Position),
    Float(f64, Position, Position),
    List(Vec<SExpr>, Position, Position),
}

impl std::fmt::Display for SExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        match self {
            SExpr::Atom(s, _, _) => {
                write!(f, "{}", s)
            }
            SExpr::Boolean(v, _, _) => {
                write!(f, "{}", v)
            }
            SExpr::Integer(v, _, _) => {
                write!(f, "{}", v)
            }
            SExpr::Float(v, _, _) => {
                write!(f, "{}", v)
            }
            SExpr::List(vs, _, _) => {
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
        let (_, sexpr) = parse_token(&mut tokens, Position::new(1, 0))?;
        Ok(sexpr)
    }
}

fn parse_token<I>(
    tokens: &mut std::iter::Peekable<I>,
    pos: Position,
) -> Result<(Position, SExpr), Error>
where
    I: Iterator<Item = char>,
{
    let mut local_pos = pos.clone();
    match tokens.next() {
        Some('(') => {
            // Start a new expression
            let start_pos = local_pos.clone();
            let mut v = Vec::new();
            while let Some(t2) = tokens.peek() {
                match t2 {
                    ')' => {
                        // Consume the right paren
                        tokens.next();
                        local_pos.increment_column();
                        return Ok((local_pos, SExpr::List(v, start_pos, local_pos)));
                    }
                    _ => {
                        local_pos.increment_column();
                        let (new_pos, t) = parse_token(tokens, local_pos)?;
                        local_pos = new_pos;
                        v.push(t);
                    }
                }
            }
            Err(Error::SyntaxError(format!(
                "[{local_pos}]: Unclosed s-expression begins at [{start_pos}]"
            )))
        }
        Some(')') => Err(Error::SyntaxError(format!(
            "[line: {local_pos}]: Unmatched right parenthesis"
        ))),
        Some(c) => {
            if c.is_whitespace() {
                // Move to the next token
                if c == '\n' {
                    local_pos.increment_line();
                    parse_token(tokens, local_pos)
                } else {
                    local_pos.increment_column();
                    parse_token(tokens, local_pos)
                }
            } else {
                let start_pos = local_pos.clone();
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
                                if c == &'\n' {
                                    local_pos.increment_line();
                                }
                                break;
                            } else {
                                s.push(*c);
                                // Consume token
                                tokens.next();
                                local_pos.increment_column();
                            }
                        }
                    }
                }
                if let Ok(v) = s.parse() {
                    Ok((local_pos, SExpr::Integer(v, start_pos, local_pos)))
                } else if let Ok(v) = s.parse() {
                    Ok((local_pos, SExpr::Float(v, start_pos, local_pos)))
                } else {
                    match s.as_str() {
                        "true" => Ok((local_pos, SExpr::Boolean(true, start_pos, local_pos))),
                        "false" => Ok((local_pos, SExpr::Boolean(false, start_pos, local_pos))),
                        _ => Ok((local_pos, SExpr::Atom(Box::from(s), start_pos, local_pos))),
                    }
                }
            }
        }
        None => Err(Error::SyntaxError(format!(
            "[{local_pos}]: unexpected end of file"
        ))),
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test1() {
        let s: SExpr = "(foo 10 2.0)".parse().unwrap();

        match s {
            SExpr::List(v, start_pos, end_pos) => {
                assert_eq!(Position::new(1, 0), start_pos);

                match &v[0] {
                    SExpr::Atom(s, x1, x2) => {
                        assert_eq!("foo", &**s);
                        assert_eq!(&Position::new(1, 1), x1);
                        assert_eq!(&Position::new(1, 3), x2)
                    }
                    _ => panic!("Expected an atom"),
                }

                match &v[1] {
                    SExpr::Integer(v, x1, x2) => {
                        assert_eq!(10, *v);
                        assert_eq!(&Position::new(1, 5), x1);
                        assert_eq!(&Position::new(1, 6), x2);
                    }
                    _ => panic!("Expected an integer"),
                }

                match &v[2] {
                    SExpr::Float(v, x1, x2) => {
                        assert_eq!(2.0, *v);
                        assert_eq!(&Position::new(1, 8), x1);
                        assert_eq!(&Position::new(1, 10), x2);
                    }
                    _ => panic!("Expected an integer"),
                }

                assert_eq!(Position::new(1, 11), end_pos);
            }
            _ => panic!("Expected a list"),
        }
    }

    #[test]
    fn test2() {
        let SExpr::List(s,start_pos,end_pos) = "(lambda (u v) (+ u v))".parse().unwrap() else {panic!("Expected a list")};

        assert_eq!(Position::new(1, 0), start_pos);
        assert_eq!(Position::new(1, 21), end_pos);

        match &s[0] {
            SExpr::Atom(t, x1, x2) => {
                assert_eq!("lambda", &**t);
                assert_eq!(&Position::new(1, 1), x1);
                assert_eq!(&Position::new(1, 6), x2);
            }
            _ => panic!("Expected atom"),
        }

        match &s[1] {
            SExpr::List(t, x1, x2) => {
                match &t[0] {
                    SExpr::Atom(u, y1, y2) => {
                        assert_eq!("u", &**u);
                        assert_eq!(&Position::new(1, 9), y1);
                        assert_eq!(&Position::new(1, 9), y2)
                    }
                    _ => panic!("Expected Atom"),
                }

                match &t[1] {
                    SExpr::Atom(u, y1, y2) => {
                        assert_eq!("v", &**u);
                        assert_eq!(&Position::new(1, 11), y1);
                        assert_eq!(&Position::new(1, 11), y2)
                    }
                    _ => panic!("Expected Atom"),
                }
                assert_eq!(&Position::new(1, 8), x1);
                assert_eq!(&Position::new(1, 12), x2);
            }
            _ => panic!("Expected list"),
        }

        match &s[2] {
            SExpr::List(t, x1, x2) => {
                match &t[0] {
                    SExpr::Atom(u, y1, y2) => {
                        assert_eq!("+", &**u);
                        assert_eq!(&Position::new(1, 15), y1);
                        assert_eq!(&Position::new(1, 15), y2)
                    }
                    _ => panic!("Expected Atom"),
                }

                match &t[1] {
                    SExpr::Atom(u, y1, y2) => {
                        assert_eq!("u", &**u);
                        assert_eq!(&Position::new(1, 17), y1);
                        assert_eq!(&Position::new(1, 17), y2)
                    }
                    _ => panic!("Expected Atom"),
                }

                match &t[2] {
                    SExpr::Atom(u, y1, y2) => {
                        assert_eq!("v", &**u);
                        assert_eq!(&Position::new(1, 19), y1);
                        assert_eq!(&Position::new(1, 19), y2)
                    }
                    _ => panic!("Expected Atom"),
                }
                assert_eq!(&Position::new(1, 14), x1);
                assert_eq!(&Position::new(1, 20), x2);
            }
            _ => panic!("Expected list"),
        }
    }

    #[test]
    fn test3() {
        let SExpr::List(_,start_pos,end_pos) = "(let ((m 1.0))
                                                     (+ m 2.0))".parse().unwrap() else {panic!("Expected a list") };

        assert_eq!(Position::new(1, 0), start_pos);
        assert_eq!(Position::new(2, 62), end_pos);
    }

    #[test]
    fn error1() {
        "(foo 1.0 2.0".parse::<SExpr>().unwrap_err();
        ")".parse::<SExpr>().unwrap_err();

        // Mismatched parentheses across lines
        "(let ((m 1.0))
              (+ m 2.0)"
            .parse::<SExpr>()
            .unwrap_err();
    }
}
