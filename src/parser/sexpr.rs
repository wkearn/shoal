/// S-expression parsing
use crate::error::Error;

#[derive(Debug, PartialEq, Clone, Copy)]
pub struct Position {
    line: usize,
    col: usize
}

impl Position {
    fn new(line: usize, col: usize) -> Self {
	Position {line, col}
    }
}

impl std::fmt::Display for Position {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(),std::fmt::Error> {
	write!(f,"{}:{}",self.line, self.col)
    }
}

#[derive(Debug, PartialEq)]
pub enum SExpr {
    Atom(Box<str>,Position,Position),
    Boolean(bool,Position,Position),
    Integer(i64,Position,Position),
    Float(f64,Position,Position),
    List(Vec<SExpr>,Position,Position),
}

impl std::fmt::Display for SExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        match self {
            SExpr::Atom(s,_,_) => {
                write!(f, "{}", s)
            }
            SExpr::Boolean(v,_,_) => {
                write!(f, "{}", v)
            }
            SExpr::Integer(v,_,_) => {
                write!(f, "{}", v)
            }
            SExpr::Float(v,_,_) => {
                write!(f, "{}", v)
            }
            SExpr::List(vs,_,_) => {
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
        let (_,sexpr) = parse_token(&mut tokens,Position::new(1,0))?;
	Ok(sexpr)
    }
}

fn parse_token<I>(tokens: &mut std::iter::Peekable<I>,pos: Position) -> Result<(Position,SExpr), Error>
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
			local_pos.col += 1;
                        return Ok((local_pos,SExpr::List(v,start_pos,local_pos)));
                    }
                    _ => {
			local_pos.col += 1;
                        let (new_pos,t) = parse_token(tokens,local_pos)?;
			local_pos = new_pos;
                        v.push(t);
                    }
                }
            }
            Err(Error::SyntaxError(format!("[{local_pos}]: Unclosed s-expression begins at [{start_pos}]")))
        }
        Some(')') => Err(Error::SyntaxError(format!("[line: {local_pos}]: Unmatched right parenthesis"))),
        Some(c) => {
            if c.is_whitespace() {
                // Move to the next token
		if c == '\n' {
		    local_pos.line += 1;
		    local_pos.col = 0;
		    parse_token(tokens,local_pos)
		} else {
		    local_pos.col += 1;
		    parse_token(tokens,local_pos)
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
				    local_pos.line += 1;
				    local_pos.col = 0;
				}
                                break;
                            } else {
                                s.push(*c);
                                // Consume token
                                tokens.next();
				local_pos.col += 1;
                            }
                        }
                    }
                }
		if let Ok(v) = s.parse() {
                    Ok((local_pos,SExpr::Integer(v,start_pos,local_pos)))
                } else if let Ok(v) = s.parse() {
                    Ok((local_pos,SExpr::Float(v,start_pos,local_pos)))
                } else {
                    match s.as_str() {
                        "true" => Ok((local_pos,SExpr::Boolean(true,start_pos,local_pos))),
                        "false" => Ok((local_pos,SExpr::Boolean(false,start_pos,local_pos))),
                        _ => Ok((local_pos,SExpr::Atom(Box::from(s),start_pos,local_pos))),
                    }
                }
            }
        }
        None => Err(Error::SyntaxError(format!("[{local_pos}]: unexpected end of file"))),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test1() {
        let s: SExpr = "(foo 1 2.0)".parse().unwrap();
    }

    #[test]
    fn test2() {
        let s: SExpr = "(lambda (u v) (+ u v))".parse().unwrap();
    }


    #[test]
    fn test3() {
        let s: SExpr = "(let ((m 1.0))
                             (+ m 2.0))".parse().unwrap();
    }

    #[test]
    fn error1() {
	"(foo 1.0 2.0".parse::<SExpr>().unwrap_err();
	")".parse::<SExpr>().unwrap_err();

	// Mismatched parentheses across lines
	"(let ((m 1.0))
              (+ m 2.0)".parse::<SExpr>().unwrap();
    }
}








