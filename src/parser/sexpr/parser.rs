use crate::error::Error;
use crate::parser::sexpr::lexer::{self, Position, Token, TokenKind};

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
        let tokens = lexer::lex(source);
        let mut parser = Parser::new(tokens);
        parser.datum()
    }
}

#[derive(Default)]
struct Parser {
    pos: usize,
    tokens: Vec<Token>,
}

impl Parser {
    pub fn new(tokens: Vec<Token>) -> Self {
        Self { pos: 0, tokens }
    }

    fn at(&self, kind: &TokenKind) -> bool {
        self.tokens
            .get(self.pos)
            .map_or(&TokenKind::Eof, |t| &t.kind)
            == kind
    }

    fn accept(&mut self, kind: &TokenKind) -> bool {
        if self.at(kind) {
            self.pos += 1;
            true
        } else {
            false
        }
    }

    fn expect(&mut self, kind: &TokenKind) -> Result<(), Error> {
        if self.accept(kind) {
            Ok(())
        } else {
	    let found = self.tokens
		.get(self.pos)
		.map_or(&TokenKind::Eof, |t| &t.kind);
            Err(Error::SyntaxError(format!("Expected token {kind}, found token: {found}")))
        }
    }

    fn datum(&mut self) -> Result<SExpr, Error> {
        if self.at(&TokenKind::LeftParen) {
            let Some(Token {kind: TokenKind::LeftParen, start_pos, ..}) = self.tokens.get(self.pos) else {
		// Should be unreachable because we just confirmed that we hit a LeftParen
		unreachable!()
	    };
	    self.pos += 1;
            let v = self.list(*start_pos)?;
            self.expect(&TokenKind::RightParen)?;
            Ok(v)
        } else {
            let v = self.simple()?;
            Ok(v)
        }
    }

    fn list(&mut self, start_pos: Position) -> Result<SExpr, Error> {
        let mut v = Vec::new();
        while !self.at(&TokenKind::RightParen) {
            let e = self.datum()?;
            v.push(e);
        }
	let Some(Token {kind: TokenKind::RightParen, end_pos, ..}) = self.tokens.get(self.pos) else {
	    // Should be unreachable because we just confirmed that we hit a LeftParen
	    unreachable!()
	};
        Ok(SExpr::List(v, start_pos,*end_pos))
    }

    fn simple(&mut self) -> Result<SExpr, Error> {
        let t = self.tokens.get(self.pos).ok_or(Error::SyntaxError("Unexpected end of file".into()))?;
        self.pos += 1;

        if let Some(data) = &t.data {
            if let Ok(v) = data.parse() {
                Ok(SExpr::Integer(v, t.start_pos, t.end_pos))
            } else if let Ok(v) = data.parse() {
                Ok(SExpr::Float(v, t.start_pos, t.end_pos))
            } else if "true" == &**data {
                Ok(SExpr::Boolean(true, t.start_pos, t.end_pos))
            } else if "false" == &**data {
                Ok(SExpr::Boolean(false, t.start_pos, t.end_pos))
            } else {
                Ok(SExpr::Atom(data.clone(), t.start_pos, t.end_pos))
            }
        } else {
            Err(Error::SyntaxError(format!("[{}]: Expected <string> token, found {}",t.start_pos,t.kind)))
        }
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

    #[test]
    fn extra_whitespace() {
        let SExpr::List(_,start_pos,end_pos) = "(+ 1 2 )"
            .parse()
            .unwrap() else { panic!("Expected a list") };

        assert_eq!(Position::new(1, 0), start_pos);
        assert_eq!(Position::new(1, 7), end_pos);

        let SExpr::List(_,start_pos,end_pos) = "(+ 1 2
)"
            .parse()
            .unwrap() else { panic!("Expected a list") };

        assert_eq!(Position::new(1, 0), start_pos);
        assert_eq!(Position::new(2, 0), end_pos);
    }

    #[test]
    fn easy_list() {
        let SExpr::List(vs,start_pos,end_pos) = "(one)"
            .parse()
            .unwrap() else { panic!("Expected a list") };

        assert_eq!(Position::new(1, 0), start_pos);
        assert_eq!(Position::new(1, 4), end_pos);

        match &vs[0] {
            SExpr::Atom(s, vstart, vend) => {
                assert_eq!(&**s, "one");
                assert_eq!(&Position::new(1, 1), vstart);
                assert_eq!(&Position::new(1, 3), vend);
            }
            _ => panic!("Expected atom"),
        }
    }

    #[test]
    fn easy_list_whitespace() {
        println!("Initial whitespace");
        let SExpr::List(vs,start_pos,end_pos) = "( one)"
            .parse()
            .unwrap() else { panic!("Expected a list") };

        assert_eq!(Position::new(1, 0), start_pos);
        assert_eq!(Position::new(1, 5), end_pos);

        match &vs[0] {
            SExpr::Atom(s, vstart, vend) => {
                assert_eq!(&**s, "one");
                assert_eq!(&Position::new(1, 2), vstart);
                assert_eq!(&Position::new(1, 4), vend);
            }
            _ => panic!("Expected atom"),
        }

        println!("Final whitespace");
        let SExpr::List(vs,start_pos,end_pos) = "(one )"
            .parse()
            .unwrap() else { panic!("Expected a list") };

        assert_eq!(Position::new(1, 0), start_pos);
        assert_eq!(Position::new(1, 5), end_pos);

        match &vs[0] {
            SExpr::Atom(s, vstart, vend) => {
                assert_eq!(&**s, "one");
                assert_eq!(&Position::new(1, 1), vstart);
                assert_eq!(&Position::new(1, 3), vend);
            }
            _ => panic!("Expected atom"),
        }
    }
}
