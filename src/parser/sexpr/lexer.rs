#[derive(Debug, PartialEq, Clone, Copy)]
pub struct Position {
    line: usize,
    col: usize,
}

impl Position {
    pub fn new(line: usize, col: usize) -> Self {
        Position { line, col }
    }

    pub fn increment_column(&mut self) {
        self.col += 1;
    }

    pub fn increment_line(&mut self) {
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
pub enum TokenKind {
    LeftParen,
    RightParen,
    String,
    Eof,
}

impl std::fmt::Display for TokenKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        match self {
            Self::LeftParen => write!(f, "("),
            Self::RightParen => write!(f, ")"),
            Self::String => write!(f, "<string>"),
            Self::Eof => write!(f, "<EOF>"),
        }
    }
}

#[derive(Debug, PartialEq)]
pub struct Token {
    pub kind: TokenKind,
    pub start_pos: Position,
    pub end_pos: Position,
    pub data: Option<Box<str>>,
}

impl Token {
    pub fn kind(&self) -> &TokenKind {
        &self.kind
    }

    pub fn pos(&self) -> (&Position, &Position) {
        (&self.start_pos, &self.end_pos)
    }
}

#[derive(Debug)]
pub enum State {
    LexingString(String, Position, Position),
    Ready,
}

pub fn lex(text: &str) -> Vec<Token> {
    let mut ts = Vec::new();
    let cs = text.chars();
    let mut pos = Position::new(1, 0);
    let mut state = State::Ready;
    for c in cs {
        match state {
            State::Ready => match c {
                '(' => {
                    ts.push(Token {
                        kind: TokenKind::LeftParen,
                        start_pos: pos.clone(),
                        end_pos: pos.clone(),
                        data: None,
                    });
                    pos.increment_column();
                }
                ')' => {
                    ts.push(Token {
                        kind: TokenKind::RightParen,
                        start_pos: pos.clone(),
                        end_pos: pos.clone(),
                        data: None,
                    });
                    pos.increment_column();
                }
                _ if c.is_whitespace() => {
                    if c == '\n' {
                        pos.increment_line();
                    } else {
                        pos.increment_column();
                    }
                }
                _ => {
                    let s = String::from(c);
                    state = State::LexingString(s, pos.clone(), pos.clone());
                    pos.increment_column();
                }
            },
            State::LexingString(mut s, start_pos, end_pos) => match c {
                '(' => {
                    let t = Token {
                        kind: TokenKind::String,
                        start_pos,
                        end_pos,
                        data: Some(s.into()),
                    };
                    ts.push(t);
                    ts.push(Token {
                        kind: TokenKind::LeftParen,
                        start_pos: pos,
                        end_pos: pos,
                        data: None,
                    });
                    state = State::Ready;
                    pos.increment_column();
                }
                ')' => {
                    let t = Token {
                        kind: TokenKind::String,
                        start_pos,
                        end_pos,
                        data: Some(s.into()),
                    };
                    ts.push(t);
                    ts.push(Token {
                        kind: TokenKind::RightParen,
                        start_pos: pos,
                        end_pos: pos,
                        data: None,
                    });
                    state = State::Ready;
                    pos.increment_column();
                }
                _ if c.is_whitespace() => {
                    let t = Token {
                        kind: TokenKind::String,
                        start_pos,
                        end_pos,
                        data: Some(s.into()),
                    };
                    ts.push(t);
                    state = State::Ready;
                    if c == '\n' {
                        pos.increment_line();
                    } else {
                        pos.increment_column();
                    }
                }
                _ => {
                    s.push(c);
                    state = State::LexingString(s, start_pos, pos.clone());
                    pos.increment_column();
                }
            },
        }
    }
    ts.push(Token {
        kind: TokenKind::Eof,
        start_pos: pos,
        end_pos: pos,
        data: None,
    });
    ts
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn lex_test() {
        let s1 = lex("(foo(bar))");
        println!("{s1:?}");

        let s = lex("(foo 10 -2.0)");

        assert_eq!(
            &Token {
                kind: TokenKind::LeftParen,
                start_pos: Position::new(1, 0),
                end_pos: Position::new(1, 0),
                data: None
            },
            &s[0]
        );

        assert_eq!(
            &Token {
                kind: TokenKind::String,
                data: Some("foo".into()),
                start_pos: Position::new(1, 1),
                end_pos: Position::new(1, 3)
            },
            &s[1]
        );

        assert_eq!(
            &Token {
                kind: TokenKind::String,
                data: Some("10".into()),
                start_pos: Position::new(1, 5),
                end_pos: Position::new(1, 6)
            },
            &s[2]
        );

        assert_eq!(
            &Token {
                kind: TokenKind::String,
                data: Some("-2.0".into()),
                start_pos: Position::new(1, 8),
                end_pos: Position::new(1, 11),
            },
            &s[3]
        );

        assert_eq!(
            &Token {
                kind: TokenKind::RightParen,
                start_pos: Position::new(1, 12),
                end_pos: Position::new(1, 12),
                data: None
            },
            &s[4]
        );

        assert_eq!(
            &Token {
                kind: TokenKind::Eof,
                start_pos: Position::new(1, 13),
                end_pos: Position::new(1, 13),
                data: None
            },
            &s[5]
        );

        //
        let s = lex("(foo  10 -2.0\n\n  )");

        assert_eq!(
            &Token {
                kind: TokenKind::LeftParen,
                start_pos: Position::new(1, 0),
                end_pos: Position::new(1, 0),
                data: None
            },
            &s[0]
        );

        assert_eq!(
            &Token {
                kind: TokenKind::String,
                data: Some("foo".into()),
                start_pos: Position::new(1, 1),
                end_pos: Position::new(1, 3),
            },
            &s[1]
        );

        assert_eq!(
            &Token {
                kind: TokenKind::String,
                data: Some("10".into()),
                start_pos: Position::new(1, 6),
                end_pos: Position::new(1, 7),
            },
            &s[2]
        );

        assert_eq!(
            &Token {
                kind: TokenKind::String,
                data: Some("-2.0".into()),
                start_pos: Position::new(1, 9),
                end_pos: Position::new(1, 12),
            },
            &s[3]
        );

        assert_eq!(
            &Token {
                kind: TokenKind::RightParen,
                data: None,
                start_pos: Position::new(3, 2),
                end_pos: Position::new(3, 2)
            },
            &s[4]
        );

        assert_eq!(
            &Token {
                kind: TokenKind::Eof,
                data: None,
                start_pos: Position::new(3, 3),
                end_pos: Position::new(3, 3),
            },
            &s[5]
        );
    }
}
