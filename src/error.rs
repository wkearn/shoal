#[derive(Debug)]
pub enum Error {
    IOError(std::io::Error),
    ParseError,
    SyntaxError(String),
    UndefinedVariableError(String),
    TypeError(String),
    RuntimeError(String),
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        match self {
            Error::IOError(e) => e.fmt(f),
            Error::ParseError => write!(f, "Parse error"),
            Error::SyntaxError(s) => write!(f, "Syntax error: {}", s),
            Error::UndefinedVariableError(v) => write!(f, "Error: variable {} is not defined", v),
            Error::TypeError(s) => write!(f, "Type error: {}", s),
            Error::RuntimeError(s) => write!(f, "Runtime error: {}", s),
        }
    }
}

impl std::error::Error for Error {}

impl From<std::io::Error> for Error {
    fn from(e: std::io::Error) -> Self {
        Error::IOError(e)
    }
}
