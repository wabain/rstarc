use std::error;
use std::io;
use std::fmt;

use lalrpop_util::ParseError;
use void::Void;

use lexer::{LexicalError, Token};

#[derive(Debug)]
pub enum RuntimeError {
    Io(io::Error),
    Lexer(LexicalError),
    Parser(ParseError<usize, Token, Void>),
}

impl RuntimeError {
    pub fn span(&self) -> Option<(usize, usize)> {
        match *self {
            RuntimeError::Io(_) => None,
            RuntimeError::Lexer(LexicalError::UnexpectedInput(p1, p2)) => {
                Some((p1, p2))
            }
            RuntimeError::Parser(ParseError::InvalidToken { location }) => {
                Some((location, location))
            }
            RuntimeError::Parser(ParseError::UnrecognizedToken { ref token, .. }) => {
                token.as_ref().map(|&(p1, _, p2)| (p1, p2))
            }
            RuntimeError::Parser(ParseError::ExtraToken { ref token }) => {
                Some((token.0, token.2))
            }
            RuntimeError::Parser(ParseError::User { .. }) => unreachable!(),
        }
    }
}

impl error::Error for RuntimeError {
    fn cause(&self) -> Option<&error::Error> {
        match *self {
            RuntimeError::Io(ref e) => Some(e),
            RuntimeError::Lexer(ref e) => Some(e),
            RuntimeError::Parser(ref e) => Some(e),
        }
    }
}

impl fmt::Display for RuntimeError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            RuntimeError::Io(ref e) => {
                write!(f, "error: {}", e)
            }
            RuntimeError::Lexer(ref e) => {
                write!(f, "error: {}", e)
            }
            RuntimeError::Parser(ParseError::InvalidToken { .. }) => {
                write!(f, "error: invalid token")
            }
            RuntimeError::Parser(ParseError::UnrecognizedToken {
                ref token, ref expected
            }) => {
                writeln!(f, "error: unexpected token {}", tok_desc(token))?;

                if !expected.is_empty() {
                    write!(f, "expected: ")?;
                    for (i, exp) in expected.iter().enumerate() {
                        if i > 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "{}", exp.replace("\\\\", "\\"))?;
                    }
                }
                Ok(())
            }
            RuntimeError::Parser(ParseError::ExtraToken { ref token }) => {
                write!(f, "error: extra token {}", token.1)
            }
            RuntimeError::Parser(ParseError::User { .. }) => unreachable!(),
        }
    }
}

fn tok_desc(token: &Option<(usize, Token, usize)>) -> String {
    if let Some((_, ref tok, _)) = *token {
        format!("{}", tok)
    } else {
        "<none>".into()
    }
}

impl From<io::Error> for RuntimeError {
    fn from(e: io::Error) -> Self {
        RuntimeError::Io(e)
    }
}

impl From<LexicalError> for RuntimeError {
    fn from(e: LexicalError) -> Self {
        RuntimeError::Lexer(e)
    }
}

impl From<ParseError<usize, Token, LexicalError>> for RuntimeError {
    fn from(e: ParseError<usize, Token, LexicalError>) -> Self {
        let parse_err = match e {
            ParseError::InvalidToken { location } => {
                ParseError::InvalidToken { location }
            }
            ParseError::UnrecognizedToken { token, expected } => {
                ParseError::UnrecognizedToken { token, expected }
            }
            ParseError::ExtraToken { token } => {
                ParseError::ExtraToken { token }
            },
            ParseError::User { error: lex_err } => {
                return RuntimeError::Lexer(lex_err);
            }
        };

        RuntimeError::Parser(parse_err)
    }
}
