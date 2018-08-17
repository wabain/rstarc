use std::error;
use std::io;
use std::fmt;

use lalrpop_util::ParseError;
use void::Void;

use base_analysis::CompileError;
use codegen::CodegenError;
use lexer::{LexicalError, Token};

#[derive(Debug)]
pub enum RuntimeError {
    Io(io::Error),
    Lexer(LexicalError),
    Parser(ParseError<usize, Token, Void>),
    Compile(CompileError),
    Codegen(CodegenError),
}

impl RuntimeError {
    pub fn span(&self) -> Option<(usize, usize)> {
        match *self {
            RuntimeError::Io(_) | RuntimeError::Codegen(_) => None,
            RuntimeError::Lexer(LexicalError::UnexpectedInput(p1, p2)) => {
                Some((p1, p2))
            }
            RuntimeError::Compile(ref e) => e.span(),
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
        match self {
            RuntimeError::Io(e) => Some(e),
            RuntimeError::Lexer(e) => Some(e),
            RuntimeError::Parser(e) => Some(e),
            RuntimeError::Compile(e) => Some(e),
            RuntimeError::Codegen(e) => Some(e)
        }
    }
}

impl fmt::Display for RuntimeError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            RuntimeError::Io(e) => {
                write!(f, "error: {}", e)
            }
            RuntimeError::Lexer(e) => {
                write!(f, "error: {}", e)
            }
            RuntimeError::Parser(ParseError::InvalidToken { .. }) => {
                write!(f, "error: invalid token")
            }
            RuntimeError::Parser(ParseError::UnrecognizedToken {
                token, expected
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
            RuntimeError::Parser(ParseError::ExtraToken { token }) => {
                write!(f, "error: extra token {}", token.1)
            }
            RuntimeError::Parser(ParseError::User { .. }) => unreachable!(),
            RuntimeError::Compile(e) => {
                write!(f, "error: {}", e)
            }
            RuntimeError::Codegen(e) => {
                let err_header = if e.is_internal() { "internal " } else { "" };
                write!(f, "{}error: {}", err_header, e)
            }
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

macro_rules! from_variant {
    ($src_ty:ty, $runtime_constructor:expr) => {
        impl From<$src_ty> for RuntimeError {
            fn from(e: $src_ty) -> Self {
                $runtime_constructor(e)
            }
        }
    }
}

from_variant!(io::Error, RuntimeError::Io);
from_variant!(LexicalError, RuntimeError::Lexer);
from_variant!(CompileError, RuntimeError::Compile);
from_variant!(CodegenError, RuntimeError::Codegen);

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
