//! Simple analyses applied directly to the AST

mod control_flow_verifier;
mod scoping;

use std::error;
use std::fmt;

use super::BINARY_NAME;
use super::ast::Pos;

pub use self::control_flow_verifier::verify_control_flow;
pub use self::scoping::{ScopeId, ScopeMap, identify_variable_scopes};

#[derive(Debug)]
pub enum CompileError {
    UnexpectedReturn(Pos),
    UnexpectedLoopControl(Pos),
    UnsupportedFeature {
        feature: String,
        has_interpreter_support: bool,
        pos: Option<Pos>,
    },
}

impl CompileError {
    pub fn span(&self) -> Option<(usize, usize)> {
        match *self {
            CompileError::UnexpectedReturn(Pos(p1, p2)) |
            CompileError::UnexpectedLoopControl(Pos(p1, p2)) |
            CompileError::UnsupportedFeature { pos: Some(Pos(p1, p2)), .. } => {
                Some((p1, p2))
            }
            CompileError::UnsupportedFeature { pos: None, .. } => None,
        }
    }
}

impl error::Error for CompileError {}

impl fmt::Display for CompileError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            CompileError::UnexpectedReturn(..) => {
                write!(f, "Unexpected return statement")
            }
            CompileError::UnexpectedLoopControl(..) => {
                write!(f, "Unexpected loop control statement")
            }
            CompileError::UnsupportedFeature {
                feature,
                has_interpreter_support,
                pos: _,
            } => {
                write!(f, "{} in compiled code is not supported.", feature)?;
                if *has_interpreter_support {
                    write!(f, "\n\nTry executing your program using '{} run \
                               --interpret <program>' instead", BINARY_NAME)?;
                }
                Ok(())
            }
        }
    }
}
