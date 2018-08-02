//! Simple analyses applied directly to the AST

mod control_flow_verifier;
mod scoping;

use std::error;
use std::fmt;

use super::ast::Pos;

pub use self::control_flow_verifier::verify_control_flow;
pub use self::scoping::{ScopeId, ScopeMap, identify_variable_scopes};

#[derive(Debug)]
pub enum CompileError {
    UnexpectedReturn(Pos),
    UnexpectedLoopControl(Pos),
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
        }
    }
}
