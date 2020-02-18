use std::{fmt, rc::Rc};
use rstarc_types::Value;

/// Compiler and interpreter's view of a Rockstar value
///
/// Spec calls for UTF-16 but I don't know that the difference
/// is actually visible
pub type RockstarValue<F> = Value<Rc<String>, F>;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash)]
pub enum LangVariable<'a> {
    Common(&'a str, &'a str),
    Proper(&'a str),
}

impl<'a> fmt::Display for LangVariable<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            LangVariable::Common(p, v) => write!(f, "{} {}", p, v),
            LangVariable::Proper(v) => write!(f, "{}", v),
        }
    }
}
