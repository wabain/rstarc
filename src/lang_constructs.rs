use std::fmt;
use std::borrow::Cow;

use rstarc_types::Value;

// Spec calls for UTF-16 but I don't know that the difference
// is actually visible
pub type RockstarString = String;

/// Compiler's view of a Rockstar value
pub type RockstarValue<F> = Value<RockstarString, F>;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub enum LangVariable<'a> {
    Common(Cow<'a, str>, Cow<'a, str>),
    Proper(Cow<'a, str>),
}

impl<'a> fmt::Display for LangVariable<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            LangVariable::Common(p, v) => write!(f, "{} {}", p, v),
            LangVariable::Proper(v) => write!(f, "{}", v),
        }
    }
}
