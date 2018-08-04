use std::fmt;
use std::borrow::Cow;

pub const ROCKSTAR_NAN: RockstarNumber = ::std::f64::NAN;

// FIXME: Spec calls for DEC64
pub type RockstarNumber = f64;

// Spec calls for UTF-16 but I don't know if the difference
// is actually visible
pub type RockstarString = String;

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

#[derive(Debug, PartialEq, Clone, Copy)]
pub enum Type {
    String,
    Number,
    Boolean,
    Function,
    Null,
    Mysterious,
}

#[derive(Debug, PartialEq, Clone)]
pub enum Value<F> {
    String(RockstarString),
    Number(RockstarNumber),
    Boolean(bool),
    Function(F),
    Null,
    Mysterious,
}

impl<F> Value<F> {
    pub fn value_type(&self) -> Type {
        match *self {
            Value::String(_) => Type::String,
            Value::Number(_) => Type::Number,
            Value::Boolean(_) => Type::Boolean,
            Value::Function(_) => Type::Function,
            Value::Null => Type::Null,
            Value::Mysterious => Type::Mysterious,
        }
    }

    pub fn coerce_number(&self) -> RockstarNumber {
        // Don't know if this aligns with ECMAScript, but I think it's close
        // apart from strings, which I just don't want to do the right way.
        match *self {
            Value::String(..) => ROCKSTAR_NAN,
            Value::Number(n) => n,
            Value::Boolean(b) => if b { 1.0 } else { 0.0 },
            Value::Function(..) => ROCKSTAR_NAN,
            Value::Null => 0.0,
            Value::Mysterious => ROCKSTAR_NAN,
        }
    }

    pub fn user_display(&self) -> Cow<str> {
        match *self {
            Value::String(ref s) => s,
            Value::Number(n) => return format!("{}", n).into(),
            Value::Boolean(b) => if b { "true" } else { "false" },
            Value::Function(..) => "[Function]",
            Value::Null => "null",
            Value::Mysterious => "mysterious",
        }.into()
    }
}

impl<F> Value<F> where F: fmt::Display {
    pub fn repr_format(&self) -> Cow<str> {
        match *self {
            Value::String(ref s) => return format!("\"{}\"", s).into(),
            Value::Number(n) => return format!("{}", n).into(),
            Value::Boolean(b) => if b { "true" } else { "false" },
            Value::Function(ref func) => return format!("Function({})", func).into(),
            Value::Null => "null",
            Value::Mysterious => "mysterious",
        }.into()
    }
}
