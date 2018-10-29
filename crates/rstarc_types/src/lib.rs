#![no_std]

#[cfg(feature = "std")]
#[macro_use] extern crate std;

#[cfg(feature = "std")]
use std::fmt;

#[cfg(not(feature = "std"))]
use core::fmt;

#[cfg(feature = "std")]
use std::borrow::Cow;

// Spec calls for DEC64
pub type RockstarNumber = f64;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy)]
pub enum Type {
    String,
    Number,
    Boolean,
    Function,
    Null,
    Mysterious,
}

#[derive(Debug, PartialEq, Clone)]
pub enum Value<S: AsRef<str>, F: fmt::Debug> {
    String(S),
    Number(RockstarNumber),
    Boolean(bool),
    Function(F),
    Null,
    Mysterious,
}

impl<S: AsRef<str>, F: fmt::Debug> Value<S, F> {
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

    pub fn user_display(&self) -> UserDisplay<S, F> {
        UserDisplay { value: self }
    }

    /// "Truthiness" coercion
    pub fn coerce_boolean(&self) -> bool {
        match *self {
            Value::String(ref s) => string_to_bool(s.as_ref()).unwrap_or(false),
            Value::Number(n) => rockstar_number_to_bool(n),
            Value::Boolean(b) => b,
            Value::Function(_) => true,
            Value::Null => false,
            Value::Mysterious => false,
        }
    }

    #[cfg(feature="std")]
    /// String coercion, as performed by `plus` and `times`
    pub fn coerce_string(&self) -> Option<Cow<str>> {
        match self {
            Value::String(s) => Some(Cow::Borrowed(s.as_ref())),
            Value::Number(n) => Some(Cow::Owned(format!("{}", n))),
            Value::Boolean(b) => {
                let s = if *b { "true" } else { "false" };
                Some(Cow::Borrowed(s))
            }
            Value::Function(_) => None,
            Value::Null => Some(Cow::Borrowed("null")),
            Value::Mysterious => Some(Cow::Borrowed("mysterious")),
        }
    }

    pub fn coerce_binary_operands(v1: Self, v2: Self) -> Option<(Self, Self)> {
        // Reorder for convenience
        if v1.value_type() > v2.value_type() {
            Value::coerce_type_ordered_binary_operands(v2, v1)
                .map(|(v2, v1)| (v1, v2))
        } else {
            Value::coerce_type_ordered_binary_operands(v1, v2)
        }
    }

    fn coerce_type_ordered_binary_operands(v1: Self, v2: Self)
        -> Option<(Self, Self)>
    {
        let t1 = v1.value_type();
        let t2 = v2.value_type();

        if t1 == t2 {
            return Some((v1, v2));
        }

        if let Value::Mysterious = v2 {
            return None;
        }

        match v1 {
            Value::String(s1) => match v2 {
                Value::String(_) => unreachable!("type precedence"),
                Value::Number(_) => {
                    if let Ok(n1) = s1.as_ref().parse() {
                        Some((Value::Number(n1), v2))
                    } else {
                        None
                    }
                }
                Value::Boolean(_) => {
                    string_to_bool(s1.as_ref())
                        .map(|b2| (Value::Boolean(b2), v2))
                }
                Value::Function(_) => None,
                Value::Null => {
                    if string_is_null_keyword(s1.as_ref()) {
                        Some((Value::Null, Value::Null))
                    } else {
                        None
                    }
                }
                Value::Mysterious => unreachable!("blanket check"),
            }

            Value::Number(n1) => match v2 {
                Value::String(_) | Value::Number(_) => {
                    unreachable!("type precedence");
                }
                Value::Boolean(_) => {
                    let to_bool = rockstar_number_to_bool(n1);
                    Some((Value::Boolean(to_bool), v2))
                }
                Value::Function(_) => None,
                Value::Null => {
                    if n1 == 0. {
                        Some((Value::Null, Value::Null))
                    } else {
                        None
                    }
                }
                Value::Mysterious => unreachable!("blanket check"),
            }

            Value::Boolean(b1) => match v2 {
                Value::String(_) | Value::Number(_) | Value::Boolean(_) => {
                    unreachable!("type precedence");
                }
                Value::Function(_) => None,
                Value::Null => {
                    if !b1 {
                        Some((Value::Null, Value::Null))
                    } else {
                        None
                    }
                }
                Value::Mysterious => unreachable!("blanket check"),
            }

            Value::Function(_) | Value::Null => None,

            Value::Mysterious => unreachable!("blanket check"),
        }
    }
}

impl<S, F> Value<S, F> where S: AsRef<str>, F: fmt::Debug + fmt::Display {
    pub fn repr_format(&self) -> ReprDisplay<S, F> {
        ReprDisplay { value: self }
    }
}

pub struct UserDisplay<'a, S, F>
    where
        S: AsRef<str> + 'a,
        F: fmt::Debug + 'a,
{
    value: &'a Value<S, F>,
}

impl<'a, S, F> fmt::Display for UserDisplay<'a, S, F>
    where
        S: AsRef<str> + 'a,
        F: fmt::Debug + 'a,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.value {
            Value::String(s) => write!(f, "{}", s.as_ref()),
            Value::Number(n) => write!(f, "{}", n),
            Value::Boolean(b) =>  write!(f, "{}", *b),
            Value::Function(..) => write!(f, "[Function]"),
            Value::Null => write!(f, "null"),
            Value::Mysterious => write!(f, "mysterious"),
        }
    }
}

pub struct ReprDisplay<'a, S, F>
    where
        S: AsRef<str> + 'a,
        F: fmt::Debug + fmt::Display + 'a,
{
    value: &'a Value<S, F>,
}

impl<'a, S, F> fmt::Display for ReprDisplay<'a, S, F>
    where
        S: AsRef<str> + 'a,
        F: fmt::Debug + fmt::Display + 'a,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.value {
            Value::String(s) => write!(f, "\"{}\"", s.as_ref()),
            Value::Number(n) => write!(f, "{}", n),
            Value::Boolean(b) =>  write!(f, "{}", *b),
            Value::Function(func) => write!(f, "Function({})", func),
            Value::Null => write!(f, "null"),
            Value::Mysterious => write!(f, "mysterious"),
        }
    }
}

fn rockstar_number_to_bool(n: RockstarNumber) -> bool {
    // NaN is truthy
    !(n == 0.)
}

fn string_to_bool(s: &str) -> Option<bool> {
    match s {
        "true" | "right" | "yes" | "ok" => Some(true),
        "false" | "wrong" | "no" | "lies" => Some(false),
        _ => None
    }
}

fn string_is_null_keyword(s: &str) -> bool {
    match s {
        "null" | "nothing" | "nowhere" |
        "nobody" | "empty" | "gone" => true,
        _ => false,
    }
}
