use std::fmt;
use std::borrow::Cow;

// FIXME: Spec calls for DEC64
pub type RockstarNumber = f64;

// Spec calls for UTF-16 but I don't know that the difference
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
pub enum Value<F: fmt::Debug> {
    String(RockstarString),
    Number(RockstarNumber),
    Boolean(bool),
    Function(F),
    Null,
    Mysterious,
}

impl<F: fmt::Debug> Value<F> {
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

    // /// "Truthiness" coercion
    // pub fn coerce_boolean(&self) -> bool {
    //     match *self {
    //         Value::String(ref s) => /*string_to_bool(s).unwrap_or(false)*/ unimplemented!(),
    //         Value::Number(n) => !(n == 0.),  // NaN is truthy
    //         Value::Boolean(b) => b,
    //         Value::Function(_) => true,
    //         Value::Null => false,
    //         Value::Mysterious => false,
    //     }
    // }

    /// String coercion, as performed by `plus` and `times`
    pub fn coerce_string(&self) -> Option<Cow<str>> {
        match self {
            Value::String(s) => Some(Cow::Borrowed(s)),
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
        let t1 = v1.value_type();
        let t2 = v2.value_type();

        if t1 == t2 {
            return Some((v1, v2));
        }

        // Reorder for convenience
        let (v1, v2) = if t1 < t2 {
            (v1, v2)
        } else {
            (v2, v1)
        };

        if let Value::Mysterious = v2 {
            return None;
        }

        match v1 {
            Value::String(s1) => match v2 {
                Value::String(_) => unreachable!("type precedence"),
                Value::Number(_) => {
                    if let Ok(n1) = s1.parse() {
                        Some((Value::Number(n1), v2))
                    } else {
                        None
                    }
                }
                Value::Boolean(_) => {
                    string_to_bool(&s1)
                        .map(|b2| (Value::Boolean(b2), v2))
                }
                Value::Function(_) => None,
                Value::Null => {
                    if string_is_null_keyword(&s1) {
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
                    // NaN is truthy
                    let to_bool = !(n1 == 0.);
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

impl<F> Value<F> where F: fmt::Debug + fmt::Display {
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
