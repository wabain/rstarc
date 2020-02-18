#![no_std]

#[cfg(feature = "std")]
#[macro_use] extern crate std;

#[cfg(feature = "std")]
use std::fmt;
#[cfg(not(feature = "std"))]
use core::fmt;

#[cfg(feature = "std")]
use std::cmp::Ordering;
#[cfg(not(feature = "std"))]
use core::cmp::Ordering;

#[cfg(feature = "std")]
use std::borrow::Cow;

/// Value representation
///
/// The runtime uses a simple tagged pointer representation, requiring
/// pointers to have 8-byte alignment.
///
/// Currently, the only immediate values provided without a pointer
/// dereference are null and mysterious. My hope is to detect AOT when values
/// don't need to be boxed, but I can also add an unboxed-but-dynamic number
/// representation. In particular, I may use NaN-boxing to put numbers on the
/// stack if I don't want to make the move to DEC64. Currently, numbers are
/// allocated on the heap with an extra 64 bits (!) reserved for a tag.
///
///
/// Scalar values:
///
///     Null        0b0.......00000
///     False       0b0.......00010
///     True        0b0.......01010
///     Mysterious  0b0.......10010
///     Heap ptr    [61 bits]...000
///     Const str   [61 bits]...011
///     Function    [61 bits]...110
///
/// One motivation for this choice of tags was to avoid having false = 0x1,
/// while still allowing booleans to be coerced to their conventional values
/// with a simple shift (although I'm not sure I'll use that ability).
///
/// All scalar values can occur on the heap. In addition, there are additional
/// tags:
///
///     Number      0x00000004 [64-bit float]
///     String      [32 bit len] 0x0005 [string content]
pub mod value_constants {
    pub const NULL_BITS: u64 = 0x0;
    pub const FALSE_BITS: u64 = 0x2;
    pub const TRUE_BITS: u64 = 0xa;
    pub const MYSTERIOUS_BITS: u64 = 0x12;

    pub const TAG_MASK: u64 = 0x7;

    pub const HEAP_PTR_TAG: u64 = 0x0;
    pub const CONST_IMMEDIATE_TAG: u64 = 0x2;
    pub const CONST_STRING_TAG: u64 = 0x3;
    pub const HEAP_NUMBER_TAG: u64 = 0x4;
    pub const HEAP_STRING_TAG: u64 = 0x5;
    pub const FUNCTION_TAG: u64 = 0x6;

    pub const STRING_LEN_BITS: u64 = 32;
}

// Spec calls for DEC64
pub type RockstarNumber = f64;

pub trait RockstarString {
    fn string_borrow(&self) -> &str;
}

impl<'a> RockstarString for &'a str {
    fn string_borrow(&self) -> &str {
        &self
    }
}

#[cfg(feature = "std")]
impl RockstarString for std::rc::Rc<std::string::String> {
    fn string_borrow(&self) -> &str {
        &self
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
pub enum Value<S, F>
    where
        S: RockstarString + fmt::Debug + PartialEq,
        F: fmt::Debug
{
    String(S),
    Number(RockstarNumber),
    Boolean(bool),
    Function(F),
    Null,
    Mysterious,
}

impl<S, F> Value<S, F>
    where
        S: RockstarString + fmt::Debug + PartialEq,
        F: fmt::Debug
{
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
            Value::String(ref s) => string_to_bool(s.string_borrow()).unwrap_or(false),
            Value::Number(n) => rockstar_number_to_bool(n),
            Value::Boolean(b) => b,
            Value::Function(_) => true,
            Value::Null => false,
            Value::Mysterious => false,
        }
    }

    #[cfg(feature = "std")]
    /// String coercion, as performed by `plus` and `times`
    pub fn coerce_string(&self) -> Option<Cow<str>> {
        match self {
            Value::String(s) => Some(Cow::Borrowed(s.string_borrow())),
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

    pub fn rstar_gt(self, other: Self) -> bool {
        Value::rstar_compare(self, other) == Some(Ordering::Greater)
    }

    pub fn rstar_ge(self, other: Self) -> bool {
        let ordering = Value::rstar_compare(self, other);
        ordering.is_some() && ordering != Some(Ordering::Less)
    }

    pub fn rstar_lt(self, other: Self) -> bool {
        Value::rstar_compare(self, other) == Some(Ordering::Less)
    }

    pub fn rstar_le(self, other: Self) -> bool {
        let ordering = Value::rstar_compare(self, other);
        ordering.is_some() && ordering != Some(Ordering::Greater)
    }

    /// Compare the two values according to Rockstar's semantics. This isn't
    /// suitable as a PartialOrd impl because it performs type coercions.
    fn rstar_compare(v1: Self, v2: Self) -> Option<Ordering> {
        let (v1, v2) = match Value::coerce_binary_operands(v1, v2) {
            Some(pair) => pair,
            None => return None,
        };

        match (&v1, &v2) {
            (Value::String(s1), Value::String(s2)) => {
                s1.string_borrow().partial_cmp(s2.string_borrow())
            }
            (Value::Number(n1), Value::Number(n2)) => n1.partial_cmp(n2),
            (Value::Boolean(b1), Value::Boolean(b2)) => b1.partial_cmp(b2),
            (Value::Function(_), Value::Function(_)) => None,
            (Value::Null, Value::Null) |
            (Value::Mysterious, Value::Mysterious) => Some(Ordering::Equal),
            (_, _) => unreachable!("values {:?} {:?}", v1, v2),
        }
    }

    /// Coerce binary operands, potentially consuming the originals
    fn coerce_binary_operands(v1: Self, v2: Self) -> Option<(Self, Self)> {
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
                    if let Ok(n1) = s1.string_borrow().parse() {
                        Some((Value::Number(n1), v2))
                    } else {
                        None
                    }
                }
                Value::Boolean(_) => {
                    string_to_bool(s1.string_borrow())
                        .map(|b2| (Value::Boolean(b2), v2))
                }
                Value::Function(_) => None,
                Value::Null => {
                    if string_is_null_keyword(s1.string_borrow()) {
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

// Equality comparisons require F: PartialEq.
impl<S, F> Value<S, F>
    where
        S: RockstarString + fmt::Debug + PartialEq,
        F: fmt::Debug + PartialEq,
{
    pub fn rstar_is(self, other: Self) -> bool {
        match Value::coerce_binary_operands(self, other) {
            Some((v1, v2)) => v1 == v2,
            None => false,
        }
    }

    pub fn rstar_is_not(self, other: Self) -> bool {
        match Value::coerce_binary_operands(self, other) {
            Some((v1, v2)) => v1 != v2,
            None => true,
        }
    }
}

// repr_format requires F: Display
impl<S, F> Value<S, F>
    where
        S: RockstarString + fmt::Debug + PartialEq,
        F: fmt::Debug + fmt::Display,
{
    pub fn repr_format(&self) -> ReprDisplay<S, F> {
        ReprDisplay { value: self }
    }
}

pub struct UserDisplay<'a, S, F>
    where
        S: RockstarString + fmt::Debug + PartialEq + 'a,
        F: fmt::Debug + 'a,
{
    value: &'a Value<S, F>,
}

impl<'a, S, F> fmt::Display for UserDisplay<'a, S, F>
    where
        S: RockstarString + fmt::Debug + PartialEq + 'a,
        F: fmt::Debug + 'a,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.value {
            Value::String(s) => write!(f, "{}", s.string_borrow()),
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
        S: RockstarString + fmt::Debug + PartialEq + 'a,
        F: fmt::Debug + fmt::Display + 'a,
{
    value: &'a Value<S, F>,
}

impl<'a, S, F> fmt::Display for ReprDisplay<'a, S, F>
    where
        S: RockstarString + fmt::Debug + PartialEq + 'a,
        F: fmt::Debug + fmt::Display + 'a,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.value {
            Value::String(s) => write!(f, "\"{}\"", s.string_borrow()),
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
