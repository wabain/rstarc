#![no_std]

extern crate libc;
extern crate rstarc_types;

#[macro_use] mod io;
mod alloc;
mod rust_lang_items;
mod value_repr;

use core::f64;
use core::fmt::Write;

use rstarc_types::Value;
pub(crate) use libc::c_void as VoidPtr;

use io::FDWrite;

type RockstarValue<'a> = rstarc_types::Value<&'a str, *const VoidPtr>;

#[no_mangle]
pub extern fn roll_alloc(size: usize) -> *mut VoidPtr {
    alloc::alloc(size)
}

#[no_mangle]
pub extern fn roll_say(ptr: *mut VoidPtr) {
    let scalar = value_repr::Scalar::new(ptr);
    let value = scalar.deref_rec();
    let mut stdout = FDWrite::stdout();
    let _ = writeln!(stdout, "{}", value.user_display());
}

#[no_mangle]
pub extern fn roll_is(p1: *mut VoidPtr, p2: *mut VoidPtr) -> u64 {
    use Value::*;

    let v1 = value_repr::Scalar::new(p1).deref_rec();
    let v2 = value_repr::Scalar::new(p2).deref_rec();

    let equality = match (&v1, &v2) {
        (Null, Null) => true,
        (Mysterious, Mysterious) => true,
        (Boolean(b1), Boolean(b2)) => *b1 == *b2,
        (String(s1), String(s2)) => s1 == s2,
        (Number(n1), Number(n2)) => *n1 == *n2,
        (Function(p1), Function(p2)) => p1 == p2,
        _ => coerce_number(&v1) == coerce_number(&v2),
    };

    value_repr::scalar_bool(equality)
}

#[no_mangle]
pub extern fn roll_is_not(p1: *mut VoidPtr, p2: *mut VoidPtr) -> u64 {
    use Value::*;

    let v1 = value_repr::Scalar::new(p1).deref_rec();
    let v2 = value_repr::Scalar::new(p2).deref_rec();

    let equality = match (&v1, &v2) {
        (Null, Null) => false,
        (Mysterious, Mysterious) => false,
        (Boolean(b1), Boolean(b2)) => *b1 != *b2,
        (String(s1), String(s2)) => s1 != s2,
        (Number(n1), Number(n2)) => *n1 != *n2,
        (Function(p1), Function(p2)) => p1 != p2,
        _ => coerce_number(&v1) != coerce_number(&v2),
    };

    value_repr::scalar_bool(equality)
}

#[no_mangle]
pub extern fn roll_mk_number(value: f64) -> u64 {
    let out = new_number(value);

    dbg!(
        "Requested {}, built value with representation {:?}",
        value,
        value_repr::Scalar::new(out as *mut VoidPtr).deref_rec()
    );

    out
}

#[no_mangle]
pub extern fn roll_add(p1: *mut VoidPtr, p2: *mut VoidPtr) -> u64 {
    let v1 = value_repr::Scalar::new(p1).deref_rec();
    let v2 = value_repr::Scalar::new(p2).deref_rec();
    new_number(coerce_number(&v1) + coerce_number(&v2))
}

#[no_mangle]
pub extern fn roll_sub(p1: *mut VoidPtr, p2: *mut VoidPtr) -> u64 {
    let v1 = value_repr::Scalar::new(p1).deref_rec();
    let v2 = value_repr::Scalar::new(p2).deref_rec();
    new_number(coerce_number(&v1) - coerce_number(&v2))
}

#[no_mangle]
pub extern fn roll_mul(p1: *mut VoidPtr, p2: *mut VoidPtr) -> u64 {
    let v1 = value_repr::Scalar::new(p1).deref_rec();
    let v2 = value_repr::Scalar::new(p2).deref_rec();
    new_number(coerce_number(&v1) * coerce_number(&v2))
}

#[no_mangle]
pub extern fn roll_div(p1: *mut VoidPtr, p2: *mut VoidPtr) -> u64 {
    let v1 = value_repr::Scalar::new(p1).deref_rec();
    let v2 = value_repr::Scalar::new(p2).deref_rec();
    new_number(coerce_number(&v1) / coerce_number(&v2))
}

#[no_mangle]
pub extern fn roll_gt(p1: *mut VoidPtr, p2: *mut VoidPtr) -> u64 {
    let v1 = value_repr::Scalar::new(p1).deref_rec();
    let v2 = value_repr::Scalar::new(p2).deref_rec();
    value_repr::scalar_bool(coerce_number(&v1) > coerce_number(&v2))
}

#[no_mangle]
pub extern fn roll_lt(p1: *mut VoidPtr, p2: *mut VoidPtr) -> u64 {
    let v1 = value_repr::Scalar::new(p1).deref_rec();
    let v2 = value_repr::Scalar::new(p2).deref_rec();
    value_repr::scalar_bool(coerce_number(&v1) < coerce_number(&v2))
}

#[no_mangle]
pub extern fn roll_ge(p1: *mut VoidPtr, p2: *mut VoidPtr) -> u64 {
    let v1 = value_repr::Scalar::new(p1).deref_rec();
    let v2 = value_repr::Scalar::new(p2).deref_rec();
    value_repr::scalar_bool(coerce_number(&v1) >= coerce_number(&v2))
}

#[no_mangle]
pub extern fn roll_le(p1: *mut VoidPtr, p2: *mut VoidPtr) -> u64 {
    let v1 = value_repr::Scalar::new(p1).deref_rec();
    let v2 = value_repr::Scalar::new(p2).deref_rec();
    value_repr::scalar_bool(coerce_number(&v1) <= coerce_number(&v2))
}

#[no_mangle]
pub extern fn roll_coerce_function(value: *mut VoidPtr) -> *const VoidPtr {
    match value_repr::Scalar::new(value).deref_rec() {
        Value::Function(p) => p,
        v => {
            let mut stderr = io::FDWrite::stderr();
            writeln!(stderr, "error: Cannot call value '{}'", v.user_display());
            unsafe {
                libc::exit(1);
            }
        }
    }
}

#[no_mangle]
pub extern fn roll_coerce_boolean(value: *mut VoidPtr) -> u8 {
    let value = value_repr::Scalar::new(value).deref_rec();
    if value.coerce_boolean() { 1 } else { 0 }
}

#[inline]
fn new_number(value: f64) -> u64 {
    let p = alloc::alloc(16) as *mut u64;
    unsafe {
        *p = value_repr::HEAP_NUMBER_TAG;
        *p.offset(1) = value.to_bits();
    }
    dbg!("Created number at 0x{:x}", p as u64);
    p as u64
}

#[inline]
fn coerce_number(v: &RockstarValue) -> f64 {
    match *v {
        Value::String(..) => f64::NAN,
        Value::Number(n) => n,
        Value::Boolean(b) => if b { 1.0 } else { 0.0 },
        Value::Null => 0.0,
        Value::Mysterious |
        Value::Function(_) => f64::NAN,
    }
}
