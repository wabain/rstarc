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

macro_rules! fatal {
    ($msg:expr, $($arg:expr),*) => {{
        let mut stderr = io::FDWrite::stderr();
        writeln!(stderr, concat!("error: ", $msg), $($arg),*);
        unsafe {
            libc::exit(1);
        }
    }};
}

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
    let v1 = value_repr::Scalar::new(p1).deref_rec();
    let v2 = value_repr::Scalar::new(p2).deref_rec();
    value_repr::scalar_bool(v1.rstar_is(v2))
}

#[no_mangle]
pub extern fn roll_is_not(p1: *mut VoidPtr, p2: *mut VoidPtr) -> u64 {
    let v1 = value_repr::Scalar::new(p1).deref_rec();
    let v2 = value_repr::Scalar::new(p2).deref_rec();
    value_repr::scalar_bool(v1.rstar_is_not(v2))
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

    match (v1, v2) {
        (Value::Number(n1), Value::Number(n2)) => new_number(n1 + n2),
        (Value::String(_), _) | (_, Value::String(_)) => {
            unimplemented!("String concatenation")
        }
        (v1, v2) => {
            fatal!("Cannot add '{}' and '{}'",
                   v1.user_display(),
                   v2.user_display())
        }
    }
}

#[no_mangle]
pub extern fn roll_sub(p1: *mut VoidPtr, p2: *mut VoidPtr) -> u64 {
    let v1 = value_repr::Scalar::new(p1).deref_rec();
    let v2 = value_repr::Scalar::new(p2).deref_rec();
    match (v1, v2) {
        (Value::Number(n1), Value::Number(n2)) => new_number(n1 - n2),
        (v1, v2) => {
            fatal!("Cannot subtract '{}' and '{}'",
                   v1.user_display(),
                   v2.user_display())
        }
    }
}

#[no_mangle]
pub extern fn roll_mul(p1: *mut VoidPtr, p2: *mut VoidPtr) -> u64 {
    let v1 = value_repr::Scalar::new(p1).deref_rec();
    let v2 = value_repr::Scalar::new(p2).deref_rec();
    match (v1, v2) {
        (Value::Number(n1), Value::Number(n2)) => new_number(n1 * n2),
        (Value::String(_), Value::Number(_)) |
        (Value::Number(_), Value::String(_)) => {
            unimplemented!("String repetition")
        }
        (v1, v2) => {
            fatal!("Cannot multiply '{}' and '{}'",
                   v1.user_display(),
                   v2.user_display())
        }
    }
}

#[no_mangle]
pub extern fn roll_div(p1: *mut VoidPtr, p2: *mut VoidPtr) -> u64 {
    let v1 = value_repr::Scalar::new(p1).deref_rec();
    let v2 = value_repr::Scalar::new(p2).deref_rec();
    match (v1, v2) {
        (Value::Number(n1), Value::Number(n2)) => new_number(n1 / n2),
        (v1, v2) => {
            fatal!("Cannot divide '{}' and '{}'",
                   v1.user_display(),
                   v2.user_display())
        }
    }
}

#[no_mangle]
pub extern fn roll_incr(p: *mut VoidPtr, count: u32) -> u64 {
    let v = value_repr::Scalar::new(p).deref_rec();
    match v {
        Value::Number(n) => {
            new_number(n + (count as f64))
        }
        Value::Boolean(b) => {
            let new = if count % 2 == 0 { b } else { !b };
            value_repr::scalar_bool(new)
        }
        v @ _ => {
            fatal!("Cannot increment '{}'", v.user_display())
        }
    }
}

#[no_mangle]
pub extern fn roll_decr(p: *mut VoidPtr, count: u32) -> u64 {
    let v = value_repr::Scalar::new(p).deref_rec();
    match v {
        Value::Number(n) => {
            new_number(n - (count as f64))
        }
        Value::Boolean(b) => {
            let new = if count % 2 == 0 { b } else { !b };
            value_repr::scalar_bool(new)
        }
        v @ _ => {
            fatal!("Cannot decrement '{}'", v.user_display())
        }
    }
}

#[no_mangle]
pub extern fn roll_gt(p1: *mut VoidPtr, p2: *mut VoidPtr) -> u64 {
    let v1 = value_repr::Scalar::new(p1).deref_rec();
    let v2 = value_repr::Scalar::new(p2).deref_rec();
    value_repr::scalar_bool(v1.rstar_gt(v2))
}

#[no_mangle]
pub extern fn roll_lt(p1: *mut VoidPtr, p2: *mut VoidPtr) -> u64 {
    let v1 = value_repr::Scalar::new(p1).deref_rec();
    let v2 = value_repr::Scalar::new(p2).deref_rec();
    value_repr::scalar_bool(v1.rstar_lt(v2))
}

#[no_mangle]
pub extern fn roll_ge(p1: *mut VoidPtr, p2: *mut VoidPtr) -> u64 {
    let v1 = value_repr::Scalar::new(p1).deref_rec();
    let v2 = value_repr::Scalar::new(p2).deref_rec();
    value_repr::scalar_bool(v1.rstar_ge(v2))
}

#[no_mangle]
pub extern fn roll_le(p1: *mut VoidPtr, p2: *mut VoidPtr) -> u64 {
    let v1 = value_repr::Scalar::new(p1).deref_rec();
    let v2 = value_repr::Scalar::new(p2).deref_rec();
    value_repr::scalar_bool(v1.rstar_le(v2))
}

#[no_mangle]
pub extern fn roll_coerce_function(value: *mut VoidPtr) -> *const VoidPtr {
    match value_repr::Scalar::new(value).deref_rec() {
        Value::Function(p) => p,
        v => fatal!("Cannot call value '{}'", v.user_display()),
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
        *p = rstarc_types::value_constants::HEAP_NUMBER_TAG;
        *p.offset(1) = value.to_bits();
    }
    dbg!("Created number at 0x{:x}", p as u64);
    p as u64
}
