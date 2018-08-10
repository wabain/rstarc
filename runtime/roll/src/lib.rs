#![no_std]
#![feature(lang_items)]
#![feature(panic_implementation)]

// TODO: Added this during a false start where the runtime didn't
// use libc. Remove if not needed.
#[macro_use] extern crate sc;

extern crate libc;

pub use libc::c_void as VoidPtr;

#[macro_use] mod syscall;
#[macro_use] mod io;
mod alloc;
mod say;
mod rust_lang_items;
mod value_repr;

use core::f64;

#[derive(Debug)]
pub enum RockstarValue<'a> {
    Null,
    Mysterious,
    Boolean(bool),
    String(&'a str),
    Number(f64),
    Func,
}

#[no_mangle]
pub extern fn roll_alloc(size: usize) -> *mut VoidPtr {
    alloc::alloc(size)
}

#[no_mangle]
pub extern fn roll_say(ptr: *mut VoidPtr) {
    let scalar = value_repr::Scalar::new(ptr);
    say::say(scalar.deref_rec());
}

#[no_mangle]
pub extern fn roll_is(p1: *mut VoidPtr, p2: *mut VoidPtr) -> u64 {
    use self::RockstarValue::*;

    let v1 = value_repr::Scalar::new(p1).deref_rec();
    let v2 = value_repr::Scalar::new(p2).deref_rec();

    let equality = match (&v1, &v2) {
        (Null, Null) => true,
        (Mysterious, Mysterious) => true,
        (Boolean(b1), Boolean(b2)) => *b1 == *b2,
        (String(s1), String(s2)) => s1 == s2,
        (Number(n1), Number(n2)) => *n1 == *n2,
        (Func, Func) => unimplemented!(),
        _ => coerce_number(&v1) == coerce_number(&v2),
    };

    value_repr::scalar_bool(equality)
}

#[no_mangle]
pub extern fn roll_is_not(p1: *mut VoidPtr, p2: *mut VoidPtr) -> u64 {
    use self::RockstarValue::*;

    let v1 = value_repr::Scalar::new(p1).deref_rec();
    let v2 = value_repr::Scalar::new(p2).deref_rec();

    let equality = match (&v1, &v2) {
        (Null, Null) => false,
        (Mysterious, Mysterious) => false,
        (Boolean(b1), Boolean(b2)) => *b1 != *b2,
        (String(s1), String(s2)) => s1 != s2,
        (Number(n1), Number(n2)) => *n1 != *n2,
        (Func, Func) => unimplemented!(),
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
        RockstarValue::String(..) => f64::NAN,
        RockstarValue::Number(n) => n,
        RockstarValue::Boolean(b) => if b { 1.0 } else { 0.0 },
        RockstarValue::Null => 0.0,
        RockstarValue::Mysterious | RockstarValue::Func => f64::NAN,
    }
}
