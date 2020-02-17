use core::{str, slice};
use core::marker::PhantomData;

use rstarc_types::{Value, value_constants::*};
use super::{VoidPtr, RockstarValue};

#[inline]
pub fn scalar_bool(b: bool) -> u64 {
    if b {
        TRUE_BITS
    } else {
        FALSE_BITS
    }
}

pub struct Scalar<'a> {
    bits: u64,
    __value: PhantomData<RockstarValue<'a>>,
}

pub struct HeapValue<'a> {
    ptr: *mut u64,
    __value: PhantomData<RockstarValue<'a>>,
}

#[derive(Debug, Copy, Clone)]
pub enum TagType {
    Null,
    Immediate,
    HeapPointer,
    ConstString,
    Function,
    HeapNumber,
    HeapString,
}

impl<'a> Scalar<'a> {
    pub fn new(bits: *mut VoidPtr) -> Self {
        Scalar {
            bits: bits as u64,
            __value: PhantomData,
        }
    }

    #[inline]
    pub fn scalar_type(&self) -> TagType {
        let tag_type = get_tag_type(self.bits);

        debug_assert!(
            match tag_type {
                TagType::Null |
                TagType::Immediate |
                TagType::HeapPointer |
                TagType::ConstString |
                TagType::Function => true,
                TagType::HeapNumber |
                TagType::HeapString => false,
            },
            "Unexpected type {:?} in scalar value 0x{:x}",
            tag_type,
            self.bits,
        );

        tag_type
    }

    #[inline]
    pub fn deref_rec(&self) -> RockstarValue<'a> {
        unsafe {
            match self.scalar_type() {
                TagType::Null => Value::Null,
                TagType::Immediate => immediate_from_bits(self.bits),
                TagType::HeapPointer => deref_heap_pointer(self.bits),
                TagType::ConstString => deref_const_string(self.bits),
                TagType::Function => extract_function_ptr(self.bits),
                TagType::HeapNumber |
                TagType::HeapString => unreachable!(),
            }
        }
    }
}

impl<'a> HeapValue<'a> {
    pub unsafe fn from_ptr(ptr: *mut u64) -> Self {
        HeapValue {
            ptr,
            __value: PhantomData,
        }
    }

    #[allow(unused)]
    #[inline]
    pub fn tag_type(&self) -> TagType {
        let head = unsafe { *self.ptr };
        get_tag_type(head)
    }

    #[inline]
    pub fn deref_rec(&self) -> RockstarValue<'a> {
        unsafe {
            let head = *self.ptr;
            match get_tag_type(head) {
                TagType::Null => Value::Null,
                TagType::Immediate => immediate_from_bits(head),
                TagType::HeapPointer => deref_heap_pointer(head),
                TagType::ConstString => deref_const_string(head),
                TagType::Function => extract_function_ptr(head),
                TagType::HeapNumber => deref_heap_number(head, self.ptr),
                TagType::HeapString => deref_heap_string(head, self.ptr),
            }
        }
    }
}

#[inline]
fn get_tag_type(bits: u64) -> TagType {
    if bits == NULL_BITS {
        TagType::Null
    } else {
        let tag = bits & TAG_MASK;
        match tag {
            CONST_IMMEDIATE_TAG => TagType::Immediate,
            HEAP_PTR_TAG => TagType::HeapPointer,
            CONST_STRING_TAG => TagType::ConstString,
            FUNCTION_TAG => TagType::Function,
            HEAP_NUMBER_TAG => TagType::HeapNumber,
            HEAP_STRING_TAG => TagType::HeapString,
            _ => panic!("Unexpected value tag in 0x{:x}", bits),
        }
    }
}

#[inline(always)]
fn immediate_from_bits<'a>(bits: u64) -> RockstarValue<'a> {
    match bits {
        TRUE_BITS => Value::Boolean(true),
        FALSE_BITS => Value::Boolean(false),
        MYSTERIOUS_BITS => Value::Mysterious,
        _ => panic!("Unexpected immediate value 0x{:x}", bits),
    }
}

macro_rules! tag_to_ptr {
    ((const) $target_type:ty, $tag:expr, $bits:expr) => {
        tag_to_ptr!(as *const $target_type, $tag, $bits)
    };
    ($target_type:ty, $tag:expr, $bits:expr) => {
        tag_to_ptr!(as *mut $target_type, $tag, $bits)
    };
    (as $ptr_type:ty, $tag:expr, $bits:expr) => {{
        let bits = $bits;
        debug_assert_eq!(bits & TAG_MASK, $tag);
        (bits & !TAG_MASK) as $ptr_type
    }};
}

#[inline]
unsafe fn deref_heap_pointer<'a>(bits: u64) -> RockstarValue<'a> {
    let ptr = tag_to_ptr!(u64, HEAP_PTR_TAG, bits);
    let value = HeapValue::from_ptr(ptr);
    value.deref_rec()
}

#[inline]
unsafe fn deref_const_string<'a>(bits: u64) -> RockstarValue<'a> {
    let ptr = tag_to_ptr!((const) u8, CONST_STRING_TAG, bits);
    let len = strlen(ptr);
    let s = str::from_utf8_unchecked(slice::from_raw_parts(ptr, len));

    Value::String(s)
}

#[inline]
unsafe fn extract_function_ptr<'a>(bits: u64) -> RockstarValue<'a> {
    let ptr = tag_to_ptr!((const) VoidPtr, FUNCTION_TAG, bits);
    Value::Function(ptr)
}

#[inline]
unsafe fn deref_heap_number<'a>(_head: u64, ptr: *const u64) -> RockstarValue<'a> {
    let n_ptr = (ptr as *const f64).offset(1);
    Value::Number(*n_ptr)
}

#[inline]
unsafe fn deref_heap_string<'a>(head: u64, ptr: *const u64) -> RockstarValue<'a> {
    let len = (head >> (64 - STRING_LEN_BITS)) as usize;
    let s_ptr = (ptr as *const u8).offset(8);
    let s = str::from_utf8_unchecked(slice::from_raw_parts(s_ptr, len));

    Value::String(s)
}

unsafe fn strlen(p: *const u8) -> usize {
    for i in 0usize.. {
        if *p.offset(i as isize) == 0 {
            return i;
        }
    }
    unreachable!();
}
