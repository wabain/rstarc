//! A wildly inefficient allocator

use super::VoidPtr;

use libc::{mmap, MAP_PRIVATE, MAP_ANON, MAP_FAILED, PROT_READ, PROT_WRITE};

const HACK_FAKE_PAGE_SIZE: usize = 4096;

static mut HEAP_POINT: *mut VoidPtr = 0 as _;
static mut HEAP_END: *mut VoidPtr = 0 as _;
static mut ALLOC_STEP: usize = 0;

#[inline]
fn round_to_pow2(n: usize, pow2: usize) -> usize {
    debug_assert!(n != 0);
    debug_assert!(pow2 != 0);
    debug_assert!(pow2 & (pow2 - 1) == 0);

    n + ((!n + 1) & (pow2 - 1))
}

pub fn alloc(size: usize) -> *mut VoidPtr {
    let size = round_to_pow2(size, 8);

    let remaining = unsafe { HEAP_END as usize - HEAP_POINT as usize };

    dbg!("Processing allocation of {} bytes", size);

    if size > remaining {
        let alloc_step;

        unsafe {
            alloc_step = ALLOC_STEP;
            ALLOC_STEP += 1;
        }

        // Fake a guess at the page size and bump up the size of the
        // allocation exponentially.
        //
        // FIXME: Should get the actual page size
        let req_size = round_to_pow2(size, HACK_FAKE_PAGE_SIZE) << (alloc_step / 2);

        dbg!("Allocating additional {} bytes", req_size);

        let new_heap = expand_heap(req_size).expect("Failed to allocate memory");
        unsafe {
            HEAP_POINT = new_heap.offset(size as isize);
            HEAP_END = new_heap.offset(req_size as isize);
        }
        new_heap
    } else {
        let alloc_start = unsafe { HEAP_POINT };
        unsafe {
            HEAP_POINT = HEAP_POINT.offset(size as isize);
        }
        alloc_start
    }
}

fn expand_heap(size: usize) -> Result<*mut VoidPtr, ()> {
    let area = unsafe {
        mmap(0 as _, size, PROT_READ|PROT_WRITE, MAP_PRIVATE|MAP_ANON, -1, 0)
    };

    if area == MAP_FAILED {
        Err(())
    } else {
        Ok(area)
    }
}
