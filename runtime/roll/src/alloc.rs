//! A wildly inefficient allocator

use core::ptr::NonNull;

use libc::{mmap, MAP_PRIVATE, MAP_ANON, MAP_FAILED, PROT_READ, PROT_WRITE};

const HACK_FAKE_PAGE_SIZE: usize = 4096;

#[inline]
fn round_to_pow2(n: usize, pow2: usize) -> usize {
    debug_assert!(n != 0);
    debug_assert!(pow2 != 0);
    debug_assert!(pow2 & (pow2 - 1) == 0);

    n + ((!n + 1) & (pow2 - 1))
}

#[derive(Debug)]
pub struct AllocEntry {
    pub ptr: NonNull<i8>,
    pub size: usize,
}

pub struct FixedAllocator {
    size: usize,
    offset: usize,
    heap_start: *mut i8,
}

impl FixedAllocator {
    pub fn new(size: usize) -> Self {
        let mut allocator = FixedAllocator {
            size,
            offset: 0,
            heap_start: 0 as _,
        };

        allocator.offset = allocator.data_offset();
        allocator
    }

    pub fn alloc(&mut self, size: usize) -> Option<NonNull<i8>> {
        let size = round_to_pow2(size, 8);

        dbg!("Processing allocation of {} bytes", size);

        if self.heap_start.is_null() {
            self.heap_start = create_new_heap(self.size).as_ptr();
        }

        if size > self.remaining() {
            None
        } else {
            unsafe {
                self.mark_used(self.offset, size);
            }

            let start_offset = self.offset as isize;
            self.offset += size;

            Some(unsafe {
                NonNull::new_unchecked(self.heap_start.offset(start_offset))
            })
        }
    }

    #[inline]
    pub fn remaining(&self) -> usize {
        self.size - self.offset
    }

    #[inline]
    pub fn size(&self) -> usize {
        self.size
    }

    pub fn reset(&mut self) {
        self.offset = self.data_offset();
    }

    pub fn visit_entries<F>(&mut self, mut visitor: F)
        where F: FnMut(AllocEntry)
    {
        if self.heap_start.is_null() {
            return;
        }

        let mut entry_start_idx = None;

        let end_idx = self.size / 8;

        'outer: for i in 0..self.get_mark_byte_count() {
            let bits = self.get_mark_bits(i);
            dbg!("Walking mark bits {:0<8b}", bits);
            for b in 0..8 {
                let new_idx = i * 8 + b;

                if new_idx == end_idx {
                    break 'outer;
                }

                if bits & 1 << b == 0 {
                    continue;
                }

                if let Some(prev) = entry_start_idx {
                    visitor(AllocEntry {
                        ptr: unsafe {
                            let ptr = self.heap_start.offset((prev * 8) as isize);
                            NonNull::new_unchecked(ptr)
                        },
                        size: (new_idx - prev) * 8,
                    });
                }

                entry_start_idx = Some(new_idx);
            }
        }

        if let Some(prev) = entry_start_idx {
            visitor(AllocEntry {
                ptr: unsafe {
                    let ptr = self.heap_start.offset((prev * 8) as isize);
                    NonNull::new_unchecked(ptr)
                },
                size: self.offset - prev * 8,
            });
        }
    }

    #[inline]
    unsafe fn mark_used(&self, offset: usize, size: usize) {
        let logical_offset = (offset - self.data_offset()) / 8;
        let byte = logical_offset / 8;
        let bit = logical_offset % 8;

        dbg!("mark offset {} size {}, starts at logical offset {} = {}:{}",
             offset, size, logical_offset, byte, bit);

        // Mask out higher bits, if they're still set
        let start_mark_byte = self.heap_start.offset(byte as isize);
        *start_mark_byte &= (1 << bit) - 1;
        *start_mark_byte |= 1 << bit;

        for now_zero in byte + 1..byte + size / (8 * 8) {
            *self.heap_start.offset(now_zero as isize) = 0;
        }
    }

    #[inline]
    fn get_mark_bits(&self, idx: usize) -> u8 {
        debug_assert!(!self.heap_start.is_null());
        debug_assert!(idx < self.size / 8);
        unsafe {
            *self.heap_start.offset(idx as isize) as u8
        }
    }

    #[inline]
    fn data_offset(&self) -> usize {
        round_to_pow2(self.get_mark_byte_count(), 8)
    }

    #[inline]
    fn get_mark_byte_count(&self) -> usize {
        debug_assert!(self.size & (8 - 1) == 0);
        self.size / (8 * 8)
    }
}

const ALLOC_POOL_COUNT: usize = 78;

pub struct GrowableAllocator {
    idx: usize,
    // This is about 1PiB, which is more than we could
    // realistically allocate
    pools: [FixedAllocator; ALLOC_POOL_COUNT],
}

impl GrowableAllocator {
    pub fn empty() -> Self {
        use core::mem; // XXX

        let mut alloc = GrowableAllocator {
            idx: 0,
            pools: unsafe { mem::uninitialized() },
        };

        for i in 0..ALLOC_POOL_COUNT {
            alloc.pools[i] = FixedAllocator::new(HACK_FAKE_PAGE_SIZE << (i / 2));
        }

        alloc
    }

    pub fn alloc_or_grow(&mut self, size: usize) -> NonNull<i8> {
        let size = round_to_pow2(size, 8);

        if size > HACK_FAKE_PAGE_SIZE {
            unimplemented!("Larger allocations (requested size {})", size);
        }

        dbg!("Processing allocation of {} bytes", size);

        loop {
            let pool = &mut self.pools[self.idx];

            if let Some(p) = pool.alloc(size) {
                return p;
            }

            self.idx += 1;
        }
    }

    pub fn compact(&mut self) {
        // unimplemented!()
    }
}

fn create_new_heap(size: usize) -> NonNull<i8> {
    let area = unsafe {
        mmap(0 as _, size, PROT_READ|PROT_WRITE, MAP_PRIVATE|MAP_ANON, -1, 0)
    };

    if area == MAP_FAILED {
        panic!("Failed mmap request for {}B", size);
    } else {
        unsafe { NonNull::new_unchecked(area as *mut i8) }
    }
}
