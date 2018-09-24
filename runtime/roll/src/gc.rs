use core::ptr::NonNull;

use value_repr;
use alloc::{AllocEntry, FixedAllocator, GrowableAllocator};
use gc_roots::visit_gc_roots;

pub struct GcAllocator {
    nursery: FixedAllocator,
    main: GrowableAllocator,
}

impl GcAllocator {
    pub fn new() -> Self {
        GcAllocator {
            nursery: FixedAllocator::new(/*1024 * 128*/ 1024 * 1024 * 2),
            main: GrowableAllocator::empty(),
        }
    }

    pub fn alloc(&mut self, size: usize) -> NonNull<i8> {
        if size > self.nursery.size() {
            return self.main.alloc_or_grow(size);
        }

        self.nursery.alloc(size).unwrap_or_else(|| {
            self.do_full_gc();
            self.nursery.alloc(size).expect("Allocation after GC")
        })
    }

    fn do_full_gc(&mut self) {
        if cfg!(feature = "ad-hoc-debugs") {
            dbg!("Starting full GC...");
            dump_stack_roots();
        }

        // self.nursery.visit_entries(|entry| {
        //     if value_repr::has_gc_mark(entry.ptr.as_ptr()) {
        //         dbg!("{}",
        //             value_repr::Scalar::new(entry.ptr.as_ptr() as _)
        //                 .deref_rec()
        //                 .user_display()
        //         );
        //         panic!("Mark bit before sweep");
        //     }
        // });

        visit_gc_roots(|root| {
            value_repr::mark_gc(unsafe { *root as _ }, true);
        });

        self.main.compact();

        {
            let mut promo_count = 0;
            let mut visit_count = 0;
            let main = &mut self.main;

            self.nursery.visit_entries(|entry| {
                // XXX: this is a bug
                if entry.size > 1024 {
                    return;
                }

                dbg!("Sweep nursery pointer {:x} (size {})", entry.ptr.as_ptr() as usize, entry.size);

                visit_count += 1;

                if value_repr::has_gc_mark(entry.ptr.as_ptr()) {
                    promo_count += 1;
                    value_repr::mark_gc(entry.ptr.as_ptr(), false);
                    forward_from_nursery(main, entry);
                }
            });

            dbg!("Visited {} nursery values; promoted {}", visit_count, promo_count);
        }

        dump_stack_roots();

        visit_gc_roots(|root| {
            unsafe {
                value_repr::jump_to_forward_ptr(root);
            }
        });

        self.nursery.reset();
    }
}

fn forward_from_nursery(main: &mut GrowableAllocator, entry: AllocEntry) {
    let graduated = main.alloc_or_grow(entry.size);
    unsafe {
        entry.ptr.as_ptr().copy_to_nonoverlapping(
            graduated.as_ptr(),
            entry.size,
        );
        dbg!("Forward {:x} -> {:x}", entry.ptr.as_ptr() as usize, graduated.as_ptr() as usize);
        value_repr::forward_heap_ptr(entry.ptr.as_ptr(), graduated.as_ptr());
    }
}

fn dump_stack_roots() {
    visit_gc_roots(|root| {
        use super::value_repr;
        let scalar = unsafe { *root };
        let value = value_repr::Scalar::new(scalar).deref_rec();
        dbg!("Root at {:0>16x} = {: >16x}: {:?}",
             root as usize, scalar as usize, value);
    })
}
