use libc::c_void;

extern {
    static roll_num_globals: u32;
    static roll_globals: *mut *mut c_void;

    static llvm_gc_root_chain: *mut StackEntry;
}

/// The map for a single function's stack frame.  One of these is
/// compiled as constant data into the executable for each function.
///
/// Storage of metadata values is elided if the %metadata parameter to
/// @llvm.gcroot is null.
#[repr(C)]
struct FrameMap {
    /// Number of roots in stack frame
    num_roots: i32,
    /// Number of metadata entries. May be < num_roots.
    num_meta: i32,
    /// Metadata for each root (in-place array)
    meta: *mut c_void,
}

/// A link in the dynamic shadow stack.  One of these is embedded in
/// the stack frame of each function on the call stack.
#[repr(C)]
struct StackEntry {
    /// Link to next stack entry (the caller's)
    next: *mut StackEntry,
    /// Pointer to constant FrameMap
    map: *const FrameMap,
    /// Stack roots (in-place array)
    roots: *mut c_void,
}

pub fn visit_gc_roots<F>(visitor: F) where F: Fn(*mut *mut c_void) {
    let global_count = unsafe { roll_num_globals } as isize;
    let globals = unsafe { roll_globals };

    for i in 0..global_count {
        let root = unsafe { globals.offset(i) };
        visitor(root);
    }

    let mut entry = unsafe { llvm_gc_root_chain };

    while !entry.is_null() {
        let num_roots = unsafe { (*(*entry).map).num_roots } as isize;
        for i in 0..num_roots {
            let root = unsafe {
                (&mut (*entry).roots as *mut *mut c_void).offset(i)
            };
            visitor(root);
        }
        entry = unsafe { (*entry).next };
    }
}
