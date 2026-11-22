//! A small, fast global allocator for the model checker: the Windows process heap (the `System` allocator) takes a lock
//! and is slow for the millions of tiny short-lived allocations the evaluator performs. Small blocks come from
//! per-thread size-class free lists carved out of large chunks; everything else goes to `System`.
//!
//! Measured need: the interpreter allocates a few `Rc`/`Vec` blocks per evaluated action (EWD998: ~100M allocations).

use std::alloc::{GlobalAlloc, Layout, System};
use std::cell::UnsafeCell;
use std::ptr::null_mut;

const GRAIN: usize = 16;
const MAX_SMALL: usize = 512;
const NCLASS: usize = MAX_SMALL / GRAIN + 1;
const CHUNK: usize = 1 << 20;

struct Local {
    free: [*mut u8; NCLASS],
    bump: *mut u8,
    end: *mut u8,
}

thread_local! {
    static LOCAL: UnsafeCell<Local> = const { UnsafeCell::new(Local { free: [null_mut(); NCLASS], bump: null_mut(), end: null_mut() }) };
}

pub struct FastAlloc;

#[inline]
fn small(l: &Layout) -> bool {
    l.size() <= MAX_SMALL && l.align() <= GRAIN
}

unsafe impl GlobalAlloc for FastAlloc {
    #[inline]
    unsafe fn alloc(&self, l: Layout) -> *mut u8 {
        if !small(&l) {
            return System.alloc(l);
        }
        let class = (l.size() + GRAIN - 1) / GRAIN;
        let r = LOCAL.try_with(|loc| {
            let loc = &mut *loc.get();
            let head = loc.free[class];
            if !head.is_null() {
                loc.free[class] = *(head as *mut *mut u8);
                return head;
            }
            let sz = class.max(1) * GRAIN;
            if (loc.end as usize) - (loc.bump as usize) < sz {
                let chunk = System.alloc(Layout::from_size_align_unchecked(CHUNK, GRAIN));
                if chunk.is_null() {
                    return null_mut();
                }
                loc.bump = chunk;
                loc.end = chunk.add(CHUNK);
            }
            let p = loc.bump;
            loc.bump = p.add(sz);
            p
        });
        match r {
            Ok(p) => p,
            // thread-local storage is gone (thread teardown): give the block to the system allocator
            Err(_) => System.alloc(Layout::from_size_align_unchecked(l.size().max(1).div_ceil(GRAIN) * GRAIN, GRAIN)),
        }
    }

    #[inline]
    unsafe fn dealloc(&self, p: *mut u8, l: Layout) {
        if !small(&l) {
            return System.dealloc(p, l);
        }
        let class = (l.size() + GRAIN - 1) / GRAIN;
        // a block that cannot be recorded (TLS destroyed) is simply leaked
        let _ = LOCAL.try_with(|loc| {
            let loc = &mut *loc.get();
            *(p as *mut *mut u8) = loc.free[class];
            loc.free[class] = p;
        });
    }

    #[inline]
    unsafe fn realloc(&self, p: *mut u8, l: Layout, new_size: usize) -> *mut u8 {
        let nl = Layout::from_size_align_unchecked(new_size, l.align());
        if !small(&l) && !small(&nl) {
            return System.realloc(p, l, new_size);
        }
        if small(&l) && small(&nl) && (l.size() + GRAIN - 1) / GRAIN == (new_size + GRAIN - 1) / GRAIN {
            return p;
        }
        let np = self.alloc(nl);
        if !np.is_null() {
            std::ptr::copy_nonoverlapping(p, np, l.size().min(new_size));
            self.dealloc(p, l);
        }
        np
    }
}
