//! A small, fast global allocator for the model checker: the Windows process heap (the `System` allocator) takes a lock
//! and is slow for the millions of tiny short-lived allocations the evaluator performs. Small blocks come from
//! per-thread size-class free lists carved out of large chunks; everything else goes to `System`.
//!
//! The per-thread state lives in a raw Win32 TLS slot read straight from the TEB (`gs:[0x1480 + 8*index]`): Rust's
//! `thread_local!` on windows-gnu goes through a destructor-registration guard (`lock`-prefixed atomics) on every
//! access, which made each alloc/free ~16 ns.

use std::alloc::{GlobalAlloc, Layout, System};
use std::ptr::null_mut;
use std::sync::atomic::{AtomicU32, Ordering};

const GRAIN: usize = 16;
const MAX_SMALL: usize = 4096;
const NCLASS: usize = MAX_SMALL / GRAIN + 1;
const CHUNK: usize = 1 << 20;

#[repr(C)]
struct Local {
    free: [*mut u8; NCLASS],
    bump: *mut u8,
    end: *mut u8,
}

extern "system" {
    fn TlsAlloc() -> u32;
    fn TlsGetValue(idx: u32) -> *mut u8;
    fn TlsSetValue(idx: u32, v: *mut u8) -> i32;
}

const TLS_UNSET: u32 = u32::MAX;
static TLS_INDEX: AtomicU32 = AtomicU32::new(TLS_UNSET);

pub struct FastAlloc;

#[inline]
fn small(l: &Layout) -> bool {
    l.size() <= MAX_SMALL && l.align() <= GRAIN
}

#[cold]
#[inline(never)]
unsafe fn slow_local() -> *mut Local {
    // allocate the TLS index lazily (racing threads: the loser frees its index)
    let mut idx = TLS_INDEX.load(Ordering::Acquire);
    if idx == TLS_UNSET {
        let n = TlsAlloc();
        match TLS_INDEX.compare_exchange(TLS_UNSET, n, Ordering::AcqRel, Ordering::Acquire) {
            Ok(_) => idx = n,
            Err(cur) => idx = cur,
        }
    }
    let p = TlsGetValue(idx) as *mut Local;
    if !p.is_null() {
        return p;
    }
    let l = System.alloc(Layout::new::<Local>()) as *mut Local;
    if l.is_null() {
        return l;
    }
    std::ptr::write(l, Local { free: [null_mut(); NCLASS], bump: null_mut(), end: null_mut() });
    TlsSetValue(idx, l as *mut u8);
    l
}

/// the calling thread's allocator state (never freed: its blocks may be released by other threads)
#[inline(always)]
unsafe fn local() -> *mut Local {
    let idx = TLS_INDEX.load(Ordering::Relaxed);
    if idx < 64 {
        let p: *mut Local;
        // TEB.TlsSlots[idx] at gs:[0x1480 + 8 * idx]
        std::arch::asm!("mov {}, gs:[{}]", out(reg) p, in(reg) 0x1480usize + 8 * idx as usize, options(nostack, readonly, preserves_flags));
        if !p.is_null() {
            return p;
        }
    }
    slow_local()
}

unsafe impl GlobalAlloc for FastAlloc {
    #[inline]
    unsafe fn alloc(&self, l: Layout) -> *mut u8 {
        if !small(&l) {
            return System.alloc(l);
        }
        let class = (l.size() + GRAIN - 1) / GRAIN;
        let loc = local();
        if loc.is_null() {
            return System.alloc(Layout::from_size_align_unchecked(class.max(1) * GRAIN, GRAIN));
        }
        let loc = &mut *loc;
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
    }

    #[inline]
    unsafe fn dealloc(&self, p: *mut u8, l: Layout) {
        if !small(&l) {
            return System.dealloc(p, l);
        }
        let class = (l.size() + GRAIN - 1) / GRAIN;
        let loc = local();
        if loc.is_null() {
            return; // leaked
        }
        let loc = &mut *loc;
        *(p as *mut *mut u8) = loc.free[class];
        loc.free[class] = p;
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
