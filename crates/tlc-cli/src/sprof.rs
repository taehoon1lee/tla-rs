//! Diagnostics only (feature `sprof`, Windows): a sampling profiler without external tools.
//!
//! A sampler thread suspends the profiled thread every ~1 ms, reads RIP and walks the frame-pointer chain
//! (build with `RUSTFLAGS="-C force-frame-pointers=yes"`), and writes the raw samples to `$TLCRS_SPROF`.
//! `tmp/symbolize.py` resolves the addresses with the COFF symbol table of the executable.
#![allow(non_snake_case, clippy::missing_safety_doc)]

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

type Handle = isize;

#[repr(C, align(16))]
struct Context([u8; 1232]);

extern "system" {
    fn OpenThread(access: u32, inherit: i32, tid: u32) -> Handle;
    fn GetCurrentThreadId() -> u32;
    fn SuspendThread(h: Handle) -> u32;
    fn ResumeThread(h: Handle) -> u32;
    fn GetThreadContext(h: Handle, ctx: *mut Context) -> i32;
    fn GetModuleHandleW(name: *const u16) -> isize;
    fn CloseHandle(h: Handle) -> i32;
}
#[link(name = "winmm")]
extern "system" {
    fn timeBeginPeriod(ms: u32) -> u32;
}

pub struct Sampler {
    stop: Arc<AtomicBool>,
    join: Option<std::thread::JoinHandle<Vec<Vec<u64>>>>,
    path: String,
}

fn rd(ctx: &Context, off: usize) -> u64 {
    u64::from_le_bytes(ctx.0[off..off + 8].try_into().unwrap())
}

/// Start sampling the calling thread when `TLCRS_SPROF=<file>` is set.
pub fn start() -> Option<Sampler> {
    let path = std::env::var("TLCRS_SPROF").ok()?;
    let tid = unsafe { GetCurrentThreadId() };
    let stop = Arc::new(AtomicBool::new(false));
    let st = stop.clone();
    let join = std::thread::spawn(move || {
        unsafe { timeBeginPeriod(1) };
        let h = unsafe { OpenThread(0x0002 | 0x0008 | 0x0010, 0, tid) }; // SUSPEND_RESUME | GET_CONTEXT | QUERY_INFORMATION
        let mut samples: Vec<Vec<u64>> = Vec::new();
        let mut ctx = Context([0; 1232]);
        while !st.load(Ordering::Relaxed) {
            std::thread::sleep(std::time::Duration::from_millis(1));
            unsafe {
                if SuspendThread(h) == u32::MAX {
                    continue;
                }
                ctx.0[0x30..0x34].copy_from_slice(&0x0010_0003u32.to_le_bytes()); // CONTROL | INTEGER
                let mut stack = vec![];
                if GetThreadContext(h, &mut ctx) != 0 {
                    let (rip, rsp, mut rbp) = (rd(&ctx, 0xF8), rd(&ctx, 0x98), rd(&ctx, 0xA0));
                    stack.push(rip);
                    // frame-pointer walk (the thread is suspended, its stack is stable)
                    let mut last = rsp;
                    for _ in 0..48 {
                        if rbp < last || rbp % 8 != 0 || rbp > rsp + (1 << 28) {
                            break;
                        }
                        let ret = *((rbp + 8) as *const u64);
                        let next = *(rbp as *const u64);
                        if ret == 0 {
                            break;
                        }
                        stack.push(ret);
                        if next <= rbp {
                            break;
                        }
                        last = rbp + 8;
                        rbp = next;
                    }
                    // always append a raw scan of the top of the stack (return-address-like words pointing into the image),
                    // separated by a 0: useful for leaf functions whose frame chain is broken
                    stack.push(0);
                    let img = GetModuleHandleW(std::ptr::null()) as u64;
                    let mut found = 0;
                    for k in 0..64u64 {
                        let w = *((rsp + k * 8) as *const u64);
                        if w > img + 0x1000 && w < img + 0x400000 {
                            stack.push(w);
                            found += 1;
                            if found >= 4 {
                                break;
                            }
                        }
                    }
                }
                ResumeThread(h);
                if !stack.is_empty() {
                    samples.push(stack);
                }
            }
        }
        unsafe { CloseHandle(h) };
        samples
    });
    Some(Sampler { stop, join: Some(join), path })
}

impl Sampler {
    pub fn finish(mut self) {
        self.stop.store(true, Ordering::Relaxed);
        let samples = self.join.take().unwrap().join().unwrap_or_default();
        let base = unsafe { GetModuleHandleW(std::ptr::null()) } as u64;
        let mut out = format!("BASE {:x}\n", base);
        for s in &samples {
            let line: Vec<String> = s.iter().map(|a| format!("{:x}", a)).collect();
            out.push_str(&line.join(" "));
            out.push('\n');
        }
        let _ = std::fs::write(&self.path, out);
        eprintln!("sprof: {} samples -> {}", samples.len(), self.path);
    }
}
