//! tlc-rs — Rust port of TLC (the TLA+ model checker) and SANY (the TLA+ front-end).
//!
//! Harness protocol (see harness/SCHEMA.md):
//!   tlc-rs [--lib DIR]... sany -error-codes FILE            ~ java tla2sany.SANY -error-codes FILE
//!   tlc-rs [--lib DIR]... tlc  -tool -workers 1 ... SPEC    ~ java tlc2.TLC -tool -workers 1 ... SPEC
//! Output must be TLC/SANY-compatible text on stdout; the process exit code must equal Java's.
//!
//! This file is infrastructure: keep the protocol stable. Put semantics in the library crates.

mod alloc;
#[cfg(feature = "sprof")]
mod sprof;

#[global_allocator]
static GLOBAL: alloc::FastAlloc = alloc::FastAlloc;

use std::path::{Path, PathBuf};
use tla_sany::Resolver;
use tlc_core::mp::{self, Reporter};
use tlc_core::TlcOptions;

/// Deep recursion in the evaluator/parser: run the real work on a thread with a big stack.
const STACK: usize = 512 * 1024 * 1024;
const PANIC_EXIT: i32 = 198;

fn usage() -> ! {
    eprintln!(
        "usage: tlc-rs [--lib DIR]... sany [-error-codes] FILE\n\
         \x20      tlc-rs [--lib DIR]... tlc [-tool] [-workers N] [-fp N] [-seed N] [-lncheck MODE] [-noGenerateSpecTE]\n\
         \x20             [-metadir DIR] [-deadlock] [-continue] [-nowarning] [-view] [-maxSetSize N] [-inv EXPR]\n\
         \x20             [-config FILE] SPEC"
    );
    std::process::exit(1)
}

/// Port of the subset of `tlc2.TLC.handleParameters` the harness uses. Unknown flags are an error.
fn parse_tlc_args(args: &[String]) -> TlcOptions {
    let mut o = TlcOptions::default();
    let mut i = 0;
    let val = |i: &mut usize| -> String {
        *i += 1;
        args.get(*i).cloned().unwrap_or_else(|| usage())
    };
    let num = |s: String| -> i64 { s.parse().unwrap_or_else(|_| usage()) };
    let mut spec = None;
    while i < args.len() {
        match args[i].as_str() {
            "-tool" => o.tool = true,
            "-workers" => {
                let v = val(&mut i);
                o.workers = if v == "auto" { 1 } else { num(v) as usize };
            }
            "-fp" => o.fp_index = num(val(&mut i)),
            "-seed" => o.seed = num(val(&mut i)),
            "-lncheck" => o.lncheck = val(&mut i),
            "-noGenerateSpecTE" => o.no_generate_spec_te = true,
            "-metadir" => o.metadir = Some(PathBuf::from(val(&mut i))),
            "-deadlock" => o.check_deadlock = false,
            "-continue" => o.continue_after_error = true,
            "-nowarning" => o.no_warning = true,
            "-view" => o.use_view = true,
            "-maxSetSize" => o.max_set_size = num(val(&mut i)),
            "-inv" => o.extra_invariants.push(val(&mut i)),
            "-config" => o.config = Some(PathBuf::from(val(&mut i))),
            s if s.starts_with('-') => {
                eprintln!("tlc-rs: unsupported TLC option {s}");
                usage()
            }
            s => spec = Some(PathBuf::from(s)),
        }
        i += 1;
    }
    o.spec = spec.unwrap_or_else(|| usage());
    o
}

fn run(args: Vec<String>) -> i32 {
    #[cfg(feature = "sprof")]
    let sampler = sprof::start();
    let rc = run_inner(args);
    #[cfg(feature = "sprof")]
    if let Some(s) = sampler {
        s.finish();
    }
    rc
}

fn run_inner(args: Vec<String>) -> i32 {
    let mut libs = Vec::new();
    let mut i = 0;
    while i < args.len() && args[i] == "--lib" {
        libs.push(PathBuf::from(args.get(i + 1).cloned().unwrap_or_else(|| usage())));
        i += 2;
    }
    let sub = args.get(i).cloned().unwrap_or_else(|| usage());
    let rest = &args[i + 1..];
    match sub.as_str() {
        "sany" => {
            let file = rest.iter().rev().find(|a| !a.starts_with('-')).cloned().unwrap_or_else(|| usage());
            let flags: Vec<String> = rest.iter().filter(|a| a.starts_with('-')).cloned().collect();
            // standalone SANY: ToolIO.getUserDir() is unset -> modules are looked up in the working directory
            let cwd = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
            let resolver = Resolver::new(cwd, libs);
            let mut rep = Reporter::new(false);
            let rc = tla_sany::sany_main(Path::new(&file), &flags, &resolver, &mut rep);
            rep.flush();
            rc
        }
        "tlc" => {
            let opts = parse_tlc_args(rest);
            // TLC: ToolIO.setUserDir(<directory of the spec>)
            let spec_dir = opts
                .spec_file()
                .parent()
                .map(|p| if p.as_os_str().is_empty() { PathBuf::from(".") } else { p.to_path_buf() })
                .unwrap_or_else(|| PathBuf::from("."));
            let resolver = Resolver::new(spec_dir, libs);
            let mut rep = Reporter::new(opts.tool);
            let rc = tlc_check::run(&opts, &resolver, &mut rep);
            rep.flush();
            rc
        }
        _ => usage(),
    }
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let tool = args.iter().any(|a| a == "-tool");
    let h = std::thread::Builder::new().stack_size(STACK).spawn(move || run(args)).expect("spawn worker thread");
    let rc = match h.join() {
        Ok(rc) => rc,
        Err(e) => {
            let msg = e
                .downcast_ref::<String>()
                .cloned()
                .or_else(|| e.downcast_ref::<&str>().map(|s| s.to_string()))
                .unwrap_or_else(|| "unknown panic".into());
            let mut rep = Reporter::new(tool);
            rep.error(mp::RUST_PANIC, &format!("tlc-rs panicked: {msg}"));
            rep.flush();
            PANIC_EXIT
        }
    };
    std::process::exit(rc)
}
