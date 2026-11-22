//! TLC model checker. Port of the BFS model checker and liveness checking of TLC 1.8.0.
//!
//! Java -> Rust (fill in as you port; keep `docs/JAVA_MAP.md` in sync):
//!   tlc2.TLC.process()                      -> [`run`] (phases + the messages printed around them)
//!   tlc2.tool.AbstractChecker, ModelChecker, Worker -> `bfs` (init states, BFS, invariants, deadlock, -continue)
//!   tlc2.tool.fp.* (FPSet), tlc2.tool.queue.* (StateQueue) -> `fpset`, `queue` (in-memory is fine)
//!   tlc2.tool.TLCTrace (trace reconstruction)                -> `trace`
//!   tlc2.tool.liveness.* (Liveness, Tableau, LiveCheck, OrderOfSolution, SCC) -> `liveness`
//!
//! Public contract used by the CLI: [`run`] returns the process exit code (Java `EC.ExitStatus`).

use tla_sany::Resolver;
use tlc_core::ec;
use tlc_core::mp::{self, Reporter};
use tlc_core::TlcOptions;

/// Exit code used while a phase is not ported yet (never equals a Java exit code).
pub const NOT_PORTED_EXIT: i32 = 199;

pub const VERSION_TEXT: &str = "TLC2 Version 2026.11.19.180144 (rev: bc1b506)";

/// Java `tlc2.TLC.main` -> `process()`: SANY, config, constants, ASSUME, init states, BFS, liveness, statistics.
pub fn run(opts: &TlcOptions, resolver: &Resolver, rep: &mut Reporter) -> i32 {
    rep.info(ec::TLC_VERSION, &format!("{VERSION_TEXT} [tlc-rs {}]", env!("CARGO_PKG_VERSION")));
    rep.info(
        ec::TLC_MODE_MC,
        &format!(
            "Running breadth-first search Model-Checking with fp {} and seed {} with {} worker on tlc-rs.",
            opts.fp_index, opts.seed, opts.workers
        ),
    );
    rep.info(ec::TLC_SANY_START, "Starting SANY...");
    let spec = tla_sany::frontend(&opts.spec_file(), resolver, rep);
    if let Err(e) = &spec {
        rep.raw(&e.text); // Java prints SANY's error report before "SANY finished."
    }
    rep.info(ec::TLC_SANY_END, "SANY finished.");
    match spec {
        Ok(_spec) => {
            rep.info(ec::TLC_STARTING, "Starting...");
            rep.error(mp::NOT_PORTED, "tlc-rs: model checking is not ported yet (milestones M4+)");
        }
        Err(e) => {
            rep.info(ec::TLC_STARTING, "Starting...");
            if e.not_ported {
                rep.error(mp::NOT_PORTED, "tlc-rs: the SANY front-end is not ported yet (milestone M1)");
            } else {
                rep.error(ec::TLC_PARSING_FAILED, "Parsing or semantic analysis failed.");
                rep.info(ec::TLC_FINISHED, "Finished in 0ms at (tlc-rs)");
                return ec::exit_status::ERROR_SPEC_PARSE;
            }
        }
    }
    rep.info(ec::TLC_FINISHED, "Finished in 0ms at (tlc-rs)");
    NOT_PORTED_EXIT
}
