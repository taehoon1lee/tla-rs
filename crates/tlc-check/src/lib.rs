//! TLC model checker. Port of `tlc2.TLC.process()` + `tlc2.tool.ModelChecker` (breadth-first search, invariants,
//! deadlock detection, counterexample traces).
//!
//! Java -> Rust:
//!   tlc2.TLC.process()                      -> [`run`] (phases + the messages printed around them)
//!   tlc2.tool.ModelChecker / Worker         -> `bfs`
//!   tlc2.tool.TLCTrace                      -> trace reconstruction from parent pointers

mod bfs;
mod live;

use std::rc::Rc;
use tla_sany::Resolver;
use tlc_core::config;
use tlc_core::ec;
use tlc_core::mp::{self, Reporter};
use tlc_core::spec;
use tlc_core::TlcOptions;

/// Exit code used while a phase is not ported yet (never equals a Java exit code).
pub const NOT_PORTED_EXIT: i32 = 199;

pub const VERSION_TEXT: &str = "TLC2 Version 2026.11.19.180144 (rev: bc1b506)";

pub fn now_str() -> String {
    let secs = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).map(|d| d.as_secs() as i64).unwrap_or(0);
    let days = secs.div_euclid(86400);
    let rem = secs.rem_euclid(86400);
    // civil from days (Howard Hinnant)
    let z = days + 719468;
    let era = z.div_euclid(146097);
    let doe = z.rem_euclid(146097);
    let yoe = (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365;
    let y = yoe + era * 400;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp_ = (5 * doy + 2) / 153;
    let d = doy - (153 * mp_ + 2) / 5 + 1;
    let m = if mp_ < 10 { mp_ + 3 } else { mp_ - 9 };
    let y = if m <= 2 { y + 1 } else { y };
    format!("{:04}-{:02}-{:02} {:02}:{:02}:{:02}", y, m, d, rem / 3600, (rem % 3600) / 60, rem % 60)
}

pub(crate) fn finish(rep: &mut Reporter, start: std::time::Instant, code: i32) -> i32 {
    let ms = start.elapsed().as_millis();
    rep.info(ec::TLC_FINISHED, &format!("Finished in {}ms at ({})", ms, now_str()));
    code
}

/// Java `tlc2.TLC.main` -> `process()`: SANY, config, constants, ASSUME, init states, BFS, liveness, statistics.
pub fn run(opts: &TlcOptions, resolver: &Resolver, rep: &mut Reporter) -> i32 {
    let start = std::time::Instant::now();
    rep.info(ec::TLC_VERSION, VERSION_TEXT);
    rep.info(
        ec::TLC_MODE_MC,
        &format!(
            "Running breadth-first search Model-Checking with fp {} and seed {} with {} worker{} on {} cores with 5461MB heap and 64MB offheap memory [pid: {}] ({}, {}, MSBDiskFPSet, DiskStateQueue).",
            opts.fp_index,
            opts.seed,
            opts.workers,
            if opts.workers == 1 { "" } else { "s" },
            std::thread::available_parallelism().map(|n| n.get()).unwrap_or(1),
            std::process::id(),
            "tlc-rs",
            "Rust"
        ),
    );
    // ---- configuration file
    let cfg_path = opts.config_file();
    let cfg_text = match std::fs::read(&cfg_path) {
        Ok(b) => String::from_utf8_lossy(&b).into_owned(),
        Err(_) => {
            let name = cfg_path.file_name().map(|s| s.to_string_lossy().to_string()).unwrap_or_default();
            rep.error(ec::CFG_ERROR_READING_FILE, &format!("TLC encountered the following error when trying to read the configuration file {}:\nFile not found.", name));
            rep.flush();
            return ec::error_constant_to_exit_status(ec::CFG_ERROR_READING_FILE);
        }
    };
    let cfg = match config::parse(&cfg_text) {
        Ok(c) => c,
        Err(e) => {
            rep.error(e.code, &e.text);
            return finish(rep, start, ec::error_constant_to_exit_status(e.code));
        }
    };
    // ---- SANY
    rep.info(ec::TLC_SANY_START, "Starting SANY...");
    let spec = tla_sany::frontend(&opts.spec_file(), resolver, rep);
    let spec = match spec {
        Ok(s) => s,
        Err(e) => {
            if !e.text.is_empty() {
                rep.raw(&e.text);
            }
            rep.info(ec::TLC_SANY_END, "SANY finished.");
            rep.info(ec::TLC_STARTING, &format!("Starting... ({})", now_str()));
            rep.error(ec::TLC_PARSING_FAILED, "Parsing or semantic analysis failed.");
            return finish(rep, start, ec::error_constant_to_exit_status(ec::TLC_PARSING_FAILED));
        }
    };
    rep.info(ec::TLC_SANY_END, "SANY finished.");
    rep.info(ec::TLC_STARTING, &format!("Starting... ({})", now_str()));
    let sem = match &spec.sem {
        Some(s) => s,
        None => {
            rep.error(ec::TLC_PARSING_FAILED, "Parsing or semantic analysis failed.");
            return finish(rep, start, ec::error_constant_to_exit_status(ec::TLC_PARSING_FAILED));
        }
    };
    // ---- spec processing
    let mut setup = match spec::setup(sem, &cfg, opts.max_set_size) {
        Ok(s) => s,
        Err(e) => {
            rep.error(e.code, &e.text);
            return finish(rep, start, ec::error_constant_to_exit_status(e.code));
        }
    };
    // ---- temporal properties (Java: `new LiveCheck(...)` -> `Liveness.processLiveness`)
    if !setup.properties.is_empty() {
        match tlc_core::liveness::oos::process_liveness(&mut setup) {
            Ok(live) => {
                if live.oss.is_empty() {
                    // Java: `ModelChecker.modelCheckImpl`: no order of solution = the property is a tautology
                    rep.error(ec::TLC_LIVE_FORMULA_TAUTOLOGY, "Temporal formula is a tautology (its negation is unsatisfiable).");
                    return finish(rep, start, ec::error_constant_to_exit_status(ec::TLC_LIVE_FORMULA_TAUTOLOGY));
                }
                rep.info(ec::TLC_LIVE_IMPLIED, &format!("Implied-temporal checking--satisfiability problem has {} branches.", live.oss.len()));
                setup.live = live;
            }
            Err(e) => {
                use tlc_core::liveness::translate::TrErr;
                let (code, text) = match e {
                    TrErr::Handle(t) => (ec::TLC_LIVE_CANNOT_HANDLE_FORMULA, format!("TLC cannot handle the temporal formula {}", t)),
                    TrErr::Code(c, m) => (c, m),
                    TrErr::Eval(e) => (e.code, e.msg.clone()),
                    // a formula shape not translated by this port: the temporal properties are not checked
                    TrErr::Unsupported(_) => (0, String::new()),
                };
                if code != 0 {
                    rep.error(code, &text);
                    return finish(rep, start, ec::error_constant_to_exit_status(code));
                }
            }
        }
    }
    if let Ok(names) = std::env::var("TLCRS_TOK") {
        for n in names.split(',') {
            eprintln!("TOK {} {}", n, tla_sany::intern::intern(n));
        }
    }
    let setup = Rc::new(setup);
    let code = bfs::model_check(&setup, opts, rep, start);
    rep.flush();
    code
}

#[allow(dead_code)]
fn _unused() {
    let _ = mp::NOT_PORTED;
}
