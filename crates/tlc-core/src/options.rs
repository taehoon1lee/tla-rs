//! TLC command-line options (subset of `tlc2/TLC.java` `handleParameters`, l.~480-1100) used by the harness.
//! Field names follow the Java globals (`TLCGlobals.*`, fields of `TLC`).

use std::path::PathBuf;

#[derive(Debug, Clone)]
pub struct TlcOptions {
    /// `-tool`: frame every message (see `mp`).
    pub tool: bool,
    /// `-workers N` (the harness always passes 1).
    pub workers: usize,
    /// `-fp N`: index of the irreducible polynomial for FP64 (Java default: random).
    pub fp_index: i64,
    /// `-seed N`: seed for RandomElement & co. (Java default: random).
    pub seed: i64,
    /// `-lncheck default|final|...` (the harness always passes `final`).
    pub lncheck: String,
    /// `-noGenerateSpecTE`
    pub no_generate_spec_te: bool,
    /// `-metadir DIR`: where Java keeps states/ (Rust may ignore it or use it for temporary files).
    pub metadir: Option<PathBuf>,
    /// `-deadlock`: DISABLES deadlock checking (`TLCGlobals.checkDeadlock = false`).
    pub check_deadlock: bool,
    /// `-continue`: keep going after an invariant violation.
    pub continue_after_error: bool,
    /// `-nowarning`
    pub no_warning: bool,
    /// `-view`: apply VIEW when printing states.
    pub use_view: bool,
    /// `-maxSetSize N` (`TLCGlobals.setBound`, default 1000000).
    pub max_set_size: i64,
    /// `-inv EXPR` (additional invariants given on the command line).
    pub extra_invariants: Vec<String>,
    /// `-config FILE` (Java strips a trailing `.cfg`; default: spec name + `.cfg`).
    pub config: Option<PathBuf>,
    /// The spec file (`.tla` optional, as in Java).
    pub spec: PathBuf,
}

impl Default for TlcOptions {
    fn default() -> Self {
        TlcOptions {
            tool: false,
            workers: 1,
            fp_index: 0,
            seed: 0,
            lncheck: "default".into(),
            no_generate_spec_te: false,
            metadir: None,
            check_deadlock: true,
            continue_after_error: false,
            no_warning: false,
            use_view: false,
            max_set_size: 1_000_000,
            extra_invariants: Vec::new(),
            config: None,
            spec: PathBuf::new(),
        }
    }
}

impl TlcOptions {
    /// Path of the spec file with `.tla` appended when missing (Java `TLC.handleParameters`).
    pub fn spec_file(&self) -> PathBuf {
        let s = self.spec.to_string_lossy();
        if s.ends_with(".tla") {
            self.spec.clone()
        } else {
            PathBuf::from(format!("{s}.tla"))
        }
    }

    /// Path of the .cfg file: `-config X[.cfg]` or `<spec>.cfg`.
    pub fn config_file(&self) -> PathBuf {
        match &self.config {
            Some(c) => {
                let s = c.to_string_lossy();
                if s.ends_with(".cfg") {
                    c.clone()
                } else {
                    PathBuf::from(format!("{s}.cfg"))
                }
            }
            None => self.spec_file().with_extension("cfg"),
        }
    }
}
