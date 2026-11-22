//! TLA+ front-end. Port of `tla2sany` (SANY 2.2 as shipped in TLC 1.8.0).
//!
//! Java packages -> Rust modules (fill in as you port; keep `docs/JAVA_MAP.md` in sync):
//!   tla2sany.parser   (TLAplusParser.jj is the JavaCC grammar; TLAplusParser.java is GENERATED from it)
//!                                   -> `lexer`, `parser`
//!   tla2sany.st       (TreeNode, SyntaxTreeConstants)                      -> `syntax`
//!   tla2sany.modanalyzer (SpecObj, ParseUnit, module dependency order)     -> `modules`
//!   tla2sany.semantic (Generator, Context, ModuleNode, OpDefNode, ..., levels) -> `semantic`
//!   tla2sany.drivers.SANY (frontEndMain, SANYmain, exit codes)            -> this file
//!   util.SimpleFilenameToStream                                           -> `resolve` (done)
//!
//! Public contract used by the CLI and by tlc-core (extend, don't break):
//!   * [`sany_main`]  ~ `tla2sany.drivers.SANY.SANYmain(["-error-codes", file])`: prints SANY's text output
//!     to `out` and returns the process exit code (0 ok, 2 syntax, 4 semantic, -1 other, per `SanyExitCode`)
//!   * [`frontend`]   ~ `SANY.frontEndMain` as called by TLC: the parsed + analysed specification

pub mod analyze;
pub mod analyze_expr;
pub mod ast;
pub mod driver;
pub mod intern;
pub mod lexer;
pub mod modules;
pub mod ops;
pub mod parser;
pub mod resolve;
pub mod sem;
pub mod stdlib;

pub use resolve::{Located, Origin, Resolver};

use std::io::Write;
use std::path::Path;

/// Exit code used while a phase is not ported yet. It never equals a Java exit code, so it always scores as a
/// failure (honest "not implemented").
pub const NOT_PORTED_EXIT: i32 = 199;

/// Port of `tla2sany.drivers.SanyExitCode`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SanyExitCode {
    Ok = 0,
    SyntaxParsingFailure = 2,
    SemanticAnalysisOrLevelCheckingFailure = 4,
    Error = -1,
}

/// A fully parsed and semantically analysed specification (Java: `SpecObj` with its `ExternalModuleTable`).
pub struct Spec {
    pub obj: modules::SpecObj,
    pub sem: Option<analyze::SemSpec>,
}

/// Why the front-end failed. `text` is what Java prints for it.
#[derive(Debug, Clone)]
pub struct FrontEndError {
    pub exit: SanyExitCode,
    pub text: String,
    pub not_ported: bool,
}

/// Parse + analyse `root_file` and everything it EXTENDS/INSTANCEs (Java `SANY.frontEndMain`).
/// Progress/error text goes to `out` exactly as Java prints it ("Parsing file ...", "Semantic processing of
/// module ...", error reports).
pub fn frontend(root_file: &Path, resolver: &Resolver, out: &mut dyn Write) -> Result<Spec, FrontEndError> {
    frontend_opts(root_file, resolver, out, true, true)
}

fn exit_from_code(c: i32) -> SanyExitCode {
    match c {
        0 => SanyExitCode::Ok,
        2 => SanyExitCode::SyntaxParsingFailure,
        4 => SanyExitCode::SemanticAnalysisOrLevelCheckingFailure,
        _ => SanyExitCode::Error,
    }
}

/// `SANY.parse` with the settings of the command line: semantic analysis / level checking switches.
pub fn frontend_opts(
    root_file: &Path,
    resolver: &Resolver,
    out: &mut dyn Write,
    semantic: bool,
    level_check: bool,
) -> Result<Spec, FrontEndError> {
    let obj = match modules::load_spec(root_file, resolver, out) {
        Ok(o) => o,
        Err(e) => {
            return Err(FrontEndError { exit: exit_from_code(e.exit), text: e.text, not_ported: false });
        }
    };
    if !semantic {
        return Ok(Spec { obj, sem: None });
    }
    let outcome = driver::analyze_spec(&obj, out, level_check, true);
    if outcome.error_level != 0 {
        return Err(FrontEndError { exit: exit_from_code(outcome.error_level), text: String::new(), not_ported: false });
    }
    Ok(Spec { obj, sem: outcome.spec })
}

/// `java tla2sany.SANY -error-codes FILE` (the CLI passes the other SANY flags through `args`).
/// Writes SANY's output to `out` and returns the exit code the process must exit with.
pub fn sany_main(file: &Path, args: &[String], resolver: &Resolver, out: &mut dyn Write) -> i32 {
    let mut semantic = true;
    let mut level = true;
    for a in args {
        match a.as_str() {
            "-S" | "-s" => semantic = !semantic,
            "-L" | "-l" => level = !level,
            _ => {}
        }
    }
    let _ = writeln!(out, "
****** SANY2 Version 2.2 created 08 July 2020
");
    if !file.is_file() && !file.with_extension("tla").is_file() {
        let _ = writeln!(out, "Cannot find the specified file {}.", file.display());
        return SanyExitCode::Error as i32;
    }
    match frontend_opts(file, resolver, out, semantic, level) {
        Ok(_) => SanyExitCode::Ok as i32,
        Err(e) => {
            if !e.text.is_empty() {
                let _ = writeln!(out, "{}", e.text);
            }
            if e.not_ported {
                NOT_PORTED_EXIT
            } else {
                e.exit as i32
            }
        }
    }
}
