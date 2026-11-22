//! Port of `tlc2/output/MP.java` (message printing) — framing done; message templates are ported as needed.
//!
//! With `-tool` every message is framed exactly like Java (`MP.getMessage`, l.378/407):
//! ```text
//! @!@!@STARTMSG <code>:<class> @!@!@
//! <text>
//! @!@!@ENDMSG <code> @!@!@
//! ```
//! Text that is not a message (Print/PrintT output, SANY's progress lines) is printed raw, in program order.
//! The harness (harness/tlcout.py) parses this stream; see harness/SCHEMA.md for what is compared.

use std::io::{self, Write};

/// `MP` message classes.
pub mod class {
    pub const NONE: i32 = 0;
    pub const ERROR: i32 = 1;
    pub const TLCBUG: i32 = 2;
    pub const WARNING: i32 = 3;
    pub const STATE: i32 = 4;
}

/// Harness-only codes (never produced by Java TLC). See harness/SCHEMA.md.
pub const NOT_PORTED: i32 = 9999;
pub const RUST_PANIC: i32 = 9998;

/// Buffered stdout writer shared by everything that prints (Java `ToolIO.out` + `MP`).
pub struct Reporter {
    pub tool: bool,
    out: io::BufWriter<io::Stdout>,
}

impl Reporter {
    pub fn new(tool: bool) -> Self {
        Reporter { tool, out: io::BufWriter::with_capacity(1 << 16, io::stdout()) }
    }

    /// Java `MP.printMessage/printError/printWarning/printState` after the template was filled in.
    pub fn message(&mut self, code: i32, class: i32, text: &str) {
        if self.tool {
            let _ = writeln!(self.out, "@!@!@STARTMSG {code}:{class} @!@!@\n{text}\n@!@!@ENDMSG {code} @!@!@");
        } else {
            // Java prefixes some classes in non-tool mode (see MP.getMessage); refine when needed.
            let _ = writeln!(self.out, "{text}");
        }
    }

    pub fn error(&mut self, code: i32, text: &str) {
        self.message(code, class::ERROR, text);
    }

    pub fn warning(&mut self, code: i32, text: &str) {
        self.message(code, class::WARNING, text);
    }

    pub fn info(&mut self, code: i32, text: &str) {
        self.message(code, class::NONE, text);
    }

    /// Raw line (Java `ToolIO.out.println`), e.g. the output of `Print`/`PrintT`.
    pub fn raw(&mut self, text: &str) {
        let _ = writeln!(self.out, "{text}");
    }

    pub fn flush(&mut self) {
        let _ = self.out.flush();
    }
}

impl Write for Reporter {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.out.write(buf)
    }
    fn flush(&mut self) -> io::Result<()> {
        self.out.flush()
    }
}

impl Drop for Reporter {
    fn drop(&mut self) {
        let _ = self.out.flush();
    }
}
