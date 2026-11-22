# tools/ — diagnostics for the loop (not part of the build, not used by the harness)

Build the sampling profiler once (separate target dir, frame pointers on):

    RUSTFLAGS="-C force-frame-pointers=yes" CARGO_TARGET_DIR=target-prof cargo build --release --features tlc-cli/sprof

* `python tools/prof.py <check-id> [--top N] [--lines <fn-substring>] [--callers <fn-substring>]` — runs the model with
  the harness arguments under the sampler (`TLCRS_SPROF`), prints self/inclusive profile by function; `--lines F` shows
  hot source lines inside functions matching F (DWARF line table, `dwarfline.py`); `--callers F` shows the stack-scan
  callers of F (for leaf functions without a frame chain).
* `python tools/profnode.py <check-id>` — node-kind profile (needs `--features "tlc-cli/sprof tlc-check/prof"`).
* `python tools/perf.py <id>... | --ex-slow` — sequential wall-clock of Rust vs the Java golden.
* `python tools/rr.py <check-id>` — run one corpus model with the harness arguments, print the output tail.

No symbolizer exists on this box (no nm/addr2line/gdb): `symbolize.py` reads the COFF symbol table and DWARF line
program of the PE directly.
