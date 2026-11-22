# NOTES — durable knowledge (keep bullets short; newest at the bottom of each section)

## Environment
- Windows 11, Rust stable via rustup, host `x86_64-pc-windows-gnu`, **no C compiler** → pure-Rust crates only.
- `cargo` lives in `%USERPROFILE%\.cargo\bin`; add it to PATH if a shell does not see it.
- Java 25 (only for the oracle). TLC jar: `reference/bin/tla2tools.jar` (1.8.0, rev bc1b506 = source in
  `reference/tlaplus`), `reference/bin/CommunityModules-deps.jar` (release 202611191749 = `reference/community-modules`).
- `reference/{tlaplus,examples,community-modules,tlapm,apalache}` are git submodules pinned to the commits the
  goldens were made from; the driver resets them every iteration. Never `git add` a submodule change.
- Ad-hoc Java/Rust comparisons on your own scratch spec: `python harness/oracle.py tlc tmp/x/S.tla --diff`.

## Harness facts
- Every TLC run uses `-tool -workers 1 -fp 0 -seed 1 -lncheck final -noGenerateSpecTE -metadir <tmp>`, cwd = an
  empty temp dir, absolute spec/cfg paths. TLC test models additionally get `-deadlock` (= NO deadlock check)
  unless their JUnit test overrides `checkDeadLock()`, plus the flags from the test (`-continue`, `-view`, ...).
- SANY runs as `tla2sany.SANY -error-codes FILE` with cwd = the module's directory (standalone SANY looks up
  sibling modules in the working directory; TLC looks in the spec's directory).
- Java wall time includes JVM start (~0.3-0.5 s): tiny specs are easy perf wins, big state spaces are not.
- Goldens of models that finished in < 60 s were produced twice; fields that differed are listed in the golden's
  `nondet` and are not compared. Java timeouts (600 s) are unscored. Models with Java > 60 s are "heavy"
  (skipped unless `--heavy`).
- Golden corpus: 1140 modules (1107 ok / 16 semantic error / 17 exit -1); 364 scored models (217 success,
  47 liveness, 38 safety, 25 eval failure, 15 assumption, 10 config error, 7 exit 255, ...), 13 heavy, 7 Java
  timeouts. Java total for the scored models 758 s. Java timings were measured with 3-4 JVMs running in parallel
  (slightly pessimistic for Java), wall clock incl. JVM start.
- Only the module NAME of SANY's `Parsing file <path>` lines is compared (Java prints temp-extraction paths for
  standard modules); print e.g. `Parsing file <dir>/<Module>.tla` — the path must end in `<Module>.tla`
  followed by a space or end of line.
- `check.py` keys: parse-corpus ids look like `ex/<spec dir>/<module>`, `tt/<test-model path>`, `cm/<module>`;
  check-corpus ids are `ex/<spec dir>/<cfg name>` and `tt/<JUnit test class>`.

## Java quirks (add as you discover them)
- SANY `-error-codes` exit codes: 0 ok, 4 semantic/level error, but most PARSE failures exit with -1 (shown by
  Windows as 4294967295; the harness maps it back to -1), not 2.
- TLC exit codes = `EC.ExitStatus` (`tlc_core::ec::exit_status`): 0 ok, 10 assumption, 11 deadlock, 12 safety,
  13 liveness, 14 assert, 75/76/77 evaluation failures, 150 spec parse, 151 config, 255 other errors.
- Strings and model values compare by `UniqueString.compareTo` = **intern order** (`tok`, the position in the
  intern table = order of first interning while parsing/processing), NOT alphabetically. This decides the
  printing order of sets of strings and which element CHOOSE picks. Sets compare by size first, then elementwise
  after normalization (`SetEnumValue.compareTo`).
- Print/PrintT output goes to stdout between messages, in evaluation order (Init's Print may run again during
  liveness checking).

## Design decisions
- Output protocol = TLC's own `-tool` text (so tlc-rs is usable as a drop-in TLC). See harness/SCHEMA.md.

## HARNESS ISSUES (write evidence here instead of editing harness/)
