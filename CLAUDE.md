# tlc-rs — Rust rewrite of TLC + SANY (TLA+ tools 1.8.0)

Goal: a Rust CLI `tlc-rs` that gives **the same answers as Java TLC 1.8.0** (`tla2tools.jar`) on the TLA+
Examples and on TLC's own test models, and is **not slower** than Java. You work in a loop; each iteration
does ONE small task. The per-iteration procedure is in `loop/PROMPT.md`. The task list is `loop/TASKS.md`.

## Directory map
| path | what | may you edit? |
|---|---|---|
| `crates/tla-sany` | lexer, parser, module loading, semantic analysis, level checking (port of `tla2sany`) | YES |
| `crates/tlc-core` | values, .cfg parser, spec processing, evaluator (`Tool`), built-in modules, EC/MP messages | YES |
| `crates/tlc-check` | BFS model checker, fingerprint set, traces, liveness (port of `tlc2.tool.ModelChecker`, `tlc2.tool.liveness`) | YES |
| `crates/tlc-cli` | `tlc-rs` binary; harness protocol | only to add features; keep the protocol (`harness/SCHEMA.md`) |
| `loop/TASKS.md`, `loop/PROGRESS.md`, `loop/NOTES.md` | your plan / log / knowledge base | YES (keep them short) |
| `docs/JAVA_MAP.md` | Java→Rust file map | YES (add what you learn) |
| `harness/**` (scripts, goldens, corpus) | the judge | **NO — never** |
| `reference/**` | Java source, examples, libraries (git submodules, pinned) + generated jars/library dir (read-only) | **NO** — never commit a submodule change |
| `loop/PROMPT.md`, `loop/run-loop.ps1`, `loop/haiku-settings.json`, `CLAUDE.md`, `.claude/` | loop driver + rules | **NO** |

Java source root: `reference/tlaplus/tlatools/org.lamport.tlatools/` (= `TT`; sources under `TT/src`).
Key entry points (see `docs/JAVA_MAP.md` for the full map):
- Grammar: `TT/javacc/tla+.jj` (JavaCC; `TT/src/tla2sany/parser/TLAplusParser.java` is GENERATED from it)
- SANY: `TT/src/tla2sany/drivers/SANY.java`, `modanalyzer/SpecObj.java`, `semantic/Generator.java`, `semantic/LevelNode.java`
- TLC: `TT/src/tlc2/TLC.java` (CLI + `process()`), `tool/impl/{ModelConfig,SpecProcessor,Tool}.java`, `tool/ModelChecker.java`,
  `value/impl/*.java`, `module/*.java`, `tool/liveness/*.java`, `output/{EC,MP}.java`
- Community modules (TLA+ + Java overrides): `reference/community-modules/modules/` (`tlc2/overrides/*.java`)
- Corpus: `reference/examples/specifications/` (+ `manifest.json` per spec), `TT/test-model/` (+ JUnit tests in `TT/test/`)

## Commands (run from the repo root = the directory containing this file)
```
cargo build --release                       # binary: target/release/tlc-rs.exe
cargo test -q                               # unit tests (add tests for every ported piece)
python harness/check.py --quick             # smoke set, ~1 min
python harness/check.py --kind parse        # only the SANY corpus (1140 modules; levels syntax/parse/parse_msg)
python harness/check.py --kind check        # only the TLC models
python harness/check.py --filter <substr>   # subset by id
python harness/check.py --id <id> --verbose # side-by-side Java vs Rust for one entry
python harness/check.py --gate              # FULL run; exit 1 on regression vs harness/results/best.json
python harness/check.py --update-best       # FULL run; record new baseline (refused if regression)
python harness/check.py --perf --filter X   # sequential timing (trustworthy perf numbers)
python harness/oracle.py tlc  tmp/x/S.tla --diff   # Java vs Rust on YOUR scratch spec, normalized diff
python harness/oracle.py sany tmp/x/S.tla --java --raw   # raw Java SANY output
target/release/tlc-rs.exe tlc -tool -workers 1 -config X.cfg X.tla   # run one model by hand
```
If `cargo` is not found: `export PATH="$HOME/.cargo/bin:$PATH"` (bash) / `$env:PATH="$env:USERPROFILE\.cargo\bin;$env:PATH"` (PowerShell).

## Hard rules
1. **Port, don't invent.** When Rust differs from Java (exit code, message text, state counts, trace, speed), read
   the corresponding Java code and mirror its logic: enumeration order of init/next states, set normalization and
   value ordering, CHOOSE, printing of values, message templates (`MP.java`), error texts, positions.
2. **No cheating.** Never read harness/golden* or the manifests' expected results from Rust code, never
   special-case file/module/spec names, never hard-code answers or state counts, never print a message that the
   real pipeline did not produce (e.g. "Computing initial states" before actually computing them), never weaken
   or skip harness checks. A pass must come from real logic.
3. **Never regress.** Before committing, `python harness/check.py --gate` must exit 0. If it fails, fix or revert.
4. **Pure-Rust dependencies only** (toolchain `x86_64-pc-windows-gnu`, no C/C++ compiler). Prefer std. Nothing
   external is used yet; ask in `loop/NOTES.md` before adding a crate.
5. Small steps: one task per iteration, commit when it builds, tests pass and the gate passes.
6. Keep output small: pipe long outputs through `head`/`tail`; read big Java files by line ranges
   (`grep -n` first, then ~150 lines around the hit). Never cat a whole 1000+ line file (Tool.java is 4136 lines,
   Generator.java 9736, tla+.jj 4417).
7. Library code must not panic on user input: return errors that become the right TLC/SANY messages. A panic is
   reported as code 9998 (always a failure). Not-yet-ported features must report code 9999 (see SCHEMA.md).
8. Never write into `reference/` or `harness/`; scratch specs go under `tmp/`.

## Architecture contract (CLI ⇄ libraries)
- `tla_sany::sany_main(file, flags, &Resolver, out) -> i32` ≈ `tla2sany.drivers.SANY.SANYmain` with `-error-codes`.
- `tla_sany::frontend(root_file, &Resolver, out) -> Result<Spec, FrontEndError>` ≈ `SANY.frontEndMain` (used by TLC).
- `tla_sany::Resolver::locate(module)` ≈ `SimpleFilenameToStream` (done: user dir → standard modules → `--lib` dirs).
- `tlc_check::run(&TlcOptions, &Resolver, &mut Reporter) -> i32` ≈ `tlc2.TLC.process()`; returns the exit code.
- `tlc_core::mp::Reporter` = Java `MP` + `ToolIO.out` (tool-mode framing); `tlc_core::ec` = all `EC` codes +
  `error_constant_to_exit_status` (generated from EC.java — do not hand-edit the constants).

## Style
- Rust 2021, `cargo fmt` style, no `unsafe` unless measured necessary.
- Put a `//! Port of <java path>` header in every module, and `// Java: Class.method` comments on non-obvious
  ported functions, so the next iteration can find the counterpart quickly.
- Prefer arena/index-based trees (`Vec<Node>` + `NodeId(u32)`) and interned strings (Java `UniqueString`) over
  `Rc<RefCell<>>` graphs. Values: an enum with cheap clones (`Rc`/`Arc` inside), normalized (sorted) sets like
  `SetEnumValue.normalize()`.
