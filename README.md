# tlc-rs — TLC + SANY (Java, TLA+ tools 1.8.0) → Rust rewrite, built as a loop-engineering environment

Opus built the environment; the actual porting is done by **separate Haiku sessions running in an iteration loop**
(same design as `../alloytoolRS`). There is a single judge: the score of `python harness/check.py` — the **same
answers** as Java TLC 1.8.0, and **not slower**.

## Layout
```
reference/                    (not in git, read-only; `python harness/setup.py` fetches it at pinned commits)
  tlaplus/                    github.com/tlaplus/tlaplus @ v1.8.0 (Java source being ported: tlatools/org.lamport.tlatools)
  examples/                   github.com/tlaplus/Examples (specs + manifest.json per spec)
  community-modules/          github.com/tlaplus/CommunityModules (modules/*.tla + Java overrides)
  tlapm/library, apalache/src/tla   TLAPS / Apalache modules some specs EXTEND
  tla-library/                assembled from the two above (on the module search path)
  bin/tla2tools.jar           official TLC 1.8.0 release (reference executor)
  bin/CommunityModules-deps.jar
harness/                      the judge — must not be edited inside the loop
  corpus.json                 1140 SANY modules (Examples, TLC test-model, CommunityModules) + 384 TLC models
                              (168 Examples manifest models with mode "exhaustive search", 216 TLC JUnit test models)
  golden/parse/, golden/check/   Java results (SANY exit/markers/module order/error text; TLC exit code, messages,
                              state counts, counterexample, output, wall time)
  tlcout.py                   parser for TLC -tool output and SANY output (applied to Java AND Rust)
  check.py                    runs Rust → compares with golden → scoreboard / regression check
  oracle.py                   ad-hoc Java-vs-Rust diff on any scratch spec
  quick.txt                   smoke set
  SCHEMA.md                   the protocol (invocations, compared fields)
crates/                       Rust workspace (filled in by Haiku)
  tla-sany  tlc-core  tlc-check  tlc-cli (→ target/release/tlc-rs.exe)
loop/
  PROMPT.md                   procedure for one Haiku iteration (do not edit)
  TASKS.md                    milestone task list M1~M9 (ticked off by Haiku)
  PROGRESS.md / NOTES.md      iteration log / knowledge base (memory across sessions)
  run-loop.ps1                loop driver
CLAUDE.md                     rules every session reads automatically
docs/JAVA_MAP.md              Java file ↔ Rust module map
```

## Score levels (check.py)
| Level | Corpus | Criterion |
|---|---|---|
| syntax | modules | `SANY -s` (parse only): exit code, error kind and the files parsed (discovery order) equal Java's |
| parse | modules | SANY exit code, error kind and the order of "Semantic processing of module X" equal Java's |
| parse_msg | modules | + the SANY error text is identical (whitespace-normalized) |
| front | models | same outcome up to "Computing initial states" (parse, .cfg, constants, ASSUME) |
| init | models | same number of distinct initial states |
| verdict | models | same exit code, first error code, violated property; same states generated / distinct / depth on success; same counterexample length for BFS violations |
| trace | models | identical counterexample states and action labels, error texts, Print output, warnings, statistics |
| perf | models | verdict matches **and** `rust_ms ≤ 1.1 × java_ms + 50ms` (process wall time; not gated) |

Java runs: `tlc2.TLC -tool -workers 1 -fp 0 -seed 1 -lncheck final -noGenerateSpecTE` (deterministic BFS),
TLC test models also get their JUnit flags (`-deadlock`, `-continue`, `-view`, ...). Models that finished in
< 60 s were run twice; fields that differed are not compared. Java timeouts (600 s) are unscored; models with
Java > 60 s are "heavy" and only run with `--heavy`.

## Current status
M0 only (2026-11-22): the environment is built; tlc-rs reports "not ported" everywhere.

| Corpus | Java golden outcome |
|---|---|
| SANY modules (1140) | 1107 ok, 16 semantic error (exit 4), 17 other error (exit -1: parse errors, missing modules); `-s`: 1123 ok, 17 error |
| TLC models, scored (364: 150 Examples + 214 test models) | 217 success, 47 liveness violation, 38 safety violation, 25 eval failure, 15 assumption failure, 10 config error, 7 other error (exit 255), 1 each deadlock / assert / safety-eval / liveness-eval / spec parse |
| TLC models, not in the default run | 13 heavy (Java 79–495 s, run with `--heavy`), 7 Java timeouts (> 600 s, unscored) |

Java total over the 364 scored models: 758 s (single worker, wall time incl. JVM start).
Full gate with a fast Rust: a few minutes (`-j8`).

## Running the Haiku loop

### Option A — headless driver (recommended)
Every iteration starts a Haiku session with a **fresh context** and performs one task.
```powershell
cd D:\sw\tlc_rs
pwsh -File loop/run-loop.ps1                          # defaults: --model haiku, up to 100 iterations, 45 min each
pwsh -File loop/run-loop.ps1 -MaxIterations 10 -IterationTimeoutMin 30 -MaxBudgetUsdPerIter 2
New-Item loop/STOP                                    # stop after the current iteration
```
After every iteration the driver:
1. reverts any change to protected files (harness/, PROMPT.md, CLAUDE.md, the driver, settings) and resets
   `harness/results/best.json` to its pre-iteration state (the baseline only grows through the driver's gate)
2. commits leftover uncommitted changes
3. **re-runs the full gate** (`check.py --gate --update-best`)
   - pass → updates and commits the baseline (best.json)
   - build failure / regression → keeps that iteration's work on a `rejected/iter-NNN` branch, resets HEAD to the
     state before the iteration and records the reason in `loop/LAST_REJECTED.md`, which the next iteration reads
4. stops after 4 consecutive iterations without changes under `crates/` (stuck detection)

Logs: `loop/logs/driver.log` (summary), `loop/logs/iter-NNN-*.jsonl` (full stream-json of each session).
To test the driver itself without calling Claude, substitute a fake agent with `-Agent <fake-agent.ps1>`.

### Option B — interactive Haiku session
```powershell
cd D:\sw\tlc_rs
claude --model haiku --settings loop/haiku-settings.json
> /loop read loop/PROMPT.md and perform one iteration following that procedure
```
Context keeps accumulating in one session (with automatic summarization), so Option A is better for long runs.
In Option B nothing reverts regressions for you, so run `python harness/check.py --gate` yourself now and then.

## Watching progress
```powershell
python harness/check.py --no-build          # current scoreboard (skip the build)
Get-Content harness/results/history.csv     # score history per run
Get-Content loop/PROGRESS.md -Tail 30       # Haiku work log
git log --oneline | Select-Object -First 20
```

## Rebuilding / checks
```powershell
python harness/setup.py                              # fetch/verify reference (pinned), jars, tla-library, cargo
python harness/corpus.py                             # rebuild corpus.json (only if the corpus definition changes)
python harness/gen_golden.py --kind parse -j 8 --force   # SANY goldens (~2 min)
python harness/gen_golden.py --kind check -j 3 --force   # TLC goldens (long: single worker, up to 600 s per model)
```

## Design notes
- **Oracle = TLC's own `-tool` output.** It is the machine interface the Toolbox and the VS Code extension parse,
  so the Rust CLI reproduces it (making tlc-rs a drop-in replacement) and one parser (`tlcout.py`) normalizes both
  sides. Fields that depend on timing, fingerprints or the machine (timestamps, progress, collision estimates) are
  never compared.
- **Determinism.** One worker, fixed `-fp`/`-seed`, BFS: state counts and shortest-counterexample lengths are
  deterministic. Exact counterexample contents additionally need Java's enumeration order — that is the `trace` level.
- **Telemetry.** Java runs with an isolated `user.home` whose `.tlaplus/esc.txt` is `NO_STATISTICS`
  (TLC's documented opt-out), so generating goldens sends nothing.
- **Anti-cheating.** Rust code must not read goldens/manifests or special-case names (CLAUDE.md). The parse level
  also compares the order in which SANY analysed modules, so a stub cannot pass it. Protected files are guarded
  twice: the deny rules in `loop/haiku-settings.json` (the driver passes them to Haiku via `--settings`) and the
  driver's automatic revert.
- **Pure Rust.** The toolchain is `x86_64-pc-windows-gnu` without a C compiler; no external crates yet.
