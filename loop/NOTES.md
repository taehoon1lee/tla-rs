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

## SANY port notes (2026-11-22)
- Parser = hand-written recursive descent mirroring tla+.jj; DEFBREAK tokens are inserted by `belch_def` exactly like Java (definition boundaries).
- Module discovery order = `SpecObj.loadSpec` (all unresolved EXTENDS first, then INSTANCE; monolith modules are read from the root file).
- Instance copies (`I!Op`) are new OpDefs (params = instance params ++ original params, body wrapped in `SubstIn`), like Generator.processModuleDefinition.
- Selectors `Def!label`, `Def!2`, `Thm!:` handled via synthetic defs (`gen_selector`); exotic ones become `EKind::Unsupported` (TLC must report 9999 if evaluated).
- Levels are computed on the fly (`Expr.level`, `OpDef.level/weights`), simplified w.r.t. SANY's level-parameter machinery.
- Tooling gotcha: the Bash tool mangles backslashes inside `python - <<EOF` heredocs. Write patch scripts with the Write tool (scratchpad) and run them.

## Evaluator / enumeration facts learned (TLC semantics that bite)
- Java enumerates `\E x \in S, y \in T` with the FIRST variable varying fastest (ContextEnumerator). `for_each_binding_cb` mirrors it.
- `getNextStates` expands `\/`, `\E`, `=>` (consequent), bounded `\A` (one continuation per context), applications of user ops and
  function constructors (`f[x]` of an unevaluated FcnLambda) in ANY conjunct position => duplicate successors are counted in
  "states generated". Once every variable is assigned (`allAssigned`) the remaining conjuncts are only evaluated (no expansion).
  Our `eval_only` flag in `actions.rs` does this (Init too; Next only when `warn`).
- Action labels: `<Name(arg,..) line L, col C to line L2, col C2 of module M>`: Name/params from the operator the splitting went
  through (constant args only), location of the first non-splittable node (`Ev::node_info` side table filled by the compiler).
- `left on queue` at an invariant violation excludes the violating state (Java enqueues after the checks).
- Config overrides (`Op <- Op2`, `[Mod]Op = v`) name the ORIGINAL def; INSTANCE copies must follow (`d.original().id`).
- Profiling: `cargo build --release --features tlc-check/prof` then `TLCRS_PROF=1 [TLCRS_PROF_PHASE=enum|inv|constraint] tlc-rs ...`
  prints a sampling profile of the current node kind to stderr (no external profiler on this box). Remove nothing: off by default.
- The windows heap is slow: `crates/tlc-cli/src/alloc.rs` is a per-thread size-class allocator (measured 10-15%).
- POSTCONDITION(S) is parsed but NOT evaluated: the corpus tests that use it also use `_POSSIBLE` / `TLCGet("all:named")`
  (new in this TLC build; SpecProcessor.processConfigPossible synthesizes a TLA+ module). Evaluating postconditions without
  that would regress ~6 tt/ tests that currently pass because nothing is evaluated. TODO: port `_Possible` + postconditions together.
- Successors outside the model (CONSTRAINT false) are NOT stored, but TLC still checks their invariants (`unseen` stays true).
- State-level nullary definitions are cached per (state pointer, `Ev::epoch`); the epoch must be bumped whenever a state buffer
  is mutated or a new evaluation starts (`run_top`, `assign_and_continue`, BFS expansion).

## Performance tooling / findings (2026-11-22, /goal session 2)
- Profiler: `tools/README.md` (sampling profiler `sprof` feature + COFF/DWARF symbolizer; no nm/addr2line/gdb on this box).
  Build into `target-prof` so the normal `target/` build (used by the gate) is never replaced during a gate run.
- `std::thread_local!` on windows-gnu costs ~10 ns per access (lock-prefixed guard `enable()` on every access): the global
  allocator reads its per-thread state straight from the TEB TLS slot (`gs:[0x1480+8*idx]`) -> alloc+free 16 ns -> 3.6 ns.
  Do not put `thread_local!` on hot paths.
- `eval_inner` has a ~1 KB stack frame and an 8-register prologue: `Ev::eval` handles `Const`/`Var`/`Local(V)` inline.
- Assumption error locations (2104/2105) are the location of the assumption EXPRESSION, not of `ASSUME Name ==`.
- Remaining perf ideas: frames are copied for every closure/by-name argument/function constructor capture (`capture`,
  `eval_arg`, `run_captured_in`); capture only the slots the code reads (free-variable analysis at compile time).
- INSTANCE substitutions are a persistent list (`ir::Substs`, newest first): capture/restore is O(1); a state-level nullary
  definition is cached per (state ptr, epoch, substitution-list identity). Call-by-name arguments that read no frame slot
  (`Arg::ValClosed`, `Arg::State(_, true)`) need no frame copy (compiler counts slot events: `FrameCtx::events`).
- `eval_inner` keeps only hot arms (frame 984 -> 408 bytes); big arms live in `eval_heavy` (#[inline(never)]).
- Look for whole-vector copies in value ops (`fcn_parts`, `fcn_values`, `.to_vec()`): `member` on record/function sets copied
  both vectors on every call (MultiPaxos invariant: 10%).  `abs_hash`/symmetry used SipHash maps per model value.

## Liveness (M6) — ported 2026-11-22
- `tlc-core/src/liveness/{ln,tableau,translate,oos}.rs` = `LiveExprNode`+`LN*`, `TBPar/TBGraph`, `Liveness.astToLive`, `processLiveness`;
  `tlc-check/src/live.rs` = behavior graph (state graph x tableau, built after the BFS) + `LiveWorker` (Tarjan SCC, `checkComponent`,
  lasso construction); `bfs.rs::final_liveness_check/print_lasso` print the counterexample like `LiveWorker.printTrace`.
- Verdict level needs only exit code + first error (13, 2116): `BFS_TRACE_EXITS` does not include 13. Exact lassos need Java's `SetOfStates`
  hash order (FP64 fingerprints; our `tok`/intern ids differ from Java's) -> not reproduced yet; successors are in generation order, self loop last.
- `Setup.live` (oss + positive property formulas) is filled in `tlc-check/src/lib.rs` before the BFS; 2212 is printed there, 2253 (tautology) when
  there is no order of solution.  `TrErr::Unsupported` = formula shape this port cannot translate (operator arguments that are not constants,
  incomparable set elements): liveness is skipped (as before this port) instead of failing.
- `classify_property` unrolls calls with constant arguments and constant `\A` like `SpecProcessor.processConfigProps`; the bound values travel in
  `Top.bound` / `Setup.properties_bound` (first slots of the frame).
- ENABLED: a substituted declaration `v <- expr` met as `v' = e` or `UNCHANGED v` is bound by name (`Ev::virt`), as Java binds it in the TLCStateFun.
- With a VIEW a graph node stands for several states: action/consistency checks use the successor actually produced by the edge (`live_edge`),
  the printed trace is rebuilt state by state with `Checker::step` (Java: `Tool.getState(fp, predecessor)`).
- Nullary LET definitions (state level, no primes) are memoized per LET scope: `Node::LetScope(slots, body)` clears the memo slots on
  entry, `Node::LetUse(slot, def)` evaluates the definition once per (state pointer, evaluation epoch) like Java's `LazyValue`. Before, every
  use re-evaluated the body: nested LETs multiplied the cost (TLCSailfish1: > 7x slower than Java, timeout) — now 0.7x of Java.
  `LetScope` is transparent to action splitting (labels point into the LET body).
- `SUBSET S` is enumerated directly in normalized order (size, then lexicographic): no sorting of 2^n sets.

## RandomElement (java.util.Random)
- `TLC.RandomElement` is native (`natives::random_element`): SetOfFcns/SetOfRcds/SetOfTuples recurse per component, Interval and
  every other finite set pick `floor(nextDouble() * size)` of the normalized elements. The generator is `jrandom::JRandom` (port
  of `java.util.Random`), seeded with `-seed` and shared by the whole run (`Ev.rng`).
- Java reseeds it with `state.fingerPrint() ^ seed` while the successors of a state are generated (BFS only); that needs Java's
  FP64 state fingerprint, which we do not reproduce. Constant-level uses (SpanTreeRandom's `Edges`, evaluated once at startup)
  and initial-state generation use the plain sequence and match Java exactly.

## ALIAS / IOUtils.Serialize / SVG / Json
- `ALIAS` (Setup.alias, `bfs::state_text_at`): every state of an error trace is printed as the fields of the alias record,
  evaluated with s0 = the state, s1 = the next trace state (itself for the last one) and `TLCGet("level")` = trace position.
  An evaluation error prints the state variables plus `_ALIASEvalError` (all lines with `/\`); `_format` is honoured.
- Natives: `IOUtils.Serialize` (TXT, writes the file, returns the exit record), `SVG.SVGElemToString`, `SequencesExt.SetToSeq`,
  `Json.ndJsonDeserialize/JsonDeserialize` (override errors carry the framed 2154 text; the FileNotFoundException text is
  `<path with \ on Windows> (<OS message minus the final period>)`), `\o` and `Len` accept strings like Sequences.java.
- A LET-local `INSTANCE M` of an operator with a native implementation is called, not inlined (`is_native_copy`).
