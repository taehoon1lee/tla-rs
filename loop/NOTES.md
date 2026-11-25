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

## Action labels are recomputed for traces
- The main search runs with `ev.splitting = false` (no per-disjunct label bookkeeping, ~8% of the time on LamportMutex). When a
  trace is printed, `Checker::transition_label` re-splits the actions for that one predecessor (`step()`, Java:
  `Tool.getState(fp, predecessor)`) and takes the label of the first successor with the child's fingerprint.
- `tools/cpu.py exe1,exe2 -n 3 <ids>`: best-of-N wall and CPU time (GetProcessTimes); far less noisy than wall time.

## Memoized constant-level operator calls (`memo.rs`)
- A call of a constant-level, parameterized, non-native operator is remembered by the values of its arguments when the operator
  is pure (everything it reaches is a pure standard-module operator or a user definition; no TLC Print/TLCGet/RandomElement,
  no IOUtils/Json/SVG, no operator-valued parameters) and builds sets/functions (SUBSET, {x \in S : P}, {e : x \in S}, [S -> T]).
  Skipped inside INSTANCE substitutions. 20000 entries per operator, the table is cleared when full.
- MCQuicksort: 5.9 s -> 0.5 s (`PermsOf(seq0)` was recomputed for every state).

## \A chain must restore the whole frame (PaxosCommit generated-count bug)
- `forall_chain` runs the same `body` node once per instance of an action-level `\A`; the instances share the body's frame slots
  (operator parameters, `\E` witnesses). The frame `[base, end)` is saved when `body` yields and restored after the next instance
  returns, so the remaining alternatives of the earlier instance see their own values (Java: immutable `Context`s).
- Reproduction: `\A rm \in RM : Decided(rm)` with `Decided(rm) == \E MS \in Majority : ...` (more than one witness per rm).

## Dependency-based cache of state-level nullary definitions (`deps.rs`) — 2026-11-23
- Java's `LazyValue` keeps (value, copy of s0/s1) and reuses it while every variable assigned *when it was computed* still has the same
  value (`TLCState.isSubset`). `CompiledDef::dep_cache` does it with the variables the definition really reads (`deps::state_reads`:
  walks the compiled body and everything it calls; `None` for primes, UNCHANGED, ENABLED, temporal ops, operator parameters,
  INSTANCE substitutions, impure natives). Checked after the (state ptr, epoch) cache misses. InnerSerial: `totalOpOrder` reads only `opQ`
  and was recomputed for each of 2^16 candidate `opOrder'` values: MCInnerSerial 523 s -> 2 s (Java 495 s), same counts.
- Constant-level operator memo (`memo.rs`) is now also used under INSTANCE substitutions when the operator contains no `SubstIn` and
  reaches none of the substituted constants (`CompiledDef::memo_decls`): MisraReachability RandomGraphs 1.5 s -> 0.2 s.
- Quantifier bounds: `SUBSET S` is generated lazily (`Value::try_each`, Java `SubsetValue.elements(NORMALIZED)` is lazy, so
  `\E s \in SUBSET S : Q` stops at the first witness) but `{x \in S : P}` is NOT: `EnumerableValue.elements(NORMALIZED)` converts every other
  set with `toSetEnum()`, i.e. P is evaluated for ALL elements before the first one is visited (an error behind the witness is raised).
  A lazy SetPred walk looked like a win and is WRONG (verified with tmp/dep1 against Java). Do not "optimize" it.
- Java's `ContextEnumerator` also prefetches one element ahead; this only matters for side effects/errors of the enumerator itself.
- Known gap (unchanged): an evaluation error in an invariant of an INITIAL state is reported by Java as 1000+2103 / exit 75 (or 255 with
  2121+2103 for Next), by us as 2111 / exit 76; the 2103 position chain is not produced (TODO 2 in TASKS.md).
- Measurement: sequential `tools/perf.py --heavy-ex` (TLCRS_EXE=<exe> to time a copy of the binary) gave x0.13 .. x1.10 for the 13 heavy ex/
  models; MCReachable's golden (78 s) is a measurement artefact (Java 0.4 s when rerun). `tools/profnode_t.py <id> [secs]` = node-kind
  profile of a time-limited run (needs `--features "tlc-cli/sprof tlc-check/prof"` in target-prof).
- Frame growth uses `eval::grow_unset` (a tag-store loop) instead of `Vec::resize` (~1-2 %). A hand-written `Clone for Value` with an
  inline scalar fast path was SLOWER (code bloat): keep the derive.
- Run the gate with `-j 4`: `-j8` plus a background build/test made the machine run out of memory once.

## Perf pass 5 (2026-11-23): what helped and what did not
- Helped: `Len/Head/Tail/Append/Cardinality` without copying the sequence (`as_seq_rc`) + value-level `natives::Fast` entry points called
  from `call_def` (no `Slot`s / pool); `x = Const`, `x \in Var/Const` compared in place; `enum_def_call` decides a body `/\ test /\ rest`
  whose first conjunct is a plain state-level `=,#,\in,\notin` test right after the frame is set up (`actions::first_test`; only Mode::Next,
  not while splitting labels, not with by-name arguments): DijkstraMutex 3-proc benchmark -16 %, MCLamportMutex -11 %;
  record constructors share one sorted domain `Rc` per field set (`Node::RcdCons(fields, dom, pos)`: no sort/alloc, `ptr_eq` fast paths hit);
  `run_frame_in` (no `Captured` with two `Rc::new(vec![])` per forced by-name argument); `\oplus`/`\ominus` merge the sorted domains
  (`merge_bags/subtract_bags`, fall back to the general code when elements are incomparable);
  small function constructors whose body is pure (`deps::is_pure_state_expr`) are computed right away instead of capturing the frame and
  both states for a lazy `FcnLambdaValue` (EWD998PCal -12 %): if any element fails the lazy function is built as before.
- Did NOT help (reverted): hand-written `Clone for Value` with inline scalar fast path (everywhere or only at the 3 leaf reads in `Ev::eval`).
- Java forces a function value more eagerly than we do in some places (`DOMAIN f = 0..2` with `f == [i \in 0..2 |-> 10 \div i]` raises
  the division error in Java, we stay lazy). Pre-existing difference, not changed.
- Tools: `tools/cpu_dir.py exe1,exe2 -n N <dir> Spec.tla Spec.cfg` (best-of-N CPU time on a scratch model), `tools/run_id.py <exe> <id> <secs>`
  (corpus model, stderr passed through), `tools/profnode_t.py`. Python on Windows reads files as cp949: pass `encoding='utf-8'` (and keep CRLF).

## Java timeout 1200 s: the five ex/ models without a golden (2026-11-23)
- `tools/long_compare.py java|rust|compare <id>...` runs Java (harness command line, -Xmx6g) / tlc-rs with a long timeout into tmp/long/ and scores
  with the harness' own `check.score_check` (read-only import; nothing under harness/ is written). The 600 s goldens of bosco, EWD998Chan,
  ElevatorSafetyMedium, MCKVSSafetyMedium, CoffeeCan3000Beans were timeouts only because 3-4 JVMs ran in parallel: alone Java needs 530 / 708 /
  589 / 874 / 741 s and all five succeed (exit 0): bosco 29223200 gen / 1072452 distinct, EWD998Chan 12882257 / 1524022, Elevator 120792180 /
  17997111, KVS Medium 365609473 / 17220672, CoffeeCan 18000002 / 4504500 (all 4.5M states are initial states).
- tlc-rs: EWD998Chan 270 s (x0.38), CoffeeCan 119 s (x0.16, peak 7.4 GB!), bosco 856 -> 324 s (x0.61) after `Node::Memo`.
  KVS Medium and Elevator Medium were killed at a 5 GB cap (490 s / 410 s): tlc-rs keeps every state (`Rec.vals`) in memory, Java keeps
  fingerprints + the queue on disk. TODO: store only fp/parent/level per state and re-derive trace states by replay (Java `getState(fp, pred)`).
- `Node::Memo` (deps::memo_spec): a pure set-building expression (`\cup \cap \ SUBSET UNION \X`, `{..: x \in S}`, `{x \in S : P}`, set of functions /
  records) is remembered by the VALUES of the state variables (s0 and s1), the free frame slots and the substitution list it reads (<= 4 entries,
  switched off when the hit rate is < 25 % after 64 calls). bosco: `\E r \in SUBSET (P \X M) : r \subseteq (sent \cup {..} \cup {..})` rebuilt the
  invariant right-hand side for each of the 256 `r` (60 % of the run). Keys are values, not (pointer, epoch): no staleness question.
- Symmetry cost (KVS-like, Key 3/Val 2/TxId 2: 96 s -> 77 s CPU, Java 61 s): `SymGroup.canonical_state` uses the exhaustive canonical form (try every perm,
  keep the smallest image) ONLY when the group has exactly 1 non-identity perm; with 2..5 perms the signature-based `canonical_fast` is faster
  (CheckpointCoordinationFailure, MultiPaxos_small got slower with the exhaustive form). Top-level function images are cached per perm
  (`ImgCache`, cap 512); a function over a closed domain permuted onto itself keeps the `dom` Rc and only reorders values (binary search);
  `Fcn.has_model` memoizes `contains_model`. Remaining profile is flat (eval_inner, permute_opt ~10 %, hash_into, cmp_val_slow, clone/alloc).
- tt/ pass (verdict 304 -> 364/364): `_POSSIBLE` + POSTCONDITION(S) are real now. `spec::process_config_possible` generates the module text of
  `SpecProcessor.processConfigPossible` and analyses it with `tla_sany::analyze_generated_module` (loads `_Possible` + its LOCAL INSTANCEs);
  state-level predicates become model constraints, action-level ones action constraints (the generated defs get the level of the tracked predicate,
  otherwise the compiler folds them: SANY gives `_Track(P, n)` constant level). `bfs::check_postconditions` runs after the BFS (2404/2405/2780, exit 10).
  Named registers `TLCSet("s:..", v)` / `TLCGet("all:named")` / `TLCExt!TLCGetOrDefault`; native `_Possible!_Counts` (Java override).
- Init-state errors: an exception while an initial state is checked (constraints, fingerprint, invariants) prints 2102 ("While working on the initial
  state") + 2103 and exits 75 (`report_init_state_error`); the call-stack positions of 2103 are NOT reproduced ("The error call stack is empty").
  `-continue` reports every violated invariant of every initial state (DoInitFunctor). No next-state action with states in the queue -> 2115.
  Incomplete successor (2109): single action -> text without the action name; the failing successor is printed as the last state (`y = null`).
- Safety-like temporal properties (`oos.has_empty_pem()`): Java finds the counterexample while building the behavior graph (`LiveCheck`, recursive
  `addNextState` when a node of a done state is created and a tableau successor is accepting) => exit 12 + finite trace + stats at that moment.
  `live::safety_shortcut` replays that incremental construction over the finished state graph (processing order = BFS order; `proc_log` keeps the
  generated/distinct/depth numbers after each state).  Successor order inside a state is still Java's hash-set order (not reproducible).
- Typed model values (`A_x`: second char `_`, name > 2 chars): comparing/equating two different types or a typed one with a non-model value raises
  Java's error (`value::model_type`); `TLCExt!TLCModelValue` is a native.  `[f EXCEPT ![x] = v]` only swallows a domain miss, not other errors.
- Config: constant operators given as tables (`CONSTANT F(0) = 1 ...` -> `Ev.const_tables`, Java OpRcdValue); unterminated cfg string = lexical error 5007;
  SPECIFICATION naming a state variable = 2236; `[]S` with state-level S in a SPEC = 2213; unnamed next-state actions are called `Action`.
- Fingerprints of strings only see the low byte of each UTF-16 char (`FP64.Extend(fp, String)`): "é" and "ǩ" are one state (`str_fp_class`).
- ENABLED / primed INSTANCE access: `actions::target_var` and `var_of` follow SubstIn and nullary definitions (Java `getPrimedVar` / `getVar`).
- Still open in tt/ (0 at verdict level): lazy normalization of set enumerations / SUBSET / kSubset ("*AssumeTest", RandomSubset*, ModuleSemanticsAssume),
  Java classes (UserModuleOverride), `Randomization` natives, TLCGet("spec") coverage + level (TLCGetLevel), parameterized INSTANCE in
  SPECIFICATION (Github687specA/D), 2102/2103 call stacks and the
  exit-255 variants (Github696b, CyclicRedefine*, FingerprintException*), config constant `A <- diameter` evaluated at startup (TLCGetNamedUndefined).
- Tooling quirk: doubled backslashes in my tool input arrive halved - patch Rust text with raw strings / chr(92) (see memory note).
- Also: a constant substituted by a definition that reads variables/TLCGet is evaluated at startup (`Ev.setup_phase`: TLCGet("distinct") etc. are undefined
  then) -> 2281; a constant-Boolean conjunct of a SPECIFICATION that is FALSE -> 2237; arguments of operators met while the SPECIFICATION / a temporal
  property is analysed are inlined by name (`spec::INLINE_PARAMS/INLINE_OPS`, used by the compiler for otherwise unbound parameters).
- Init errors by Java exception class: `Assert.fail` (TLCRuntimeException) -> 2102 with the state; `new EvalException` (TLC modules: TLC_MODULE_* codes) -> plain 1000 (`bfs::is_eval_exception`); StackOverflowError at init -> 1000 + 2103 + exit 75, in the
  subscript collector (cycle through `<-` overrides) -> 1005 + exit 255 before init.  TLCGet("level"): 0 in Init, 1 for initial states, `TLCGet("level")'` = successor level (`Ev.prime_depth`).
- Not worth porting: *AssumeTest (hundreds of ASSUMEs that pin exact Java error texts incl. reflection signatures), UserModuleOverride (loads a Java class).
- A `SUBSET` with more than 2^24 elements stays lazy when it is bound to a variable (`Value::is_huge_subset`); the failure happens when the state is fingerprinted, reported like Java (2102 + 2147 at init;
  1000 + trace + 1000 + 2147 for a successor).
- Randomization!RandomSubset is a native (natives::random_subset): k distinct indices (any RNG: Java seeds per state fingerprint, so the values cannot be reproduced) decoded as mixed-radix
  elements of products / function sets / record sets, a big interval is not enumerated; `Value::is_empty_set` / `size` / `is_finite` follow Java's order of asking the constituents.
- Value semantics (ValueSemanticsAssume / ModuleSemanticsAssume): `TLCExt!AssertError` is a native (the TLA+ definition is always TRUE): TRUE iff the 2nd argument fails with exactly the text of the 1st;
  `TLCExt!TLCFP`; `Nat \cap {1,2}` enumerates the finite side; Java's equality of Nat/Int/Seq(S) and of product-like sets (`value::set_eq_special`), `Seq({})` is finite, `Nat \cup {}` reduces,
  EXCEPT on a function with an infinite domain stays lazy, lazy-function application errors use `In applying the function ...`, IsFiniteSet({x \in Nat : p}) fails like Java (override text with markers).
- EmptySetEqAssume: Java prints a product-like set by its elements only when it has < 2000 (`Value::expands`), otherwise structurally (`[n1: S, n2: T]`, `[D -> R]`, `(S \X T)`); ToString does not
  normalize; `Value::is_empty_set` follows `Value.isEmpty` (UNION decided by its first element); scalar compare/equality errors use Java's text (`... with non-integer:` + value).
- KSubsetAssume: `FiniteSetsExt!kSubset` is a native returning `Value::KSubset(k, S)` (Java `KSubsetValue`): no elements iff k<0 or k>|S| (finite S); k=0 is {{}} for any S; size/enumeration/equality/compareTo/member as in Java, never
  enumerating `SUBSET S`; `size()` > 2^31-1 is an `IllegalArgumentException` (`JAVA_RUNTIME_EXCEPTION` code) that the Cardinality/ToString overrides wrap (`k=32 and n=64`). `AssertError` compares the text with tool-mode
  markers for errors that carry an EC code (Java builds those with `MP.getMessage`), plain text only for `Assert.fail(String)`.
  `tmp/assume_diff.py <Module>` (scratch) runs each ASSUME of a *Assume test model alone in Java and Rust and prints the differences.
- InitialLivenessEvaluationError: a liveness property with a tableau evaluates its state predicates for the initial states during `doInit` (Java `TableauLiveChecker.addInitState` -> `TBGraphNode.isConsistent`), so an error there is an init-state
  error (2102, no replay: the state is in the fingerprint set already; exit status of the original error code, 2280 -> 151). `ENABLED` reading an unassigned `x'` is Java's 2280 `In evaluation, the identifier x is either undefined...` with the
  position of `x` (`Node::PrimedVar` carries it).
- NormalizationAssume / Github696b: `Value::SetU` is Java's unnormalized `SetEnumValue`: `Value::set_lit` (set enumerations) keeps the written elements when they cannot be compared (`{1, "a"}`), `member` is a linear `equals`
  search (`linear_member`; a normalized `Value::Set` falls back to it when the binary search fails), `\cup`/`\cap`/`\`/`UNION` with a SetU follow `Reducible.cup/cap/diff` and `UnionValue.union` (`reduce_unnormalized`, `union_unnormalized`),
  `{x \in S : P}` over it is computed at once, enumerate/size/compare/fingerprint normalize it (error from the sort). An error report that prints such a set fails again (`check_printable`, `state_not_printable`: generic 1000 + exit 255).
- UserModuleOverride: `classfile.rs` reads `<Module>.class` next to the spec (Java: `SpecProcessor.processModuleOverrides`), reports `2400` (no operator of that name/arity) and `2168` (loaded) like Java and replaces the operator by the
  value of a method it can interpret (constants only: `BoolValue.ValTrue/ValFalse`, `IntValue.gen(c)`). A method with another body keeps the TLA+ definition of the operator (the examples that ship such a class, `Bits.class`, compute the same);
  there is no JVM, so a user override that computes anything else would silently differ.
- FingerprintExceptionHang: `TlcErr.fp_exc` marks failures inside `Value::member` (Java rethrows them as `FingerprintException` because the set has a source). An invariant failing that way at a successor prints 2111 with the cause, the
  trace, then the replay (`replay_failed_invariant`): the successors the first pass did not store are stored and evaluated, the first failure is the 2147; the stack positions of 2147 are not reproduced (no source positions on values).
  Trace-level text (290/364) still differs for: 2147 positions, 2111 layout of the other evaluation failures (Java embeds the cause), the stats after such errors, JVM method order of override messages.

- Trace-level pass 2 (342/364): state variables / constants are listed in Java's `Hashtable` order (`spec::java_decl_order`: bucket = `String.hashCode() % capacity`, capacity from the symbol count + 72 built-ins).
  Counterexample machinery (`bfs.rs`: `post_after_trace`, `post_after_lasso`, `counter_example_value`, `action_record`) builds `[state, action]` like `CounterExample.java` and runs the POSTCONDITION after the trace (safety:
  `Worker.doPostCondition` incl. ALIAS records; liveness: raw states + the closing action); `Ev.counter_example` / `Ev.alias_trace` back `TLCExt!CounterExample` / `Trace` (TLCExt definitions are not constant-folded).
  `step(pred, level, fp)` sets `TLCGet("level")`. `Subst.module` / `NodeInfo.module`: frames of instance copies are located in the module holding the `INSTANCE` statement. After a failed invariant/action-property evaluation the
  summary prints the outdegree (Java's replay is silent -> `printSummary(true)`).
- Java-compatible randomness / liveness order (pass 3): `jfp.rs` = FP64 + `Value.fingerPrint` (ints, strings, booleans, tuples, functions/records, sets; model values are not portable: `UniqueString.tok` depends on the JVM run);
  `RandomSubset` = `SubsetEnumerator` (`computeOptimalMandA`, `nextInt`, `nextPrime`) / `BigIntegerSubsetEnumerator`, the generator is re-seeded with `fingerprint(predecessor) ^ seed` once per expanded state (`Ev.pred_state`);
  liveness successors are put in `SetOfStates` slot order (`java_set_order`, the worker's `multiplier` capacity) and the tableau graph is built like `TableauLiveChecker` (`live::build_graph_incr`: states in BFS order, nodes created for
  already-processed states are expanded at once: self-loops first, then successors in generation order). Not available with SYMMETRY / VIEW / model values in the state (old reverse order is kept there).
- SYMMETRY + liveness (pass 6): Java files each successor of a state in a `SetOfStates` under `state.fingerPrint()` = the FP64 of the lexicographically smallest image (`minVals`); model values hash `UniqueString.tok` and compare by `ModelValue.index`.
  The tokens of the config's values are 1, 2, ... in the order the parser meets them (verified with a Java probe that dumps `UniqueString.uidToUniqueString`); strings of the config count too. Model values created later (TLCModelValue) have no
  known token: `jfp` returns None and the old reverse order is used. Probe recipe: a `main` that calls `new TLC().handleParameters(args); process()` and then walks `TLCGlobals.mainChecker` / `UniqueString` (see tmp/probe in the session, not committed).
- Call stacks are replayed, not recorded (2026-11-24): `TlcErr.frames` is only filled while `Ev.tracking` is set (`Ev::with_tracking`/`tracked_quiet`/`replay`); a check of the result after every `eval` costs 6-14 % even when `#[cold]`.
  New code that needs the nodes of a failure must re-run the failing evaluation inside `ev.replay(e, || ...)` (see `replay_next`, init enumeration in `bfs.rs`). Do not add `thread_local!` (or any per-eval result check) to value comparison / eval paths:
  per-id tables are statics (`value.rs`: `MODEL_IDX`, `TYPES`, `CLASSES`, `SRC_RING`). Compare binaries with `tmp/timeit.py`-style interleaved min-of-N runs: single runs differ by 5-10 % from noise alone.

## Perf review of the 5 highest-ratio models (2026-11-25): Java ALONE is faster than its golden
- The goldens' Java wall times come from 3-4 JVMs running in parallel. Java alone (`tmp/javatime.py`: harness command line, min of 2) vs Rust
  (min of 3, sequential): MCLamportMutex 11.1 / 12.1 s (Rust x1.09 SLOWER), EWD998PCal 29.7 / 31.6 (x1.07), EWD998Small 24.2 / 25.2 (x1.04),
  SlidingPuzzles 1.46 / 1.36 (x0.93), MCBakery 7.56 / 7.14 (x0.94). The harness perf level (golden times) is optimistic by 7-19 % on these.
- Phase split MCLamportMutex (node-profile build, +20 % overhead): successor generation 68 %, invariants 16 % (TypeOK 1.3 s + BoundedNetwork/Mutex 1.1 s
  of 12 s), constraint 8 %, fingerprint 6 %, FpSet 1 %. A failing action guard costs ~118 ns: ~34 test expr + ~33 call + ~51 disjunction/quantifier.
  A trivial transition (`c' = c+1`, UNCHANGED net) costs ~600 ns/state of BFS overhead.
- Tried and NOT helpful (all measured interleaved, min of 3-6, sequential): `lto="fat"` + `codegen-units=1` (LamportMutex 12.12 -> 12.42 s);
  `-C target-cpu=native` (12.08 -> 12.10); `enum_def_call` without `self.empty()` per argument / `first_test` by reference / by-name flag in the argument
  loop (microbench 839 -> 847 ms, LamportMutex 12.15 -> 12.29); a 8-entry `dep_cache` per state-level definition (EWD998PCal 32.6 -> 34.1 s: the refinement
  mapping `token`/`pending` rarely repeats a network value, a miss now scans 8 entries).
- Applied: `normalize()` returns early for `Fcn.norm_ok` and `TLCGet("duration")` is computed on read (`Ev::start_time`) instead of `Instant::now()` per state
  in `set_counters` (trivial-transition BFS -9 %).
- Applied (structural): borrowed read paths. `Value::apply_ref` (tuple / normal-form function element by reference) + `Ev::place` follow `x`, `x[a]`, `x[a][b]`
  (arguments: constant, frame slot, state variable, nested path) as references into the state; used by `=`/`#`/`\in`/`\notin` (left operand), `r.field`, the
  chain `x[a][b]` and the `natives::Fast` arguments (`Len/Head/Tail/Append/Cardinality`). A path that does not apply returns `None` and the normal code runs
  (so error texts / order are unchanged). LamportMutex -9 %, MCBakery -11 %, MCbtree -16 %, EWD998Small -3 %.
- Pitfall: the first version (place probes inline in `eval_inner`, then in helpers that always probed) made EWD998PCal 4 % SLOWER although the probe hit
  rate there is ~1 % (99 % of the operands are not `Var`/`FcnApply`). Fix: check the operand kind first; only a `Var`/`FcnApply` operand goes to the
  separate `#[inline(never)]` `*_placed` function, every other operand runs the code that existed before. Keep `eval_inner` free of new locals.
- `Fcn.fp` already caches the hash of every function value (hierarchical fingerprint); do not add another hash cache for functions.
- `profnode.py` is distorted by its own `PROF_CUR.swap` (an `xchg` per `eval`): leaf nodes (`Local`, `Var`, `Const`) look 2-3x too expensive; use the
  sampling profile (`tools/prof.py`) for proportions. Under Git Bash, an id filter like `/MCBakery` is rewritten to a Windows path: pass it without `/`.
- Still open: EWD998PCal is ~10 % slower than Java alone (32.5 vs 29.7 s): the refinement mapping (`token` = CHOOSE over the network, `pending`) is re-evaluated
  per transition; closures capture the whole frame (free-variable analysis, see "Remaining perf ideas"); `enum_action_inner` disjunction path.
