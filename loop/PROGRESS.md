# PROGRESS — append-only iteration log (max 6 lines per entry)

## 2026-11-22 M0 — environment built (Opus)
parse 0/1140, front 0, init 0, verdict 0, trace 0, perf 0 (Rust reports "not ported" everywhere)
next: M1.1 lexer

## 2026-11-22 M1+M2 — SANY lexer/parser/module loader/semantic analyzer (Opus-level session, Sonnet 5.5)
syntax 1140/1140, parse 1132/1140, parse_msg 1126/1140 (all 436 ex/ modules pass; remaining = tt/ error-message cases), front 1, init 1, verdict 1
code: crates/tla-sany/src/{lexer,parser,ast,ops,modules,sem,analyze,analyze_expr,driver}.rs (see docs/JAVA_MAP.md)
next: TLC side — values (M3), config + spec processing (M4), evaluator, BFS (M5)

## 2026-11-22 M3-M5, M7 partial (Sonnet 5.5, /goal session)
full corpus: front 341/364, init 315, verdict 245, trace 199, perf 227; ex/ only: verdict ~144/150, trace ~140/150.
done: Java-faithful action enumeration (`getNextStates`: =>, \A chain, FcnApply/LAMBDA expansion, all-assigned fast path,
ContextEnumerator order = first var fastest), action splitting + labels (`Action.getLocation`), SYMMETRY, PROPERTY
classification (`[]P` invariants, implied init/action), TLC pretty printer (`pprint.rs` = tlc2.pprint), outdegree stats,
community natives (Functions, FiniteSetsExt fold/quantify, IOUtils env, Graphs/UndirectedGraphs), recursive LET ops,
INSTANCE substitution fixes, perf (Arith nodes, fast allocator in tlc-cli, Fcn dom sharing, no per-call allocs).
open: liveness (43 tt/ models + 3 ex/), CCT/ALIAS/POSTCONDITION, perf of heavy models (Sailfish1, MultiPaxos, FastPaxos).

## 2026-11-22 M9 perf pass 2 (Sonnet 5.5, /goal session 2)
allocator TLS via TEB (alloc 16->3.6 ns), eval inline leaf fast path, ASSUME location = expression loc, tools/ profiler.
ex/ slow models now 0.95-1.3x of Java (SlidingPuzzles 1.69->1.29, MCBakery 1.38->1.04). Corpus unchanged otherwise: verdict 258, trace 214.
next: more perf (sparse frame capture), liveness port (M6), SpanTreeRandom RNG, ALIAS/IOExec.

## 2026-11-22 M9 perf pass 3 (Sonnet 5.5)
Substs persistent list, closed by-name args, eval_heavy split, borrowed membership, dense symmetry tables.
ex/: perf 133/150 at -j8 (sequential: MultiPaxos 1.14, PCal 1.33, LamportMutex 1.24, SlidingPuzzles 1.27, SimpleRegular 1.19). Corpus: verdict 258, trace 214 (unchanged).
next: remaining perf (PCal/LamportMutex/SimpleRegular), liveness port (M6), SpanTreeRandom.

## 2026-11-22 M6 liveness port (Sonnet 5.5)
LN formulas + tableau + processLiveness + behavior graph + SCC/lasso. Corpus: front 347, init 325, verdict 296 (was 258), trace 224, perf 283.
ex/: MCRealTimeHourClock, MCDistributedReplicatedLog now pass verdict. Not yet: operator-argument formulas (Github1161/817/LetDef*), exact lasso order (FP64).
next: remaining ex/ items (SpanTreeRandom RNG, ALIAS/IOExec, Json), perf (PCal 1.33, LamportMutex 1.24), TLCSailfish1 timeout.

## 2026-11-23 ex/ pass 4: liveness perf, RandomElement, ALIAS, natives, label deferral, call memo (Sonnet 5.5)
full corpus: verdict 304/364, trace 250, perf 298 (best), time x0.70 of Java over verdict-matching models. ex/ (non-heavy): verdict 150/150, trace 150/150.
done: `java.util.Random` + `TLC.RandomElement` (SpanTreeRandom), ALIAS in traces, IOUtils.Serialize/SVGElemToString/SetToSeq/Json deserialize,
string `\o`/`Len`, LET-local INSTANCE of native ops; perf: liveness behaviour-graph memo of state predicates, closed INSTANCE substs cache,
16-byte Slot, function fingerprint memo, 4 KB allocator classes, no label tracking in the search (labels recomputed for traces),
cached getenv, memoized pure constant-level set-building operator calls (MCQuicksort 5.9 s -> 0.5 s).
next: ex/ perf borderline (MCLamportMutex ~1.12x, RandomGraphs, PCal), heavy ex/ models (see tmp/heavy1.log), remaining tt/ failures.

## 2026-11-23 perf: dependency cache, lazy SUBSET, memo under INSTANCE (Sonnet 5.5)
sequential ex/: all 150 + 13 heavy within 1.1x of Java (heavy x0.13-1.10); MCInnerSerial 523 s -> 2 s (Java 495 s), MisraReachability RandomGraphs 1.5 -> 0.2 s, AllGraphs 5.2 -> 1.2 s.
full corpus: verdict 304/364 (unchanged), trace 250, perf 300-301, time x0.53 of Java (was x0.70). Gate: no regressions.
next: remaining ex/ >= 1.0x of Java: DijkstraMutex 1.10, MCLamportMutex 1.08, EWD998PCal 1.06, KVS Small 1.03 (flat interpreter profile: eval_inner, Value clone/drop, action enumeration); tt/ failures.

## 2026-11-23 perf pass 5: sequences w/o copies, first-test rejection, shared record domains, eager small function constructors (Sonnet 5.5)
CPU (sequential, vs previous commit): MCLamportMutex 14.2 -> 12.6 s (Java 13.3), EWD998PCal 36.2 -> 31.7 s (Java 34.8), DijkstraMutex 3-proc bench -16 %.
full corpus: verdict 304/364, trace 250, perf 301, gate: no regressions.
next: confirm DijkstraMutex (4 proc, Java 430 s) sequentially; remaining ex/ ratios.

## 2026-11-23 Java timeout 1200 s: the 5 golden-less ex/ models; Node::Memo (Sonnet 5.5)
Java alone: bosco 530 s, EWD998Chan 708 s, Elevator Medium 589 s, KVS Medium 874 s, CoffeeCan 3000 741 s (all exit 0). tlc-rs: EWD998Chan 270 s, CoffeeCan 119 s, bosco 324 s (was 856 s): all levels pass.
KVS Medium / Elevator Medium: tlc-rs exceeds memory (every state kept) -> state storage rework is next.
gate: no regressions (verdict 304/364, trace 250, perf 302).

## 2026-11-23 symmetry cost pass (Sonnet 5.5)
KVS-like model with SYMMETRY (TxId of size 2): 96.3 -> 77.0 s CPU (Java 61.3 s), same counts (25,867,108 / 1,700,595). exhaustive canonical form only for a group with 1 non-identity perm; per-perm image cache; closed-domain reorder; `Fcn.has_model` memo.
gate (-j 2): no regressions (verdict 304/364, trace 250, perf 302; the two perf misses SlidingPuzzles / BugzillaBug279Test pass when timed sequentially: x0.78 / x1.10).
next: KVS Medium (Java 874 s) and Elevator Medium (Java 589 s) with a 14 GB cap; lean state storage (fp/parent/level only).

## 2026-11-23 tt/ pass: 60 more models match Java (Sonnet 5.5)
gate (-j 2): verdict 304 -> 364/364, trace 250 -> 283 (all 150 + 13 heavy ex/ unchanged). Done: `_POSSIBLE`/POSTCONDITION, 2102/2103 init-state errors,
safety-like liveness shortcut (exit 12), typed model values, constant operator tables, config/spec validation (2236, 2213, 5007), `-continue` at init,
ENABLED over INSTANCE, unicode string fingerprints, `\cdot`, incomplete successor text, `_format` alias exception, TLCGet("spec") (no coverage).
open: 0 tt/ models at verdict level (see NOTES.md "Still open in tt/"); the two Java-timeout tt/ models are unscored.

## 2026-11-23 tt/ trace pass 2: 342/364 check models identical at trace level (Sonnet 5.5)
gate (-j 2): no regressions (verdict 364/364, trace 283 -> 342). Done: call-stack texts (2103/2147 frames: `TlcErr.frames`, module of instance copies and substitution values), `doNextFailed`/`doNextEvalFailed` shapes
(2111/2112 embed the cause, outdegree after a silent replay), POSTCONDITION after every counterexample with `TLCExt!CounterExample` / `Trace` / `ToTrace`, ALIAS levels, state variables and constants in Java's `Hashtable` order,
`impliedtemporals`, SUBSET overflow/printing, large SUBSET stays lazy in a state, 2215 text for constraints.
open: liveness lassos that depend on Java's FP64 / `SetOfStates` order (CodePlexBug08*, Symmetry/Tableau*, Github1389ViolatedC), FingerprintException 2147 stacks (no value sources), `\cdot` ENABLED trail, ValueSemanticsAssume warning order, Random* (needs Java FP64 seeding).

## 2026-11-23 tt/ trace pass 3: 351/364 check models identical at trace level (Sonnet 5.5)
gate: no regressions (verdict 364/364, trace 342 -> 351, perf 363). Java-compatible randomness and liveness order: `jfp.rs` (FP64 + value fingerprints), `jrandom.rs` (`nextInt`, `nextLong`, `RandomGenerator.nextPrime`),
`RandomSubset` as `SubsetEnumerator` / `BigIntegerSubsetEnumerator` seeded per predecessor state (`TLCStateRandom`), `SetOfStates` slot order of the liveness successors, and the incremental tableau graph of
`LiveCheck.TableauLiveChecker` (`live::build_graph_incr`: late nodes expand self-loops first, then successors in generation order). Also: Java's insertion-sort / `FcnRcdValue.sort` error order, `Arrays.binarySearch` midpoint.
open (13): symmetry + tableau liveness (3, model-value fingerprints use `UniqueString` tokens), FingerprintException 2147 stacks + EmptySubsetEq (5, no value sources), `\cdot` ENABLED trail (2), liveness Print count (1),
ValueSemanticsAssume warning order (1), StringDeserialize (localized OS message).

## 2026-11-23 tt/ trace pass 4: 353/364 check models identical at trace level (tt/ 203/214) (Sonnet 5.5)
gate: no regressions (verdict 364/364, trace 351 -> 353, perf 363). `ENABLED` resets `eval_only` (an enclosing assignment of all variables no longer leaks into it); the `UNCHANGED` operand is a frame (`\cdot` stacks of CdotWithContextB/D);
2147 prints the call stack of a `FingerprintException` (FingerprintExceptionHang / EmptySubsetEq: Java also appends the sources of the lazily built sets on the failing path, which values do not carry here).
Still different (11, all tt/): symmetry + tableau liveness (3: model-value fingerprints use `UniqueString` tokens of the JVM run), 2147 value-source chains (Init/Next/NextCallstack/Hang/EmptySubsetEq: need `Value.source`),
liveness `Print` evaluation count (UserModuleOverrideAnnotation: Java evaluates tableau consistency per successor, un-memoized), ValueSemanticsAssume (order of three 2144 warnings), StringDeserialize (localized OS error text).

## 2026-11-23 tt/ trace pass 5: 361/364 check models identical at trace level (tt/ 211/214) (Sonnet 5.5)
gate (-j 2, --update-best): no regressions (verdict 364/364, trace 353 -> 361, perf 363). Done: value sources (`TlcErr.vsrc`, ring buffer of the nodes that built the lazy sets, `Value::tag_err` on enumerate/size/member/subseteq) for the
2147 `Fingerprint Stack Trace` (FingerprintExceptionInit/Next/Hang, EmptySubsetEq); `SUBSET x` of a non-set is lazy like `SubsetValue`; `IODeserialize` (file-not-found message) and `TLCGet("-D...")`; INSTANCE copies are made in the order of
the instancee's `Hashtable` (`sem::java_hashtable_order`) and every constant-level definition is evaluated once at startup in the order of the root context (`SpecProcessor.processConstantDefns`: ValueSemanticsAssume's warning order);
the liveness state predicates are evaluated when a state is expanded and the `Print` output of the violated-property attribution is flushed (UserModuleOverrideAnnotation).
Still different (3, all tt/): ChooseTableauSymmetry, TableauSymmetry, SymmetryTableauModelChecker: with SYMMETRY the successors of a state reach liveness in `SetOfStates` slot order, which needs the fingerprint of model values;
Java hashes a model value by the `UniqueString` token, i.e. by how many strings the JVM interned (SANY identifiers, built-ins, config) before it: not derivable without replaying the JVM's interning.

## 2026-11-23 tt/ trace pass 6: 364/364 check models identical at trace level (tt/ 214/214) (Sonnet 5.5)
gate (-j 2, --update-best): no regressions, verdict 364/364, trace 364/364. Symmetry + tableau liveness now matches Java:
the model values of the configuration file get Java's `UniqueString.tok` (the first strings the JVM interns, in the order `ModelConfig` mentions them: `ModelConfig.value_order`, `jfp::set_model_toks`) and Java's
`ModelValue.index` order (`value::register_model`, creation order) for comparisons; `java_set_order` files each successor under the fingerprint of the exact smallest image of the actual successor state;
`live::build_graph_incr` evaluates the predicates on the actual successor of each edge and expands a late node from the actual state it was reached with (`gen_successors` regenerates its successors in generation order).
perf: SpanTreeRandom is borderline (the 250k evaluations of `<<Next>>_vars` of its `WF` dominate the graph build, 6 s vs Java 5.8 s): it passes or misses by noise, as before this pass.

## 2026-11-24 perf: the 11 models slower than Java (Sonnet 5.5)
Sequential Rust/Java after this pass (min of 2): SpanTreeRandom 4.99/5.8, EWD998PCal 32.1/34.8, EWD998Small 25.5/28.3, MCLamportMutex 12.3/13.3, SlidingPuzzles 1.38/1.6, MCBakery 7.2/8.9, MCCheckpointCoordinationFailure 12.2/18.2.
Two regressions of the parity passes were found by timing old binaries (`git worktree` of 2888227 vs 10f7fe9, `tmp/timeit.py` = min of N interleaved runs):
(1) `thread_local!` in value comparison (`model_cmp`, `model_type`, `str_fp_class`) and in `note_source` (a Vec::remove(0) per lazy set): on windows-gnu each access runs a destructor guard (~10 ns); now static atomic tables / a static ring;
(2) the per-eval error check that records the call stack (`TlcErr.frames`) cost 6-14 %: now `Ev.tracking` (off) is read once at the entry of `eval_inner`, and a failure that needs its call stack is REPLAYED with tracking on
(`Ev::replay`, `Checker::replay_next`, init enumeration, `fp_stack_of_fp`; Java does the same with `CallStackTool`). The replay's output is dropped.

## 2026-11-25 perf: borrowed read paths (Sonnet 5.5)
Java alone (sequential) is faster than its goldens (those were timed with 3-4 JVMs in parallel): before this pass Rust was x1.09 / x1.07 / x1.04 SLOWER than Java alone on MCLamportMutex / EWD998PCal / EWD998Small (see NOTES.md "Perf review").
`Value::apply_ref` + `Ev::place`: `x[a][b]` chains over state variables are followed by reference (no clone/drop per step) in the left operand of `=`, `#`, `\in`, `\notin`, in `r.field`, in the chain itself and in the `natives::Fast` arguments (`Len/Head/Tail/Append/Cardinality`); a path that does not apply returns `None` and the old code runs (same errors).
Also `normalize()` returns early for `Fcn.norm_ok` and `TLCGet("duration")` is computed on read.
Sequential, interleaved, min of 2 (26 of the longest models): total x0.98; MCbtree -16 %, MCBakery -11 %, MCLamportMutex -9 % (11.1 s = Java alone), SimpleRegular -7 %, EWD998Small -3 %; no model > 3 % slower. EWD998PCal unchanged (32.0 s vs Java alone 29.7 s: the refinement mapping `token`/`pending` dominates).
Rejected (NOTES.md): fat LTO, target-cpu=native, call-path tweaks, 8-entry dep_cache (PCal +5 %).
gate (-j 2): no regressions (verdict 364/364, trace 364/364, perf 364/364).

## 2026-11-25 perf H3 -- ACCEPT: value-keyed memo of state-level nullary definitions (Sonnet 5.5)
EWD998PCal 32.05 -> 19.62 s (x0.61, Java alone 29.7 s), VoteProof x0.52, EWD998Small x0.91; `AB RESULT: ACCEPT (geomean new/base 0.950, best 0.516, worst 1.036, models 15)`. H1 rejected without code (0 frame copies measured).
Next: re-run `ab.py time --set full` to refresh STANDING; remaining over Java alone: SpanTreeRandom (x1.02, liveness graph build, H6); then `EWD998!vars` (12 % of PCal) and H2.
