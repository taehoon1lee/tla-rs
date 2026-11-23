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

## 2026-11-23 tt/ pass: 53 more models match Java (Sonnet 5.5)
gate (-j 2): verdict 304 -> 357/364, trace 250 -> 283 (all 150 + 13 heavy ex/ unchanged). Done: `_POSSIBLE`/POSTCONDITION, 2102/2103 init-state errors,
safety-like liveness shortcut (exit 12), typed model values, constant operator tables, config/spec validation (2236, 2213, 5007), `-continue` at init,
ENABLED over INSTANCE, unicode string fingerprints, `\cdot`, incomplete successor text, `_format` alias exception, TLCGet("spec") (no coverage).
open: 7 tt/ models (see NOTES.md "Still open in tt/"); the two Java-timeout tt/ models are unscored.
