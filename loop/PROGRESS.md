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
