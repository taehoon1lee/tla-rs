# PERF — performance loop state (used by loop/PROMPT_PERF.md)

Judge: `python tools/ab.py ...` (read its docstring). Single worker, identical results, sequential interleaved timings.
Edit this file freely: tick backlog items, add LEDGER rows, refresh STANDING. Keep it short (numbers, not stories).

## Goal
1. Every model of the full set (`tools/ab.py` FULL) at or below Java ALONE (rust/java <= 1.00).
2. Then keep lowering the geomean of rust/base with accepted hypotheses (each must pass `ab.py compare --set full` = ACCEPT).

## STANDING (rust vs Java alone, sequential, min of 2; refresh with `python tools/ab.py time --set full`)
measured 2026-11-25 on the dev box, HEAD 3e5661b (tools/ab.py time --set full --reps 2); worst first:

| model | rust/java alone | java alone s | rust s |
|---|---|---|---|
| ex/SpanningTree/SpanTreeRandom | x1.057 | 4.36 | 4.61 |
| ex/ewd998/EWD998Small | x1.002 | 25.36 | 25.41 |
| ex/lamport_mutex/MCLamportMutex | x0.999 | 11.39 | 11.38 |
| ex/SlidingPuzzles/SlidingPuzzles | x0.935 | 1.53 | 1.43 |
| ex/Disruptor/MCDisruptor_MPMC | x0.841 | 3.08 | 2.59 |
| ex/Bakery-Boulangerie/MCBakery | x0.838 | 7.79 | 6.53 |
| ex/TeachingConcurrency/SimpleRegular | x0.738 | 3.75 | 2.77 |
| ex/byzpaxos/VoteProof | x0.684 | 9.90 | 6.77 |
| ex/YoYo/YoYoAllGraphs | x0.658 | 5.29 | 3.48 |
| ex/allocator/AllocatorImplementation | x0.615 | 6.88 | 4.23 |
| ex/KeyValueStore/MCKVsnap | x0.502 | 8.96 | 4.50 |
| ex/btree/MCbtree | x0.391 | 26.24 | 10.26 |
| ex/FlashProtocol/MCFlashWithMutexLive | x0.388 | 11.02 | 4.28 |
| ex/bcastByz/bcastByz | x0.360 | 11.67 | 4.20 |
| ex/MultiCarElevator/ElevatorLivenessMedium | x0.165 | 18.16 | 3.00 |

Not in the FULL set (too long for one A/B run; add it to `ab.py compare <id> --reps 3` when your hypothesis targets it):
`ex/ewd998/EWD998PCal` x1.08 (Rust 32.0 s vs Java alone 29.7 s, from NOTES.md) = the slowest model relative to Java.
Over Java alone: SpanTreeRandom (x1.057, liveness graph build), EWD998Small (x1.002), EWD998PCal (x1.08).

## Do NOT retry (measured and rejected; details in NOTES.md "Perf ...")
- `lto = "fat"` + `codegen-units = 1`; `-C target-cpu=native` (no gain on this box).
- Hand-written `Clone for Value` with an inline scalar fast path (code bloat, slower). Keep the derive.
- Per-state `thread_local!`, `Instant::now()` per state, per-eval call-stack recording (use `Ev::replay`).
- An 8-entry `dep_cache` per state-level definition (EWD998PCal +5 %: the refinement mapping rarely repeats a network value).
- Inline "place" probes in `eval_inner` (probe operand kind first; helpers are `#[inline(never)]`).
- Lazy `SetPred` walk (WRONG: Java evaluates P for all elements first; error order differs). Not a performance option.
- Anything that changes enumeration order, set normalization order, CHOOSE, fingerprints, or messages.

## BACKLOG (top = next; expected gain is a guess to be checked with the profile)
- [x] H1 (REJECT, premise false: 0 frame copies measured) Free-variable analysis for closures / by-name arguments: `capture`, `eval_arg`, `run_captured_in` copy the WHOLE frame;
      capture only the slots the code reads (compile time analysis, `FrameCtx`). Target EWD998PCal, EWD998Small, MCLamportMutex. ~3-8 %.
- [ ] H2 `enum_action_inner` disjunction path and failing guards (a failing guard costs ~118 ns: ~34 test, ~33 call, ~51
      disjunction/quantifier): avoid per-branch frame/state setup when the first conjunct already fails. Target MCLamportMutex, MCBakery.
- [x] H3 (ACCEPT, see LEDGER H3) EWD998PCal: profile first (`tools/prof.py ex/ewd998/EWD998PCal --top 25 --lines ...`), the refinement mapping
      (`token` = CHOOSE over the network, `pending`) is re-evaluated per transition (~10 % slower than Java alone). Find the dominant
      node, remove one copy/allocation/re-evaluation there. Do not use a bigger dep_cache (see above).
- [ ] H4 Invariant `TypeOK` on MCLamportMutex costs ~1.3 s of 12 s: membership in function/record/sequence sets
      (`f \in [S -> T]`, `\in Seq(..)`) must not build the set or copy `f`; keep error behaviour identical.
- [ ] H5 Per-state BFS overhead of a trivial transition (~600 ns/state): profile a `c' = c + 1` spec under `tools/prof.py`
      (state allocation, fingerprint, queue push, counters); fewer allocations per successor.
- [ ] H6 Liveness graph build (SpanTreeRandom, ~250k evaluations of `<<Next>>_vars` of its `WF`): evaluate the action
      predicate of an edge without re-enumerating Next from scratch when the edge is known to come from Next. Only if identical results.

## LEDGER (append one row per experiment; newest at the bottom; seeded from NOTES.md)
| id | outcome | change | before -> after | full geomean | why |
|---|---|---|---|---|---|
| s1 | ACCEPT | `thread_local!` -> static atomics/ring in value compare + `note_source`; error call stack only on replay (`Ev::replay`) | 6-14 % per model | n/a | windows-gnu TLS guard ~10 ns/access |
| s2 | ACCEPT | `Len/Head/Tail/Append/Cardinality` without copying (`natives::Fast`), `first_test` in `enum_def_call` | MCLamportMutex -11 %, DijkstraMutex -16 % | n/a | removed copies |
| s3 | ACCEPT | pure small function constructors computed eagerly (`deps::is_pure_state_expr`) | EWD998PCal -12 % | n/a | no frame/state capture for a lazy FcnLambda |
| s4 | ACCEPT | borrowed read paths (`Value::apply_ref`, `Ev::place`) for `x[a][b]` | LamportMutex -9, MCBakery -11, MCbtree -16, EWD998Small -3 % | x0.98 (26 models) | no clone/drop per step |
| s5 | REJECT | `lto="fat"` + `codegen-units=1` | LamportMutex 12.12 -> 12.42 s | n/a | no gain |
| s6 | NEUTRAL | `-C target-cpu=native` | LamportMutex 12.08 -> 12.10 s | n/a | no gain |
| s7 | REJECT | `enum_def_call` without `self.empty()` per arg, `first_test` by reference, by-name flag in arg loop | LamportMutex 12.15 -> 12.29 s | n/a | microbench 839 -> 847 ms |
| s8 | REJECT | 8-entry `dep_cache` per state-level definition | EWD998PCal 32.6 -> 34.1 s | n/a | refinement mapping rarely repeats a network value; a miss scans 8 |
| s9 | REJECT | hand-written `Clone for Value` with inline scalar fast path | slower | n/a | code bloat |
| s10 | REJECT | place probes inline in `eval_inner` | EWD998PCal +4 % | n/a | probe hit rate ~1 %; fixed by checking operand kind first |
| H1 | REJECT (no code) | free-variable analysis for closures / by-name args | 0 frame copies (`eval_arg` x2, `capture`, Lambda closure) counted on PCal, EWD998Small, MCLamportMutex | n/a | premise false: every by-name arg is `closed` (no frame copy) or strict; nothing to save. Counter patch idea: static AtomicU64 per site, dump before `process::exit` in tlc-cli |
| H3 | ACCEPT | value-keyed multi-entry memo (`CompiledDef.memo`, hash of the variables in `deps` + `eq_val`, <= 65536 entries, switched off below 25 % hits after 256 lookups) for state-level nullary defs (`dep_memo_get/put` in `eval.rs`), allowed while no INSTANCE substitution in scope substitutes a constant the def reaches (`deps::state_reads_decls`, `dep_decls`) | EWD998PCal 32.05 -> 19.62 s (x0.61), VoteProof x0.52, EWD998Small x0.91 | 0.950 (15 models) | PCal profile: `pending` 24 % + `token` 22 % + `EWD998!vars` 12 % of the time; `token'`/`pending'` ran for every successor (2.8M) although only 321k distinct network values exist. The old 1-entry `dep_cache` missed, and the substitution-list check (`substs.same`) blocked reuse (args of a SubstIn see the earlier substitutions) |
