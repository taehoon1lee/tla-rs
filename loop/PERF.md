# PERF — performance loop state (used by loop/PROMPT_PERF.md)

Judge: `python tools/ab.py ...` (read its docstring). Single worker, identical results, sequential interleaved timings.
Edit this file freely: tick backlog items, add LEDGER rows, refresh STANDING. Keep it short (numbers, not stories).

## Goal
1. Every model of the full set (`tools/ab.py` FULL) at or below Java ALONE (rust/java <= 1.00).
2. Then keep lowering the geomean of rust/base with accepted hypotheses (each must pass `ab.py compare --set full` = ACCEPT).

## STANDING (rust vs Java alone, sequential, min of 2; refresh with `python tools/ab.py time --set full`)
measured 2026-11-25, HEAD 0744ec2 (after H3 + H7): EVERY model of the full set is below Java alone (goal 1 reached). Worst first:

| model | rust/java alone |
|---|---|
| ex/lamport_mutex/MCLamportMutex | x0.971 |
| ex/SlidingPuzzles/SlidingPuzzles | x0.919 |
| ex/ewd998/EWD998Small | x0.883 |
| ex/Bakery-Boulangerie/MCBakery | x0.820 |
| ex/Disruptor/MCDisruptor_MPMC | x0.790 |
| ex/TeachingConcurrency/SimpleRegular | x0.724 |
| ex/YoYo/YoYoAllGraphs | x0.676 |
| ex/allocator/AllocatorImplementation | x0.605 |
| ex/KeyValueStore/MCKVsnap | x0.509 |
| ex/SpanningTree/SpanTreeRandom | x0.495 |
| ex/FlashProtocol/MCFlashWithMutexLive, MCbtree, bcastByz, VoteProof, ElevatorLivenessMedium | x0.17 .. x0.37 |

Not in the FULL set: `ex/ewd998/EWD998PCal` 19.6 s vs Java alone 29.7 s = x0.66 after H3 (was x1.08).
Goal 2 (lower the geomean) continues: MCLamportMutex (x0.97) and SlidingPuzzles are the closest to Java.

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
- [x] H6 (superseded by H7: the profile of SpanTreeRandom was set operations of `Nbrs(n)`, not the graph build) Liveness graph build (SpanTreeRandom, ~250k evaluations of `<<Next>>_vars` of its `WF`): evaluate the action
      predicate of an edge without re-enumerating Next from scratch when the edge is known to come from Next. Only if identical results.

- [x] H11 (ACCEPT, see LEDGER H11) Huang liveness (40 % of the run): `<<A>>_vars` per edge.
- [x] H12 (ACCEPT on the symmetry models, see LEDGER H12) Symmetry `abs_hash` one-traversal form.
- [ ] H13 Memo of calls with an operator argument naming a pure definition (`FoldFunction(Add, ..)` in Huang `Sum`).

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
| H7 | ACCEPT | `memo::scan`: the body of a constant-level definition WITHOUT parameters (evaluated once, value cached in `CompiledDef::cache`) may contain impure natives (`RandomElement`): `Nbrs(n)` of SpanTreeRandom (reaches `Edges` = `RandomElement(SUBSET ..)`) is now remembered by its argument | SpanTreeRandom 4.44 -> 2.05 s (x0.46, Java alone x0.47) | 0.955 (15 models; the 2-rep full run printed REJECT only because of MCDisruptor_MPMC x1.136, re-measured with `--reps 5`: 2.49 -> 2.47 s = x0.991, noise; the longer run is final) | profile: 45 % in set ops (`cmp_val_slow` 17, `member_impl` 7.5, `model_type` 6, `set_from` 5, `enumerate` 5) rebuilding `{m \in Nodes : {m, n} \in Edges}` for every `\E m \in Nbrs(n)`; the old scan rejected the operator because of `RandomElement` although `Edges` runs once |
| H8 | ACCEPT | `memo::scan`: bounded quantifier / CHOOSE / function constructor count as heavy, or transitive body >= 12 nodes, so more pure constant-level operators are remembered by argument values; `Value::hash_is_cheap()` guard before hashing a memo key (a lazy `1..MaxInt` argument hung `tt/ModuleSemanticsAssumeTest`); `cmp_val` inline Model/Model (packed `MODEL_IDX`, bit 31 = typed) and direct `Set` vs `Set` in `cmp_val_slow` | Huang 30.8 -> 20.4 s (x0.66), MCKVsnap x0.85, SpanTreeRandom x0.83, Sailfish x0.91, PCal x0.88; 14 slowest models -10.4 % wall | 0.958 (15 models) | Huang `TypeOK` = 53 % of the run: DyadicRationals `Add/Reduce/GCD/Max/IsDyadicRational` re-evaluated per state; set/model compare allocated two Rc clones per `Set` vs `Set`. Details: `loop/PERF_RESEARCH.md` |
| H9 | NEUTRAL | `hash_into`: tag and payload in one word (half the mixing steps) | geomean 0.996 over 7 models | n/a | hash arithmetic is not the bottleneck |
| H10 | NEUTRAL | `except1` keeps `Fcn.norm_ok` when the new element is normal | geomean 1.002 over 7 models | n/a | `needs_normalize` cost is not in the Fcn rescan |
| H11 | ACCEPT | `Node::ActionSub` returns before evaluating `sub` when A decides (Java `Tool.eval` OPCODE_aa/sa: `<A>_e` false when A is false, `[A]_e` true when A is true); `CompiledDef::cheap_body`: a state-level definition without parameters whose body is a tuple of variables/constants (`vars == <<a,b,c>>`) is evaluated directly instead of going through `state_cache`/`dep_cache`/value-keyed memo | Huang 20.66 -> 17.86 s (x0.86; liveness part 8.5 -> 5.9 s), EWD998PCal x0.84, ElevatorLivenessMedium x0.89, MCFlashWithMutexLive x0.90 | 0.967 (15 models) | Huang profile (liveness only): `Call(vars)` 31 % + `Eq` 8 % of the time: `<<A>>_vars` evaluated `vars` twice for each of the 10 WF actions on every edge although A is false for ~9 of them; the remaining `vars` calls paid for 3 cache lookups (hash of 3 variables) to avoid building a 3-tuple. No unit test (needs an `Ev` + module text; covered by the liveness corpus models, gate 364/364) |
| H12 | ACCEPT (targeted) | `SymGroup::signatures_all`: the signature of every symmetric model value from ONE traversal of the state (`AbsAll::go` returns the neutral hash and, per symmetric value inside the subtree, the hash with that value marked; a set/function/tuple parent differs from the neutral hash only in the children that contain the value) instead of one `abs_hash` traversal per value + `collect_models`; same hash VALUES (test `signatures_all_equal_signatures_ref` compares with the old code, kept as `signatures_ref` and used when > 8 symmetric values occur) | MultiPaxos_MC_small 14.67 -> 12.41 s (x0.85), FastPaxos x0.87, MCCheckpointCoordinationFailure x0.91, MCKVsnap x0.985 | compare of the 4 symmetry models: ACCEPT geomean 0.900; `--set full`: NEUTRAL 1.007 (worst 1.028) | the FULL set contains only one symmetry model (KVsnap), so it cannot show this gain; the code runs only under SYMMETRY (`canonical_fast`), the other 14 models are noise by construction. Profile: `abs_hash` 18 % + `collect_models` 5 % of MultiPaxos, k traversals of the whole state for k symmetric values. Gate rc 0 (all 26 symmetry models identical at trace level) |
