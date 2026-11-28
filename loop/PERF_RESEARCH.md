# PERF research 2026-11-26 — how to get >= 10 % over the current build

Scope: research + prototypes, NOT merged. Prototype = `tmp/perf_research/e1b_e2_guard.patch` (3 files, ~60 lines; also an
uncommitted diff in the worktree `D:\sw\tlc_rs_exp`, detached at 126c59b). Judge pieces of `tools/ab.py` were reused through a wrapper
(`signature` equality + min-of-N interleaved) on two arbitrary exes, because the other session owns `target/release` + `tmp/ab/base.exe`.

## Result (candidate E1b+E2+guard vs. unchanged build of the same worktree)
| set | geomean new/base | note |
|---|---|---|
| the 14 slowest corpus models (= 75 % of all Rust time), 1 rep | 0.913; sum 196.8 s -> 176.3 s (**-10.4 %**) | Huang x0.66, KVsnap x0.84, PCal x0.88, Nano x0.87, Checkpoint x0.87, Sailfish x0.91, FastPaxos x0.92, Dijkstra x0.93, btree x0.95 |
| `ab.py` FULL set (15 models), 2 reps | 0.950 (best SpanTreeRandom x0.84, worst MCBakery x1.011) | AB-style ACCEPT (geomean <= 0.98) |
| all signatures (states, depth, trace, errors, output) | identical | |
| `check.py --gate` (main tree, patch applied) | rc 0; check levels 364/364 | see "Gate" |

So: >= 10 % is reached on wall time of the heavy models (what a user waits for); the unweighted geomean over the 15 AB models is -5 %.

## What the patch does
- **E1b `memo.rs`**: calls of constant-level parameterized operators are remembered by argument values also when the body is not a set builder:
  bounded quantifier / CHOOSE / function constructor count as "heavy", or the transitive body has >= 12 nodes. The existing hit-rate switch-off
  (128 calls, < 50 % hits) is unchanged. Huang's `TypeOK` (53 % of the run: DyadicRationals `Add/Reduce/GCD/Max/IsDyadicRational`) 16.7 s -> ~8 s.
- **Guard (needed by E1b)**: `Value::hash_is_cheap()` before hashing memo keys. Without it `tt/ModuleSemanticsAssumeTest` hangs / dies with 0xC0000409:
  `SingletonOf(T, S) == .. \A x,y \in T ..` is now memoizable and its argument `1..(MaxInt-1)` is a lazy 2^31-element interval that `hash_into` enumerates.
  (The same hazard existed for the old "heavy" memo; nothing triggered it.)
- **E2 `value.rs`**: `cmp_val` inlines Model/Model order (one packed table `MODEL_IDX`, bit 31 = typed -> general path), and `cmp_val_slow` compares
  `Set` vs `Set` directly instead of `enumerate()`-ing both (two Rc clones + a chain of arms). Sailfish -7 %, KVsnap -7 %, SlidingPuzzles -4 %.

## Measured and REJECTED / NEUTRAL (do not repeat)
| id | change | result |
|---|---|---|
| PGO | `-C profile-generate` | impossible: this rust-std (rustc 1.100, windows-gnu) has no `profiler_builtins`, no `llvm-profdata` |
| E4 | `hash_into`: tag+payload in ONE word (halves the mixing steps) | geomean 0.996 over 7 models: noise. Hash arithmetic is not the bottleneck |
| E5 | `except1` keeps `Fcn.norm_ok` when the new element is normal (skips the rescan in `needs_normalize`) | geomean 1.002: noise |
| E1 (steps >= 12 only, no quantifier rule) | | Huang -14 % only; `IsDyadicRational` (`\E i \in 0..r.den`) is < 12 nodes but loops |
| JCC-erratum flag | | n/a: CPU is AMD Zen3 (5800X3D) |

## Where the remaining time is (sampling profile, 14 slowest models weighted by time; `tmp`-script `aggprof.py`)
eval_inner 10.8 %, cmp_val_slow 6.8, call_def 4.9, hash_into 4.0, symmetry (permute_opt_raw 3.5 + abs_hash 2.5 + collect_models 0.6) 6.6, eval_arg 2.9,
eval_heavy 2.6, enum_action_inner 2.5, Value::clone 3.4, member_impl 2.4, eq_val 1.9, model_type 1.6. Flat: no single function is worth > 5 %.
Share of corpus time: SYMMETRY models 15 %, models with PROPERTY 46 %.

## Next candidates (not implemented; expected gain = guess from the profile)
1. **Huang liveness** (after E1b: ~60 % of what is left). `-lncheck final` with 10 WF actions evaluates `<<A>>_vars` for every edge: 1.17M edges x 10 predicates
   (12.7 s of 31.7 s before E1b; BFS itself is 2.3 s). Pre-filter an action by the variables it can change (primed variables it assigns / UNCHANGED) before
   evaluating it (`live.rs` `action_bits`/`eval_memo`). Expected Huang -15..20 %, other PROPERTY models (46 % of corpus time) a few %.
2. **Symmetry** (3 models = 13 % of corpus time, 30 % of their time in `canonical_fast`): `abs_hash` traverses the whole state once per present model
   value (k times). Compute the neutral hash once and re-hash only the subtrees that contain the marked value (delta form of the commutative sums);
   `collect_models` with a bitmask over `orbit_dense`. Hash VALUES must stay identical (they pick the canonical representative). Expected -10..15 % on MultiPaxos_small, Checkpoint, FastPaxos.
3. **Cache the hash of Tuple/Set values** (like `Fcn.fp`): MCLamportMutex / EWD998Small spend 7 % in `hash_into` (sequences and sets are rehashed every time
   for state fingerprints and the H3 value-keyed memo). Needs a wrapper around `Rc<Vec<Value>>` (large refactor). Expected -4..6 % on those.
4. **Memo with operator arguments** (`FoldFunction(Add, Zero, f)` in Huang's `Sum` = 37 % of what is left after E1b): allow `Arg::Op` naming a pure top-level definition,
   key = (def id, argument values).
5. Structural, large: closure/bytecode compilation of `eval_inner` + `call_def` + `eval_arg` + `eval_heavy` (~21 % of time + clone/drop/alloc ~8 %). Honest
   estimate -8..12 % overall for weeks of work; only if 1-4 are exhausted. Multi-worker BFS would be far larger but violates the loop's single-worker rule.

## Method warnings (these cost me an hour)
- **Build-layout lottery**: the same source built in two directories differs by up to +12 % (SimpleRegular 2.74 -> 3.06 s, SlidingPuzzles_anim +9 %) and a
  one-line change can move a model +-5 % without being a real effect. Compare ONLY binaries built from the same path, and re-measure any short model that
  disagrees across `--reps 3`. `ab.py snapshot` (same path) is fine; a BASE built elsewhere is not. fat-LTO / native were judged by single comparisons.
- A short model that regresses although its profile does not touch the changed code is layout, not code: check with an unchanged rebuild.
- Parallel work: another Claude session ran `tools/ab.py compare` and switched the branch of the main tree while I worked; I built in a separate worktree
  (`git worktree add --detach ../tlc_rs_exp HEAD`, `reference/` junction for the harness, removed afterwards) and never touched `target/release`.

## Gate (CORRECTION of an earlier claim)
I first wrote that `check.py --gate` already exits 1 at HEAD. That was a worktree artifact (the worktree has no `harness/results/best.json` baseline, so the
known SANY mismatches parse 1132/1140 and parse_msg 1126/1140 showed up as "regressions"). In the main tree, with the patch applied:
`python harness/check.py --gate -j 2` -> **rc 0** (syntax 1140/1140, parse 1132/1140, parse_msg 1126/1140 = baseline; front/init/verdict/trace/perf 364/364),
and `python tools/ab.py compare --set full` -> **AB RESULT: ACCEPT (geomean 0.958, best 0.829 SpanTreeRandom, worst 1.048 MCFlashWithMutexLive, 15 models, 2 reps)**.
Unit tests: `cargo test -q` ok (29 in tlc-core, 2 new: `hash_is_cheap_rejects_huge_lazy_sets`, `set_and_model_comparison_fast_paths`).

# Java vs Rust, module by module (2026-11-26, read-only review)

Evidence levels: **M** = measured here (timing / peak memory / sampling profile), **C** = read in the code only (no number).
Micro-benchmarks: one operation repeated in an `ASSUME` (`tmp`-script `micro.py`), Java warm-up ~0.46 s subtracted.

| module | Java | Rust | verdict |
|---|---|---|---|
| `tla-sany` (lexer, parser, modules, semantic) | SANY, JVM | hand-written recursive descent | OK. **M** 6-17x faster than Java incl. JVM start (2.9 MB `tt/Bug156/TE`: 302 ms vs 1818 ms; 68-258 KB modules 23-52 ms vs 340-740 ms) |
| `value.rs` representation | Value objects, `FcnRcdValue` with `intv` for `1..n` domains | `Value` 16 B, `Slot` 16 B, `Node` 72 B (**M** `size_of`), sorted `Rc<Vec>` sets, binary-search member | OK (as Java) |
| `value.rs` EXCEPT (`except1`) | `takeExcept`: reference-array copy | `f.vals.clone()` = per-element `Clone` dispatch + per-element `Drop` | **slower.** **M** `[F EXCEPT ![k] = i][1]` over 100 entries: 1.0 s vs Java 0.27 s net per 1M (x3.7); profile `except1` 56 % + `drop` 17 % + `clone` 6 % |
| `value.rs` `set_from` | insertion sort | sorts, but when an element is a model value or kinds differ it first `clone()`s the whole vector (only to reproduce Java's error order) | **C** extra O(n) allocation per set built from model values (symmetry specs); can be skipped when all elements are registered untyped model values (no error possible) |
| `eval.rs` function constructor | shares the domain | `[x \in S |-> e]` over <= 16 elements: `elems.to_vec()` copies the domain per function; larger domains: lazy `FcnLam` + `capture()` copies frame + both states | **C** domain `Rc` not shared (records do share); `capture` copies where Java keeps references (H1 counted 0 hits in 3 models, so only structural) |
| `eval.rs`/`compile.rs` arithmetic | `%`, `\div`, `^` are built-in operators | only `+ - * < > <= >= ..` are inline `Node::Arith`; `%`, `\div`, `^` go through the generic native call (arg slots, `call_def`, `int_arg`) | **slower.** **M** `\E j \in 1..50 : j = (i % 50) + 1`: 2.30 s vs Java 1.32 s net (x1.7); profile `eval_arg` 15 + `call_def` 13 + `int_arg` 11 + `modulo` 6 + `eval_eq` 12 %. Huang node profile: `Call(\div)` 4.8 %, `Call(^)` 3.2 %. The inline path already falls back to the native with the evaluated values, so errors stay identical |
| `eval.rs` operator arguments / LAMBDA | `Context` chain | each call: `Vec<Slot>` + `assigns: Vec<(u32,Slot)>` + `Captured` + `run_frame_in` clones the whole captured frame onto the stack | **slower.** **M** `SelectSeq(S, LAMBDA e: ..)` over 200 elements: x3.3 vs Java warm; profile `select_seq` + `eval_arg` + `Vec<Slot>::extend` + `run_frame_in`. SlidingPuzzles (`ChooseOne(board, LAMBDA ..)`): `run_frame_in`, `Slot` extend/drop/into_iter, `apply_closure`, alloc = ~12 % |
| `actions.rs` | `getNextStates` with `ActionItemList` | continuation-passing `enum_action_inner` | same shape. open: a failing guard costs ~118 ns (H2) |
| `symmetry.rs` | all permutations | signature canonical form | was k traversals of the state per symmetric value; fixed by H12 (one traversal). `permute_opt_raw` (13 % of MultiPaxos) remains |
| `natives.rs` | `tlc2.module.*` | Rust natives | OK. **M** micro: 13 of 16 cases 5-30x faster than Java (Java `UNION` of 150k sets took 31.8 s, quadratic) |
| `bfs.rs` memory | fingerprints in FPSet, queue and trace on disk | **every state** (`Rec.vals`) in memory | **M** peak 374 B/state (EWD998Small 1.5M states, 542 MB), 678 B (MCLamportMutex), 1558 B (Sailfish); Elevator/KVS Medium were killed at 5 GB; Java stays flat (disk) |
| `bfs.rs` parallelism | `-workers N` | parsed, ignored (`auto` = 1), evaluator is `Rc`/`RefCell` (not `Send`) | **largest gap.** **M** Java `-workers 8`: MCLamportMutex 11.5 -> 3.6 s (x3.2), EWD998Small 24.8 -> 5.3 s (x4.7); Rust 1 thread: 10.9 / 22.5 s |
| `bfs.rs` per state | `Worker` | `vals.clone()` of the new state only to call `check_invariants(&self, ..)` (a shared borrow is enough); `Rc<LabelBase>` + `Arc<str>` allocated per expanded state; `live_succ.contains` O(deg^2) | **C** ~100-200 ns per new state, 1-2 % |
| `live.rs` (liveness graph) | `LiveWorker`, `DiskGraph`, compact node tables | `std::HashMap` with SipHash for `(u32,u32)` / fingerprint keys (`bits`, `leaf`, `cons`, `index`, `texist`, `fp_index`); per graph node 3 `Vec`s; `bits.get(..)` clones a `Vec<bool>` | **M** Huang liveness profile: `sip::Hasher::write` 2.0 % + `RandomState::hash_one` 1.9 % + `eval_memo` 5.0 % (map probing). `eval.rs` already has a cheap `PtrHasher`, these maps do not use one |
| `alloc.rs` | JVM heap | per-thread size-class free lists via the TEB (<= 4 KB, 16-byte classes), bigger blocks to the Windows heap | OK; **C** sets > 256 elements and big frames hit the slow heap, free lists are never returned |

## Ranking (gain x breadth)
1. parallel BFS (3-5x on multi-core; architectural: `Rc`/`RefCell` evaluator, shared state table). **DONE (P1, 2026-11-27)**: `-workers N` only; per-thread `Setup`, states as bytes, level-synchronous. Measured x3-x6.7 at 4-16 workers. Open: liveness models stay sequential; a failing pass costs its own work (SlidingPuzzles +20 %).
2. inline `%`, `\div`, `^` in `Node::Arith` (tens of lines, same fallback): up to ~8 % of Huang, more on modular-arithmetic specs. -> H14 **DONE (H14): Huang x0.979**
3. LAMBDA / operator-argument calls without per-call `Vec` allocations and without copying the captured frame. ~12 % on SlidingPuzzles-like specs. -> H15
4. cheap hasher (`PtrHasher`-style multiplicative) for the `live.rs` / `fp_index` maps: ~3-5 % of liveness runs. -> H16
5. EXCEPT copy cost (`except1`): in-place update when the `Rc` is unique, otherwise a bulk copy; also skip `Fcn::new` work. -> H17
6. state storage (fp + parent + level per state, states re-derived for traces; Java `getState(fp, pred)`): memory ceiling, not speed.

# Java vs Rust review, second pass (2026-11-27, HEAD a7d3ab2; read-only, nothing committed)

Method: 25 micro-benchmarks, one operation repeated inside `ASSUME \A i \in 1..n : ...` (the body depends on `i`: a constant body is
cached by Rust and would not measure anything), n calibrated so Rust runs ~1 s, `-workers 1`, min of 2, JVM start-up (B.tla, n = 1)
subtracted from both sides. Java is only ~1 s warm (C2 not fully warmed): treat ratios as +-15 %, direction is what counts.
Scripts: `tmp/review_micro/{run2.py,cases2.txt,head.tla.txt}` (untracked scratch).

| case | rust/java (net) | cause (M = sampling profile) |
|---|---|---|
| `Len(Tail(Append(Seq50, i)))` | **6.4** | M: `append2` 38 % + `tail1` 30 % + `drop_glue<Value>` 12 % = per-element `Value::clone` / drop of a `Vec<Value>`; Java does `System.arraycopy` |
| `Append(Seq50, k) \in Seq(1..50)` | **5.2** | same copy + membership |
| `Seq50 \o <<i>>` | **3.8** | `natives::concat`: `to_vec()` of BOTH operands, `s.extend(t)` reallocates, no `Fast` path |
| `Cardinality(DOMAIN [F EXCEPT ![1] = i])` (20 entries) | 2.7 | `except1` `f.vals.clone()` + drop (= H17) |
| `Cardinality(Set100 \cup {i + 1000})` | **2.5** | M: `set_from` 56 % + `enumerate_inner` 22 %: `SetCup` = `to_vec` + `extend` + stable sort of two sorted runs + dedup pass; Java `cup` appends the non-members and sorts lazily. A linear merge is O(n+m) |
| `[F EXCEPT ![1] = k] \in [1..20 -> 1..20]` | 2.1 | except1 + membership |
| `Cardinality((1..100) \cap ((i % 50) .. 150))` | 2.1 | `SetCap` builds an `Rc` pair, enumerates both intervals into `Vec<Value>` |
| `Cardinality(DOMAIN (F @@ (30 :> i)))` | 2.3 | function merge through `fcn_from` (sort) |
| `Cardinality(UNION {{y, y+i} : y \in Set20})` | 1.9 | `BigUnion` -> concat + `set_from` sort |
| `Cardinality(Set100 \ {..})` | 1.6 | `SetDiff` = per-element `member` (binary search) instead of a merge |
| record EXCEPT / record build / function constructor / `<<a,b>> \in S \X T` | 1.4 - 1.7 | allocation (Rc box + Vec buffer = 2 allocs per Set/Tuple/Fcn) and Java's escape analysis removing the temporary; not a bug |
| `\E` / `\A` / filter / map over 100 elements, CHOOSE, CASE, string compare | 1.2 - 1.5 | interpretive overhead, flat |
| user operator call (3 args), recursive `Fact`, `LET` | **0.57 / 0.78 / 0.79** | Rust faster than Java |

Whole corpus (harness latest.json, HEAD 1bf86dc): Rust 247 s vs Java 756 s (Java measured with parallel JVMs). Closest to Java:
MCLamportMutex x0.90 and EWD998Small x0.89, both sequence heavy (`Append`/`Tail`/`\o`: LamportMutex.tla has 12 uses, EWD998.tla 9) -
that matches the table: sequence/function copies are where Rust is slowest.

Structural findings from reading the code (C = not measured):
- `bfs.rs` per new state: `self.states[idx].vals.clone()` (l.1674) only to call `check_invariants(&self, ..)` (a shared borrow suffices); per expanded
  state: `cur = vals.clone()` (l.1482), `vec![Undef; nvars]` (l.1491), `Rc<LabelBase>` + `Arc<str>` (l.1492; same in `par.rs` l.325). C, ~1-2 %.
- `bfs.rs` `Rec` keeps every state for the whole run (queue = `states`, traces walk `parent`): 374-1558 B/state; Java keeps (fp, parent) on disk
  and re-derives states. Ceiling, not speed (Elevator/KVS Medium die at 5 GB).
- `live.rs`: every map (`index`, `texist`, `cons`, `bits`, `leaf`, `edge_checks`, `fp_index`) is a SipHash `HashMap` on small integer keys (= H16);
  `bits`/`state_checks` clone a `Vec<bool>` per use and the same bits are stored twice (`bits` + `GNode.check_action`); `Vec<bool>` instead of bitsets;
  `live_succ[head].contains(&target)` is O(deg^2) (bfs.rs l.1655).
- `par.rs`: a pass that meets any violation/error is thrown away and the level is redone sequentially (SlidingPuzzles +20 %); one `Setup` (SANY +
  spec processing) per thread; one `Mutex` lock per successor fingerprint. Liveness models never go parallel.
- `value.rs`: `set_lit` clones the element vector (l.2114) and `set_from` clones it again when elements are model values / mixed kinds (l.390);
  `SetOfFcns::enumerate` copies the domain `Vec` for every function (`fcn_sorted(doms.to_vec(), ..)`, l.644) instead of sharing the `Rc`;
  `Rc<Vec<Value>>` = 2 allocations and 2 pointer hops per Set/Tuple (an `Rc<[Value]>` is 1).
- `eval.rs`: `capture` (l.463) copies the frame and both states; `run_frame_in` (l.482) re-copies the captured frame per call (= H15);
  `FcnCons` over > 16 elements or a non-pure body stays lazy and pays this per element when it is forced.
- `actions.rs`: `Node::Unchanged` allocates a `Vec` per evaluation (l.436), the general `[A]_v` subscript does `s0.to_vec()` (l.474).
- SANY (`tla-sany`): lexer allocates `Vec<char>` per identifier run (lexer.rs l.384) and an `Arc<str>` per token; measured fine (2.9 MB in 0.3 s, 6-17x Java).
- `alloc.rs`: blocks > 4 KB go to the process heap (lock); small free lists are never returned to the OS. OK for these workloads.

Candidates, in the order I would try them (each needs `tools/ab.py compare`; none changes enumeration order, normalization order or messages if the
fast path is limited to same-kind, non-model elements):
1. merge-based `\cup` / `\cap` / `\` of two normalized sets of the same scalar kind (and the same for `UNION`, `@@`): -50..60 % of those ops.
2. sequence natives (`Append`, `Tail`, `SubSeq`, `\o`, `Head`): one allocation, `concat` with `with_capacity(|x|+|y|)` and a `Fast` entry;
   a bulk "all scalars" copy for `Vec<Value>` (needs `unsafe` or a typed vector) - s9 rejected a global fast `Clone`, a slice-level helper was not tried.
3. H17 `except1`, H16 hasher for `live.rs`, H15 closures (already in the backlog), plus the per-state clones above.

# Third pass (2026-11-27, HEAD 0059010 + H20): phase split, liveness duplicate work

rdtsc phase counters (measurement build, `-workers 1`, harness arguments): share of `Checker::run` cycles. "rest" = everything outside
the BFS phases (= the final liveness check for the models with PROPERTIES).

| model | s | enum | constraint | fp | fpset | inv | rest |
|---|---|---|---|---|---|---|---|
| SlidingPuzzles | 1.6 | 94 | 0 | 3 | 0 | 2 | 1 |
| SimpleRegular | 2.5 | 54 | 1 | 13 | 2 | 25 | 5 |
| MCDisruptor_MPMC | 2.1 | 65 | 2 | 7 | 1 | 20 | 5 |
| MCFlashWithMutexLive | 2.9 | 4 | 0 | 0 | 0 | 0 | **96** |
| EWD998Small | 20.8 | 39 | 17 | 3 | 2 | 17 | 22 |
| MCLamportMutex | 10.7 | 65 | 4 | 8 | 1 | 14 | 8 |
| MCbtree | 8.7 | 70 | 0 | 8 | 1 | 18 | 3 |
| MCBakery | 6.1 | 42 | 1 | 5 | 1 | 0 | 51 |
| VoteProof | 3.3 | 84 | 0 | 2 | 0 | 6 | 8 |
| SpanTreeRandom | 1.5 | 11 | 0 | 2 | 0 | 5 | **82** |
| MCKVsnap | 3.5 | 6 | 0 | 8 | 0 | **55** | 31 |
| AllocatorImplementation | 3.3 | 13 | 0 | 0 | 0 | 8 | **79** |
| bcastByz | 3.1 | 24 | 0 | 2 | 0 | 1 | **73** |
| YoYoAllGraphs | 3.2 | 20 | 0 | 1 | 0 | 28 | 51 |
| ElevatorLivenessMedium | 2.4 | 3 | 0 | 0 | 0 | 1 | **96** |
| Huang | 16.1 | 8 | 2 | 1 | 0 | 7 | 82 |
| EWD998PCal | 13.5 | 24 | 4 | 2 | 1 | 0 | 70 |
| MultiPaxos_MC_small | 11.7 | 36 | 0 | **47** | 0 | 16 | 1 |
| TLCSailfish1 | 22.9 | 56 | 0 | 2 | 0 | **41** | 1 |
| MCNanoMedium | 9.0 | 44 | 0 | 3 | 1 | **50** | 2 |
| DijkstraMutex Safety-4 | 278 | 82 | 1 | 7 | 3 | 3 | 5 |
| MCCheckpointCoordinationFailure | 8.1 | 26 | 3 | **66** | 0 | 4 | 1 |
| FastPaxos | 6.5 | 29 | 0 | **69** | 0 | 1 | 1 |

Liveness leaves (counter in `Leaf::eval_bool` / `eval_enabled`; share of the run, evaluations, cycles per evaluation):

| model | Oos x action leaves | edges | action `<<A>>_v` | ENABLED | graph SCC |
|---|---|---|---|---|---|
| MCFlashWithMutexLive | 12 x 9 | 36k | 47 %, 1.03M x 4.5k | 35 %, 874k x 4.0k | small |
| ElevatorLivenessMedium | 6 x 26 (256 PEMs each) | 15k | 31 %, 904k x 2.7k | 17 %, 445k x 2.9k | ~40 % |
| SpanTreeRandom (`WF_vars(Next)`) | 1 x 1 | 253k | 69 %, 269k x 12k | 2 % | small |
| AllocatorImplementation | 1 x 122 | 82k | 16 %, 340k x 4.9k | 31 %, 2.16M x 1.6k | |
| bcastByz | 3 x 1 | 101k | 60 %, 275k x 22k | 9 % | |
| YoYoAllGraphs | 1 x 1 | 75k | 36 %, 102k x 35k | 11 % | |
| Huang | 2 x 10 | 626k | 18 %, 5.6M x 1.7k | 6 % | |

Duplicate work: the ENABLED count of MCFlashWithMutexLive is exactly states x leaves x Oos (8096 x 9 x 12). Java does the same
(`LiveCheck.addNextState` -> `oos.checkAction` per checker). Shared across Oos = H20: `ab.py compare --set full` ACCEPT 0.866.
MCBakery's and EWD998PCal's "rest" is not leaf evaluation (0 leaf evaluations): still to be identified (implied actions / `[]` PROPERTY?).

Next candidates (backlog H21-H23 in `loop/PERF.md`): SCC per PEM (Elevator ~70 % of what is left), invariant/constraint conjuncts
skipped when their variables did not change (BFS models, 14-55 % in invariants), cheaper eval-mode `x' = [x EXCEPT ..]` (SpanTreeRandom).
Symmetry `fp` (canonicalization) is 47-69 % of MultiPaxos / Checkpoint / FastPaxos (not in the FULL set).

# Fourth pass (2026-11-27, HEAD 3c24d66): the models where Rust is closest to Java

Java alone vs Rust (364-model sequential run, before H25): MCLamportMutex x0.927, EWD998Small x0.848, SlidingPuzzles x0.813,
GameOfLife x0.794, MCBakery x0.713, MCDisruptor_MPMC x0.707, SimpleRegular x0.694, MultiPaxos_MC_small x0.689, SlushSmall x0.662.
These runs are long, so Java's JIT is warm: what decides is the raw cost per operation, not start-up.

Where the time goes (rdtsc phases; node profile restricted to a phase with `TLCRS_PROF_PHASE`):
| model | phases | hottest nodes (node self time) |
|---|---|---|
| MCLamportMutex | enum 65, inv 14 (+5 outside the constraint), fp 8, constraint 4 | enum: Except 24, Eq/Neq 20, Head/Tail/Append 11; inv: In 41 |
| EWD998Small | enum 39, inv 16 + 17 outside the constraint, constraint 17 | inv: In 16, FoldFunctionOnSet 13, Rng 12, Sum 7 |
| SimpleRegular | enum 54, inv 25, fp 14 | In 21, Except 20, Eq 13 |
| GameOfLife | enum 98 | FcnApply 15 (lazy `sc`), Call(Sum) 13, Or 8, SetMinus 7 |
| MCBakery | init 45 (`ISpec`), enum 44 | In 16, And 12, IInv 12, Eq 11, Except 9 |
| SlidingPuzzles | enum 94 | CallLocal 17 (LAMBDA), FcnApply 12, Tuple 9 |
| MCDisruptor_MPMC | enum 65, inv 20 | SubstIn 14, Except 12, In 9 |
| SlushSmall | enum 87 | Eq 25, Except 11, Memo(SubsetOf) 10 |
Sampling (MCLamportMutex): clone/drop/alloc ~16 %, hash_into 7.8 %, needs_normalize 4 %, member_impl 4.6 %, interpreter dispatch ~25 %.

Results on this set (A/B against the previous HEAD):
- H25 (committed): GameOfLife x0.904, EWD998Small x0.950, SimpleRegular x0.969, Disruptor x0.979, Slush x0.983, LamportMutex x0.985,
  Bakery x0.988, SlidingPuzzles x0.991 = geomean ~0.97 on the 8 models; also Huang x0.944, EWD998PCal x0.956.
- H24 Fcn membership memo: no effect (functions over `1..N` are Tuples). s11 no value memo for cheap defs: no effect.
- H26 prototype (algebraic Fcn hash, O(1) update by EXCEPT; `tmp/perf_research/h26_algebraic_fcn_hash.patch`, not committed: changes
  fingerprint values, which PROMPT_PERF.md forbids): SimpleRegular x0.924, Disruptor x0.971, but EWD998Small x1.017, LamportMutex x1.012,
  MultiPaxos x1.023 (records and other freshly built functions pay one finalizer per pair). Would need a cheaper pair combiner.

Conclusion: no local change left gives >= 10 % on these models; each remaining item is 2-5 %. What is left (expected gain):
1. H27 one-allocation Tuple/Set with a header (cached hash, normal-form flag): every state fingerprint rehashes `1..N` functions
   (fp phase LamportMutex 7.6 %, Disruptor 6.6 %, Slush 6.5 %, Bakery 5.6 %), two allocations per tuple, `needs_normalize` 4 %.
   Estimate LamportMutex -8..10 %, Bakery/Slush/Disruptor -5..7 %. Large refactor (`Rc<Vec<Value>>` everywhere); a thin DST needs `unsafe`.
2. H15 LAMBDA / operator-argument calls (SlidingPuzzles CallLocal 17 %): -8..10 % there.
3. Invariants of successors outside the constraint checked once per distinct state (EWD998Small: 1.6M checks, 1.18M distinct): <= -4.6 %.
4. H28 FpSet prefetch (MCBakery FpSet::insert 4.5 %): <= -3 %.
5. Interpreter dispatch (eval_inner + enum_* ~25 %): only a closure/bytecode compilation would move it; weeks of work.

# Fifth pass (2026-11-27, HEAD 78655c3): cumulative result on the models closest to Java

Java alone vs the build before this research (5d01875, H20; `tmp/h20.exe`, built in the same directory) vs HEAD (H25 + H22 + H29),
interleaved per model, sequential, min of 3, all signatures identical (`cmp3.py`-style run, scratch script):
| model | Java alone | H20 | HEAD | HEAD/H20 | HEAD/Java |
|---|---|---|---|---|---|
| MCLamportMutex | 11.04 | 10.17 | 8.94 | **x0.880** | x0.810 |
| EWD998Small | 24.32 | 20.19 | 17.08 | **x0.846** | x0.703 |
| SlidingPuzzles | 1.47 | 1.18 | 1.12 | x0.948 | x0.757 |
| GameOfLife | 9.11 | 7.24 | 6.50 | **x0.898** | x0.714 |
| MCBakery | 7.60 | 5.55 | 4.76 | **x0.858** | x0.626 |
| MCDisruptor_MPMC | 2.98 | 2.05 | 1.97 | x0.961 | x0.662 |
| SimpleRegular | 3.51 | 2.42 | 1.92 | **x0.792** | x0.547 |
| MultiPaxos_MC_small | 16.34 | 11.16 | 10.12 | x0.907 | x0.619 |
| SlushSmall | 5.57 | 3.75 | 3.38 | x0.901 | x0.608 |
| **geomean (9)** | | | | **x0.887** | x0.667 (was x0.753) |
What did it, by model: invariants/constraints of successors (H22: EWD998Small, MCLamportMutex, SimpleRegular, MultiPaxos), PlusCal label
dispatch (H29: MCBakery, SimpleRegular, Slush), EXCEPT path + memo lookups + Sum memo (H25: GameOfLife, EWD998Small), LAMBDA calls (H15: SlidingPuzzles).
Still open: H27 (Tuple header: fingerprint 7-15 %, needs the fingerprint rule relaxed for the hash cache), H28 FpSet prefetch, symmetry (MultiPaxos fp 46 %).
