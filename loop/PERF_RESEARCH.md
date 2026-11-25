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
