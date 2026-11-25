You are one iteration of an autonomous PERFORMANCE loop for `tlc-rs` (Rust port of TLC 1.8.0). Correctness is already
done (verdict 364/364, trace 364/364): the job now is to make `tlc-rs` FASTER without changing a single observable
behaviour. Your memory does not survive this iteration: everything you need is in files, everything you learn must be
written back to files. Work ONLY inside the current working directory (the repo root that contains `CLAUDE.md`).
Read `CLAUDE.md` first (rules + commands). Its hard rules still apply (no cheating, no regressions, pure-Rust deps only).

## Yardstick (read this once, it explains the whole procedure)
- The harness perf level (`rust <= 1.10*golden+50ms`) is SATURATED (364/364) and too lenient: goldens were timed with 3-4
  JVMs in parallel, Java alone is 7-19 % faster. Do NOT use `check.py` perf numbers to judge your work.
- The judge for this loop is `tools/ab.py` (do not edit it): `snapshot` keeps the BASE exe (= HEAD), `compare` runs BASE and
  your build INTERLEAVED, sequentially, min of N, on a fixed model set, checks that BASE and NEW print IDENTICAL results
  (states generated/distinct/left, depth, trace, errors, Print output) and prints `AB RESULT: ACCEPT|NEUTRAL|REJECT|MISMATCH`
  (exit 0 / 2 / 1 / 3). `time` compares the current exe with Java ALONE. Noise is about +-3 %; a change smaller than that is
  not a result.
- Goal order: (1) every model of the full set <= Java alone (x1.00); (2) then lower the geomean of rust/base further.
- Single worker only (`-workers 1`, as in the harness). Do not add threads, do not change BFS/enumeration order.

## Procedure (follow in order, do ONE hypothesis, then stop)

1. **Orient (<= 6 tool calls).**
   - `tail -n 30 loop/PROGRESS.md`, read `loop/PERF.md` (standing table, backlog, LEDGER of everything already tried),
     and the sections of `loop/NOTES.md` about performance ("Performance tooling", "Perf pass 5", "Perf review").
     NEVER repeat a hypothesis that is in the LEDGER as REJECT/NEUTRAL unless you have a concrete new reason written
     down in the LEDGER row you add.
   - If `loop/LAST_REJECTED.md` exists: the driver reverted the previous iteration (correctness gate failed or build
     broke); its work is on the branch named in the file. Read it, write the lesson into `loop/NOTES.md`, and
     `git rm loop/LAST_REJECTED.md` in this iteration's commit.

2. **Measure + choose (<= 8 tool calls).**
   - `cargo build --release`, then `python tools/ab.py snapshot` (refuses if `crates/` is dirty). From now on do not
     commit before the A/B run: BASE must stay equal to HEAD.
   - Pick the FIRST open hypothesis `[ ]` of the backlog in `loop/PERF.md`. If the backlog is empty: run
     `python tools/ab.py time --set full` (~4 min, Bash timeout 600000), take the model with the worst rust/java ratio,
     profile it (`tools/README.md`: build `target-prof` once, then `python tools/prof.py <id> --top 25`, `--lines <fn>`),
     and write 3 new hypotheses (with expected gain and how to test) into the backlog. Then work on the best one.
   - Write one line to yourself: "This iteration I will test hypothesis H<n>: <change>, expecting <model> -<x> %."
     Keep the change small (<= ~200 lines of Rust).

3. **Study.** Read the Rust hot path you will change (`grep -n`, then ~100 lines around). Use the Java code only as a
   source of ideas for how Java avoids the work (caching, laziness, in-place update) -- the observable behaviour must stay
   identical, so never copy a Java shortcut that changes enumeration order, error text or counts.

4. **Implement exactly that one hypothesis.** Constraints that were learned the hard way (details in NOTES.md):
   - No `thread_local!` and no `Instant::now()` on a per-state/per-eval path (windows-gnu: ~10 ns per TLS access).
   - Keep `eval_inner` small: no new locals; cold/big arms go to `#[inline(never)]` helpers. Check the operand kind
     first, only then call the new path (a probe that rarely hits made EWD998PCal 4 % slower).
   - Error texts, call-stack replay (`Ev::replay`), set normalization order, fingerprints: unchanged.
   - Do not skip checks (invariants, assumptions, constraints, deadlock), do not cache by model/module/spec name,
     do not weaken a semantic step to save time. No new crates (ask in NOTES.md first), no `unsafe` unless the profile
     proves it necessary and the LEDGER row says so.
   - Add a `#[cfg(test)]` test for new logic where one is meaningful. `cargo test -q` must pass; fix warnings you introduced.

5. **Verify -- in this order (cheap first). Long commands: Bash `timeout` 600000, or run in the background and wait.**
   a. `cargo build --release` and `cargo test -q`.
   b. `python tools/ab.py compare --set quick` (~1.5 min) plus your target model(s):
      `python tools/ab.py compare <id> --reps 3`. At most 3 build+quick cycles per iteration (tweak, rebuild, re-run).
      Never re-run an unchanged binary hoping for a better number. The only allowed re-run: a single REJECT/NEUTRAL
      model re-measured with `--reps 5`; the result of the longer run is final.
   c. If quick shows MISMATCH -> your change altered behaviour: fix or revert, do not continue.
      If quick shows REJECT -> go to 6 (REJECT). If quick shows nothing better than noise -> go to 6 (NEUTRAL).
   d. Quick looks good: `python tools/ab.py compare --set full` (~7 min). This is the acceptance run.
   e. Only on ACCEPT: `python harness/check.py --gate` MUST exit 0 (correctness of the whole corpus; perf level is not
      gated). The driver re-runs the gate after you; never commit something you have not gated.
      Do not run timing tools and the gate at the same time (they disturb each other).

6. **Decide and record -- every outcome is recorded, a rejected experiment is a result too.**
   - ACCEPT (full set `AB RESULT: ACCEPT` AND gate rc 0): commit code + notes.
   - NEUTRAL / REJECT / MISMATCH: `git checkout -- crates` (discard the code), commit ONLY the notes.
   - In every case: append a row to the LEDGER in `loop/PERF.md`
     `| Hn | ACCEPT/NEUTRAL/REJECT/MISMATCH | what was changed | target model before -> after | full geomean | why it worked / failed |`,
     tick the backlog item (`[x]`, or split it into smaller `[ ]` ones if it was too big), update the "Standing" table
     if you measured a new full `time`, add durable lessons to `loop/NOTES.md` (short bullets, include numbers).
   - Append to `loop/PROGRESS.md` (max 5 lines):
     `## <date> perf H<n> -- ACCEPT|NEUTRAL|REJECT: <summary>` / the `AB RESULT` line / what is next.
   - `git add -A && git commit -m "perf H<n>: <summary> (<model> x<ratio>, geomean <g>)"`
     (notes-only commits: `perf H<n> (no code): <why it did not help>`).
   - Do NOT run `check.py --update-best`: the driver owns the baseline.

7. **Stop.** End with a 3-line summary: hypothesis, A/B numbers, next hypothesis. Do not start a second hypothesis.

## If stuck
- Build errors you cannot fix in 3 attempts, or a MISMATCH you cannot explain: `git checkout -- crates`, write what you
  learned into the LEDGER/NOTES, commit only those notes, stop.
- Never edit `harness/`, `reference/`, `tools/ab.py`, `loop/PROMPT*.md`, `loop/run-loop.ps1`, `loop/haiku-settings.json`,
  `CLAUDE.md`. If you believe the judge is wrong, write the evidence under "HARNESS ISSUES" in `loop/NOTES.md`
  and work on something else.

## Reminders
- A profile beats intuition: look at `tools/prof.py` output before editing. Optimize what is hot, not what looks slow.
- Prefer removing work (a clone, an allocation, a re-evaluation, a copied frame) over making the same work cheaper.
- Same answers as Java stay non-negotiable; speed bought by a different state count or trace is a failure, not a win.
- Keep tool outputs short (`| head -50`, `| tail -20`); read big files by line range.
