"""A/B timing + behaviour-equivalence judge for the PERFORMANCE loop (loop/PROMPT_PERF.md).  Read-only use of harness/.

  python tools/ab.py snapshot                              # build HEAD (crates/ must be clean), keep the exe as the BASE
  python tools/ab.py compare [--set quick|full] [--reps N] [ids-or-substrings...]
                                                           # BASE vs target/release/tlc-rs.exe, interleaved, min of N
  python tools/ab.py time    [--set quick|full] [--reps N] [ids-or-substrings...]
                                                           # current exe vs Java ALONE (sequential), worst ratio first
  python tools/ab.py java    [--set quick|full] [--reps N] [--force] [ids...]
                                                           # (re)measure Java alone -> tmp/ab/java_alone.json

`compare` exit codes:  0 ACCEPT (real gain, nothing slower)   1 REJECT (a model is slower)
                       2 NEUTRAL (inside the noise: no code commit)   3 MISMATCH (behaviour differs from BASE)   4 usage/setup error
Why not the harness perf level: it compares with the goldens' Java time, which was measured with 3-4 JVMs in parallel
(7-19 % pessimistic for Java).  Here Java ALONE (sequential, same command line) is the yardstick and the A/B partner is
your own previous binary, run interleaved so that machine drift cancels.
"""
import argparse, hashlib, json, math, os, shutil, subprocess, sys, tempfile, time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "harness"))
import common as C       # noqa: E402  (read-only use)
import tlcout            # noqa: E402

AB = ROOT / "tmp" / "ab"
BASE_EXE, BASE_REV, JAVA_CACHE = AB / "base.exe", AB / "base.rev", AB / "java_alone.json"
NEW_EXE = Path(C.RUST_BIN)

# Sets (corpus ids).  quick ~10 s per exe (inner loop); full ~95 s per exe (acceptance).  Mix: safety, liveness, big values.
QUICK = ["ex/SlidingPuzzles/SlidingPuzzles", "ex/TeachingConcurrency/SimpleRegular", "ex/Disruptor/MCDisruptor_MPMC",
         "ex/FlashProtocol/MCFlashWithMutexLive"]
FULL = QUICK + ["ex/ewd998/EWD998Small", "ex/lamport_mutex/MCLamportMutex", "ex/btree/MCbtree",
                "ex/Bakery-Boulangerie/MCBakery", "ex/byzpaxos/VoteProof", "ex/SpanningTree/SpanTreeRandom",
                "ex/KeyValueStore/MCKVsnap", "ex/allocator/AllocatorImplementation", "ex/bcastByz/bcastByz",
                "ex/YoYo/YoYoAllGraphs", "ex/MultiCarElevator/ElevatorLivenessMedium"]

# Decision thresholds (min-of-N interleaved timings; noise on this box is about +-3 %).
SLOWER_PCT, SLOWER_ABS_S = 4.0, 0.04      # a model is "slower" if new > base*(1+4 %) + 40 ms
GAIN_GEOMEAN, GAIN_ONE = 0.98, 0.93       # real gain: geomean(new/base) <= 0.98 or some model <= 0.93
SAME_FIELDS = ["exit_code", "first_error", "violation", "errors", "trace", "trace_tail", "generated", "distinct", "left",
               "depth", "outdegree", "init_distinct", "output"]


def corpus():
    return {x["id"]: x for x in json.load(open(C.CORPUS_FILE))["check"]}


def select(args):
    byid = corpus()
    if args.ids:
        ids = [i for i in byid if any(p == i or p in i for p in args.ids)]
    else:
        ids = QUICK if args.set == "quick" else FULL
    missing = [i for i in ids if i not in byid]
    if missing:
        sys.exit(f"unknown corpus ids: {missing}")
    return [byid[i] for i in ids]


def run_tlc(cmd_prefix, e, timeout=900):
    with tempfile.TemporaryDirectory() as d:
        meta = Path(d) / "meta"
        meta.mkdir()
        rc, out, _err, ms = C.run_proc(cmd_prefix + C.tlc_args(e, meta), timeout, cwd=Path(d))
    return rc, out, ms / 1000.0


def rust_cmd(exe):
    return [str(exe)] + C.rust_base("tlc")[1:]


def signature(rc, out):
    p = tlcout.parse_tlc(out, rc)
    return {k: p.get(k) for k in SAME_FIELDS}


def newest_source_mtime():
    best = 0.0
    for pat in ("crates/**/*.rs", "crates/**/Cargo.toml", "Cargo.toml", "Cargo.lock"):
        for f in ROOT.glob(pat):
            best = max(best, f.stat().st_mtime)
    return best


def cargo_build():
    env = dict(os.environ)
    env["PATH"] = str(Path.home() / ".cargo" / "bin") + os.pathsep + env.get("PATH", "")
    r = subprocess.run(["cargo", "build", "--release", "-q"], cwd=ROOT, env=env)
    return r.returncode == 0


def git(*a):
    return subprocess.run(["git", *a], cwd=ROOT, capture_output=True, text=True).stdout.strip()


def load_java():
    return json.load(open(JAVA_CACHE)) if JAVA_CACHE.exists() else {}


# ---------------------------------------------------------------------------------------------------------------------
def cmd_snapshot(a):
    dirty = git("status", "--porcelain", "--", "crates", "Cargo.toml", "Cargo.lock")
    if dirty:
        sys.exit("snapshot refused: crates/ has uncommitted changes (the BASE must be exactly HEAD):\n" + dirty)
    if not cargo_build():
        sys.exit("cargo build --release failed")
    AB.mkdir(parents=True, exist_ok=True)
    shutil.copy2(NEW_EXE, BASE_EXE)
    BASE_REV.write_text(git("rev-parse", "HEAD"))
    print(f"BASE = HEAD {git('rev-parse', '--short', 'HEAD')} -> {BASE_EXE.relative_to(ROOT)}")


def cmd_compare(a):
    if not BASE_EXE.exists():
        sys.exit("no BASE: run `python tools/ab.py snapshot` BEFORE editing crates/")
    if not NEW_EXE.exists() or NEW_EXE.stat().st_mtime < newest_source_mtime():
        sys.exit("target/release/tlc-rs.exe is older than the sources: run `cargo build --release` first")
    if BASE_REV.read_text().strip() != git("rev-parse", "HEAD"):
        print("WARNING: HEAD moved since the snapshot - BASE is not the parent of your change", flush=True)
    same_bin = hashlib.sha1(BASE_EXE.read_bytes()).digest() == hashlib.sha1(NEW_EXE.read_bytes()).digest()
    if same_bin:
        print("WARNING: new exe is byte-identical to BASE (nothing changed, or the change was not built)", flush=True)
    java = load_java()
    rows, mismatch = [], []
    print(f"{'model':52s} {'base s':>8s} {'new s':>8s} {'new/base':>8s} {'new/java':>8s}", flush=True)
    for e in select(a):
        tb, tn, sig0 = [], [], None
        for rep in range(a.reps):
            order = [("b", BASE_EXE), ("n", NEW_EXE)] if rep % 2 == 0 else [("n", NEW_EXE), ("b", BASE_EXE)]
            for tag, exe in order:
                rc, out, s = run_tlc(rust_cmd(exe), e)
                if rc is None:
                    sys.exit(f"{e['id']}: timeout")
                sig = signature(rc, out)
                if sig0 is None:
                    sig0 = sig          # first run of the first rep is always BASE or NEW: both must agree anyway
                if sig != sig0:
                    mismatch.append((e["id"], tag, [k for k in SAME_FIELDS if sig[k] != sig0[k]]))
                (tb if tag == "b" else tn).append(s)
        b, n = min(tb), min(tn)
        j = java.get(e["id"])
        rows.append((e["id"], b, n))
        print(f"{e['id']:52s} {b:8.2f} {n:8.2f} {n / b:8.3f} {('%8.3f' % (n / j)) if j else '       -'}", flush=True)
    if mismatch:
        print("MISMATCH (behaviour differs between BASE and NEW; fix correctness before anything else):")
        for m in mismatch:
            print("  ", m)
        print("AB RESULT: MISMATCH")
        return 3
    slower = [(i, n / b) for i, b, n in rows if n > b * (1 + SLOWER_PCT / 100) + SLOWER_ABS_S]
    ratios = [n / b for _, b, n in rows]
    geo = math.exp(sum(math.log(r) for r in ratios) / len(ratios))
    summary = f"geomean new/base {geo:.3f}, best {min(ratios):.3f}, worst {max(ratios):.3f}, models {len(rows)}, reps {a.reps}"
    if slower:
        print("SLOWER than BASE: " + ", ".join(f"{i} x{r:.3f}" for i, r in slower))
        print(f"AB RESULT: REJECT  ({summary})")
        return 1
    if same_bin:
        print(f"AB RESULT: NEUTRAL  ({summary}); identical binaries, so the ratios above are pure noise")
        return 2
    if geo <= GAIN_GEOMEAN or min(ratios) <= GAIN_ONE:
        print(f"AB RESULT: ACCEPT  ({summary})")
        return 0
    print(f"AB RESULT: NEUTRAL  ({summary}); gain needs geomean <= {GAIN_GEOMEAN} or a model <= {GAIN_ONE}")
    return 2


def measure(cmd_prefix, e, reps):
    best = 1e9
    for _ in range(reps):
        rc, _out, s = run_tlc(cmd_prefix, e, timeout=1800)
        best = min(best, s)
    return best


def cmd_java(a):
    AB.mkdir(parents=True, exist_ok=True)
    cache = load_java()
    for e in select(a):
        if e["id"] in cache and not a.force:
            continue
        cache[e["id"]] = round(measure(C.java_base("tlc2.TLC"), e, a.reps), 3)
        json.dump(cache, open(JAVA_CACHE, "w"), indent=1, sort_keys=True)
        print(f"{e['id']:52s} java alone {cache[e['id']]:8.2f} s", flush=True)


def cmd_time(a):
    java = load_java()
    rows = []
    for e in select(a):
        n = measure(rust_cmd(NEW_EXE), e, a.reps)
        j = java.get(e["id"])
        rows.append((n / j if j else 0.0, e["id"], n, j))
        print(f"{e['id']:52s} rust {n:8.2f} s  java alone {('%8.2f' % j) if j else '       ?'} s", flush=True)
    print("\nworst first (rust/java alone; > 1.00 = slower than Java):")
    for r, i, n, j in sorted(rows, reverse=True):
        print(f"  {i:52s} x{r:5.3f}" if j else f"  {i:52s} (no Java time: run `ab.py java`)")
    return 0


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("cmd", choices=["snapshot", "compare", "time", "java"])
    ap.add_argument("ids", nargs="*")
    ap.add_argument("--set", choices=["quick", "full"], default="quick")
    ap.add_argument("--reps", type=int, default=None)
    ap.add_argument("--force", action="store_true")
    a = ap.parse_args()
    if a.reps is None:
        a.reps = {"compare": 3 if a.set == "quick" else 2, "time": 2, "java": 2}.get(a.cmd, 1)
    sys.exit(globals()["cmd_" + a.cmd](a) or 0)


if __name__ == "__main__":
    main()
