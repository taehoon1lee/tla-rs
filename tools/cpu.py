"""CPU-time (user+kernel) and wall time of several tlc-rs executables on corpus models, best of N runs.
usage: python tools/cpu.py exe1,exe2 [-n N] id1 id2 ...
CPU time is much less sensitive to other load on the machine than wall time (Windows only: GetProcessTimes)."""
import sys, json, tempfile, subprocess, ctypes, time
from ctypes import wintypes
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "harness"))
import common as C


class FT(ctypes.Structure):
    _fields_ = [("lo", wintypes.DWORD), ("hi", wintypes.DWORD)]


def ft(x):
    return ((x.hi << 32) | x.lo) / 10_000.0  # 100ns ticks -> ms


def run(cmd, cwd):
    t0 = time.time()
    p = subprocess.Popen(cmd, cwd=cwd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    p.wait()
    wall = (time.time() - t0) * 1000
    c, e, k, u = FT(), FT(), FT(), FT()
    ctypes.windll.kernel32.GetProcessTimes(int(p._handle), ctypes.byref(c), ctypes.byref(e), ctypes.byref(k), ctypes.byref(u))
    return wall, ft(k) + ft(u)


def main():
    args = sys.argv[1:]
    n = 3
    if "-n" in args:
        i = args.index("-n")
        n = int(args[i + 1])
        del args[i:i + 2]
    exes = args[0].split(",")
    c = json.load(open(ROOT / "harness" / "corpus.json"))
    byid = {x["id"]: x for x in c["check"]}
    for eid in args[1:]:
        e = byid[eid]
        row = []
        for exe in exes:
            best_w, best_c = 1e18, 1e18
            for _ in range(n):
                with tempfile.TemporaryDirectory() as d:
                    meta = Path(d) / "meta"
                    meta.mkdir()
                    cmd = [str(ROOT / exe)] + C.rust_base("tlc")[1:] + C.tlc_args(e, meta)
                    w, cpu = run(cmd, d)
                best_w, best_c = min(best_w, w), min(best_c, cpu)
            row.append(f"wall {best_w:7.0f} cpu {best_c:7.0f}")
        print(f"{eid:50s} " + " | ".join(row), flush=True)


main()
