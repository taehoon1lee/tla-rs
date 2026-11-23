"""Best-of-N CPU time of tlc-rs executables on a scratch model.
usage: python tools/cpu_dir.py exe1,exe2 [-n N] <dir> <Spec.tla> [<Spec.cfg>]
Runs `tlc -tool -workers 1 -config <cfg> <spec>` in <dir>; prints wall/CPU (GetProcessTimes) and the state counts line."""
import sys, subprocess, ctypes, time, re
from ctypes import wintypes
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


class FT(ctypes.Structure):
    _fields_ = [("lo", wintypes.DWORD), ("hi", wintypes.DWORD)]


def ft(x):
    return ((x.hi << 32) | x.lo) / 10_000.0


def run(cmd, cwd):
    t0 = time.time()
    p = subprocess.Popen(cmd, cwd=cwd, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, text=True, errors="replace")
    out = p.communicate()[0]
    wall = (time.time() - t0) * 1000
    c, e, k, u = FT(), FT(), FT(), FT()
    ctypes.windll.kernel32.GetProcessTimes(int(p._handle), ctypes.byref(c), ctypes.byref(e), ctypes.byref(k), ctypes.byref(u))
    m = re.findall(r"(\d+) states generated, (\d+) distinct states found", out)
    return wall, ft(k) + ft(u), (m[-1] if m else None)


def main():
    args = sys.argv[1:]
    n = 5
    if "-n" in args:
        i = args.index("-n")
        n = int(args[i + 1])
        del args[i:i + 2]
    exes = args[0].split(",")
    d = Path(args[1]).resolve()
    spec = args[2]
    cfg = args[3] if len(args) > 3 else Path(spec).stem + ".cfg"
    row = []
    for exe in exes:
        bw, bc, counts = 1e18, 1e18, None
        for _ in range(n):
            w, c, counts = run([str((ROOT / exe).resolve()), "tlc", "-tool", "-workers", "1", "-config", cfg, spec], d)
            bw, bc = min(bw, w), min(bc, c)
        row.append(f"wall {bw:7.0f} cpu {bc:7.0f} {counts}")
    print(" | ".join(row))


main()
