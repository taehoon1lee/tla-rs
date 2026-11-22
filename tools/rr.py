"""Run one corpus model with tlc-rs using the harness arguments; print the filtered output tail.
usage: python tools/rr.py <id> [--full] [--time]"""
import sys, json, tempfile, time, subprocess
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "harness"))
import common as C

eid = sys.argv[1]
c = json.load(open(C.ROOT / "harness" / "corpus.json"))
e = [x for x in c["check"] if x["id"] == eid][0]
with tempfile.TemporaryDirectory() as d:
    meta = Path(d) / "meta"
    meta.mkdir()
    cmd = C.rust_base("tlc") + C.tlc_args(e, meta)
    t0 = time.time()
    p = subprocess.run(cmd, cwd=d, capture_output=True, text=True, encoding="utf-8", errors="replace",
                       timeout=float(sys.argv[sys.argv.index("--timeout") + 1]) if "--timeout" in sys.argv else 600)
    dt = time.time() - t0
    out = p.stdout
    if "--full" not in sys.argv:
        i = out.find("@!@!@STARTMSG 2185")
        out = out[i:] if i >= 0 else out
    print(out[-6000:] if "--full" not in sys.argv else out)
    print("STDERR:", p.stderr[-1500:])
    print(f"exit={p.returncode} time={dt:.2f}s")
