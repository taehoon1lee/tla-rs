"""Profile one corpus model with the sampling build (target-prof), then symbolize.
usage: python tools/prof.py <id> [--top N]"""
import json, subprocess, tempfile, os, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "harness"))
import common as C

eid = sys.argv[1]
c = json.load(open(ROOT / "harness/corpus.json"))
e = [x for x in c["check"] if x["id"] == eid][0]
out = ROOT / "tmp" / "sp.txt"
if out.exists():
    out.unlink()
with tempfile.TemporaryDirectory() as d:
    meta = Path(d) / "meta"
    meta.mkdir()
    cmd = [str(ROOT / "target-prof/release/tlc-rs.exe")] + C.rust_base("tlc")[1:] + C.tlc_args(e, meta)
    env = dict(os.environ)
    env["TLCRS_SPROF"] = str(out)
    p = subprocess.run(cmd, cwd=d, env=env, capture_output=True, text=True, encoding="utf-8", errors="replace")
    print(p.stderr[-300:])
rest = sys.argv[2:]
subprocess.run([sys.executable, str(ROOT / "tools/symbolize.py"), str(out), str(ROOT / "target-prof/release/tlc-rs.exe")] + rest)
