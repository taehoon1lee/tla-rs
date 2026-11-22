import json, subprocess, tempfile, os, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "harness"))
import common as C
eid = sys.argv[1]
c = json.load(open(ROOT / "harness/corpus.json"))
e = [x for x in c["check"] if x["id"] == eid][0]
with tempfile.TemporaryDirectory() as d:
    meta = Path(d) / "meta"; meta.mkdir()
    cmd = [str(ROOT / "target-prof/release/tlc-rs.exe")] + C.rust_base("tlc")[1:] + C.tlc_args(e, meta)
    env = dict(os.environ); env["TLCRS_PROF"] = "1"
    for k in sys.argv[2:]:
        kk, vv = k.split("=", 1); env[kk] = vv
    p = subprocess.run(cmd, cwd=d, env=env, capture_output=True, text=True, encoding="utf-8", errors="replace")
    print(p.stderr[-3500:])
