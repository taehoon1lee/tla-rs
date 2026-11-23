"""Run one corpus model with the harness arguments and a chosen executable; stderr is passed through.
usage: python tools/run_id.py <exe> <check-id> [seconds] [VAR=value ...]   (stdout is discarded unless TLCRS_SHOW=1)"""
import json, subprocess, tempfile, os, sys, time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "harness"))
import common as C

exe, eid = sys.argv[1], sys.argv[2]
secs = float(sys.argv[3]) if len(sys.argv) > 3 and not "=" in sys.argv[3] else 60.0
env = dict(os.environ)
for a in sys.argv[3:]:
    if "=" in a:
        k, v = a.split("=", 1)
        env[k] = v
c = json.load(open(ROOT / "harness/corpus.json"))
e = [x for x in c["check"] if x["id"] == eid][0]
with tempfile.TemporaryDirectory() as d:
    meta = Path(d) / "meta"
    meta.mkdir()
    cmd = [str((ROOT / exe).resolve())] + C.rust_base("tlc")[1:] + C.tlc_args(e, meta)
    out = None if os.environ.get("TLCRS_SHOW") else subprocess.DEVNULL
    p = subprocess.Popen(cmd, cwd=d, env=env, stdout=out)
    t0 = time.time()
    while p.poll() is None and time.time() - t0 < secs:
        time.sleep(0.2)
    if p.poll() is None:
        p.kill()
        print("(killed after %.0fs)" % secs, file=sys.stderr)
