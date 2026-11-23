"""Node-kind profile of one corpus model for a limited time.  usage: python tools/profnode_t.py <check-id> [seconds]
Needs `--features "tlc-cli/sprof tlc-check/prof"` in target-prof.  The profiler prints a report to stderr every 20 s."""
import json, subprocess, tempfile, os, sys, time
from pathlib import Path
ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "harness"))
import common as C

eid = sys.argv[1]
secs = int(sys.argv[2]) if len(sys.argv) > 2 else 45
c = json.load(open(ROOT / "harness/corpus.json"))
e = [x for x in c["check"] if x["id"] == eid][0]
with tempfile.TemporaryDirectory() as d:
    meta = Path(d) / "meta"
    meta.mkdir()
    cmd = [str(ROOT / "target-prof/release/tlc-rs.exe")] + C.rust_base("tlc")[1:] + C.tlc_args(e, meta)
    env = dict(os.environ)
    env["TLCRS_PROF"] = "1"
    errf = Path(d) / "err.txt"
    with open(errf, "w") as ef:
        p = subprocess.Popen(cmd, cwd=d, env=env, stdout=subprocess.DEVNULL, stderr=ef)
        t0 = time.time()
        while p.poll() is None and time.time() - t0 < secs:
            time.sleep(0.5)
        if p.poll() is None:
            p.kill()
    txt = errf.read_text(errors="replace")
    # keep only the last report
    i = txt.rfind("SAMPLES total=")
    print(txt[i:] if i >= 0 else txt[-3000:])
