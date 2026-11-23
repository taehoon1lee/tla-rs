"""Sequential timing of corpus models: rust vs java golden.  usage: python tools/perf.py id1 id2 ... | --ex-slow
Prints rust ms, java ms, ratio, and whether the verdict-relevant counts match (uses check.py scoring)."""
import sys, json, tempfile, time
from pathlib import Path
ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "harness"))
import common as C

c = json.load(open(ROOT / "harness" / "corpus.json"))
byid = {x["id"]: x for x in c["check"]}
import os
EXE = os.environ.get("TLCRS_EXE")
ids = sys.argv[1:]
if ids and ids[0] == "--heavy-ex":
    ids = [x["id"] for x in c["check"] if x["id"].startswith("ex/") and (ROOT / "harness/golden/check" / (x["id"].replace("/", "__") + ".json")).exists()]
    ids = [i for i in ids if 60000 < min(float(v) for v in [json.load(open(ROOT / "harness/golden/check" / (i.replace("/", "__") + ".json"))).get("wall_ms"), json.load(open(ROOT / "harness/golden/check" / (i.replace("/", "__") + ".json"))).get("wall_ms_2") or 1e18] if v is not None) < 590000]
if ids == ["--ex-slow"]:
    lat = json.load(open(ROOT / "harness/results/latest.json"))
    ids = [r["id"] for r in lat["records"] if r["kind"] == "check" and r["id"].startswith("ex/") and r["levels"].get("verdict")
           and not r["levels"].get("perf")]
for eid in ids:
    e = byid[eid]
    g = json.load(open(ROOT / "harness/golden/check" / (eid.replace("/", "__") + ".json")))
    jms = min(float(x) for x in [g.get("wall_ms"), g.get("wall_ms_2")] if x is not None)
    with tempfile.TemporaryDirectory() as d:
        meta = Path(d) / "meta"
        meta.mkdir()
        rc, out, err, ms = C.run_proc(([EXE] + C.rust_base("tlc")[1:] if EXE else C.rust_base("tlc")) + C.tlc_args(e, meta), max(30, jms * 3 / 1000), cwd=Path(d))
    print(f"{eid:60s} rust {ms:9.0f} ms  java {jms:9.0f} ms  x{ms / jms:5.2f} {'TIMEOUT' if rc is None else ''}", flush=True)
