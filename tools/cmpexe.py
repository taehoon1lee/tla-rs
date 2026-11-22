"""Time several tlc-rs executables on the same corpus models.  usage: python tools/cmpexe.py exe1,exe2 id1 id2 ..."""
import sys, json, tempfile
from pathlib import Path
ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "harness"))
import common as C
exes = sys.argv[1].split(",")
c = json.load(open(ROOT / "harness" / "corpus.json"))
byid = {x["id"]: x for x in c["check"]}
for eid in sys.argv[2:]:
    e = byid[eid]
    row = []
    for exe in exes:
        with tempfile.TemporaryDirectory() as d:
            meta = Path(d) / "meta"; meta.mkdir()
            cmd = [str(ROOT / exe)] + C.rust_base("tlc")[1:] + C.tlc_args(e, meta)
            rc, out, err, ms = C.run_proc(cmd, 600, cwd=Path(d))
        row.append(f"{ms:8.0f}ms")
    print(f"{eid:55s} " + "  ".join(row), flush=True)
