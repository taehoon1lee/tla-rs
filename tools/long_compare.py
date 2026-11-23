"""Long-running Java-vs-Rust comparison for models whose golden is missing because Java timed out (600 s).
Nothing under harness/ is written: results go to tmp/long/.  The harness' own scoring (`check.score_check`) is reused read-only.

usage:
  python tools/long_compare.py java    [--timeout 1200] [--jobs 2] <check-id>...     # Java TLC with the harness command line
  python tools/long_compare.py rust    [--timeout 1200] [--mem-gb 10] <check-id>...  # tlc-rs (release) with the harness arguments
  python tools/long_compare.py compare <check-id>...                                 # harness scoring of rust vs java
"""
import sys, json, time, ctypes, subprocess, tempfile, argparse, concurrent.futures as cf
from ctypes import wintypes
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "harness"))
import common as C            # noqa: E402  (read-only use)
import tlcout                 # noqa: E402
import check as K             # noqa: E402

OUT = ROOT / "tmp" / "long"


class PMC(ctypes.Structure):
    _fields_ = [("cb", wintypes.DWORD), ("PageFaultCount", wintypes.DWORD), ("PeakWorkingSetSize", ctypes.c_size_t),
                ("WorkingSetSize", ctypes.c_size_t), ("QuotaPeakPagedPoolUsage", ctypes.c_size_t),
                ("QuotaPagedPoolUsage", ctypes.c_size_t), ("QuotaPeakNonPagedPoolUsage", ctypes.c_size_t),
                ("QuotaNonPagedPoolUsage", ctypes.c_size_t), ("PagefileUsage", ctypes.c_size_t),
                ("PeakPagefileUsage", ctypes.c_size_t)]


def peak_ws_mb(proc):
    pm = PMC()
    pm.cb = ctypes.sizeof(PMC)
    if ctypes.windll.psapi.GetProcessMemoryInfo(int(proc._handle), ctypes.byref(pm), pm.cb):
        return pm.PeakWorkingSetSize / 1048576.0
    return 0.0


def cpu_ms(proc):
    class FT(ctypes.Structure):
        _fields_ = [("lo", wintypes.DWORD), ("hi", wintypes.DWORD)]
    c, e, k, u = FT(), FT(), FT(), FT()
    ctypes.windll.kernel32.GetProcessTimes(int(proc._handle), ctypes.byref(c), ctypes.byref(e), ctypes.byref(k), ctypes.byref(u))
    f = lambda x: ((x.hi << 32) | x.lo) / 10_000.0
    return f(k) + f(u)


def entry(eid):
    c = json.load(open(ROOT / "harness" / "corpus.json"))
    return [x for x in c["check"] if x["id"] == eid][0]


def run(cmd, cwd, timeout_s, mem_limit_mb=None):
    out_f = tempfile.TemporaryFile()
    err_f = tempfile.TemporaryFile()
    t0 = time.perf_counter()
    p = subprocess.Popen(cmd, cwd=str(cwd), stdout=out_f, stderr=err_f, stdin=subprocess.DEVNULL)
    status, peak = "ok", 0.0
    while p.poll() is None:
        time.sleep(1.0)
        peak = max(peak, peak_ws_mb(p))
        if time.perf_counter() - t0 > timeout_s:
            status = "timeout"
            p.kill()
            break
        if mem_limit_mb and peak > mem_limit_mb:
            status = "memory"
            p.kill()
            break
    p.wait()
    ms = (time.perf_counter() - t0) * 1000
    cpu = cpu_ms(p)
    out_f.seek(0)
    err_f.seek(0)
    out = out_f.read().decode("utf-8", "replace")
    err = err_f.read().decode("utf-8", "replace")
    return status, p.returncode, out, err, ms, cpu, peak


def one(kind, eid, timeout_s, mem_gb):
    e = entry(eid)
    OUT.mkdir(parents=True, exist_ok=True)
    fn = OUT / f"{kind}__{eid.replace('/', '__')}.json"
    with C.Scratch(eid) as s:
        base = C.java_base("tlc2.TLC") if kind == "java" else C.rust_base("tlc")
        status, rc, out, err, ms, cpu, peak = run(base + C.tlc_args(e, s.meta), s.dir, timeout_s, mem_gb * 1024 if mem_gb else None)
    doc = {"id": eid, "tool": kind, "status": status, "wall_ms": round(ms, 1), "cpu_ms": round(cpu, 1), "peak_ws_mb": round(peak),
           "timeout_s": timeout_s}
    if status == "ok":
        p = tlcout.parse_tlc(out, rc)
        doc["parsed"] = p
        doc["ok"] = bool(p["messages"])
        if not p["messages"]:
            doc["stderr_tail"] = (err or out)[-1500:]
    else:
        doc["stdout_tail"] = out[-600:]
    fn.write_text(json.dumps(doc, indent=1))
    print(f"[{kind}] {eid}: {status} wall {ms/1000:.1f}s cpu {cpu/1000:.1f}s peak {peak:.0f} MB"
          + (f" exit {doc['parsed']['exit_code']} generated {doc['parsed']['generated']} distinct {doc['parsed']['distinct']}" if "parsed" in doc else ""),
          flush=True)
    return doc


def compare(eid):
    e = entry(eid)
    jf = OUT / f"java__{eid.replace('/', '__')}.json"
    rf = OUT / f"rust__{eid.replace('/', '__')}.json"
    if not jf.exists() or not rf.exists():
        print(f"{eid}: missing result file(s)")
        return
    j, r = json.load(open(jf)), json.load(open(rf))
    if j["status"] != "ok":
        print(f"{eid}: Java {j['status']} after {j['wall_ms']/1000:.0f}s -> no reference result")
        return
    g = {"parsed": j["parsed"], "wall_ms": j["wall_ms"]}
    rr = {"status": "ok" if r["status"] == "ok" and r.get("ok") else r["status"], "ms": r["wall_ms"], "parsed": r.get("parsed"),
          "stderr": r.get("stderr_tail", ""), "stdout_tail": r.get("stdout_tail", "")}
    rec = K.score_check(e, g, rr)
    lv = rec["levels"]
    print(f"{eid}: java {rec['java']} {j['wall_ms']/1000:.1f}s | rust {rec['rust']} {r['wall_ms']/1000:.1f}s (x{rec.get('ratio')})  "
          f"levels " + " ".join(f"{k}={'Y' if v else 'n'}" for k, v in lv.items()) + (f"\n    why: {rec['why']}" if rec.get("why") else ""))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("what", choices=["java", "rust", "compare"])
    ap.add_argument("--timeout", type=float, default=1200.0)
    ap.add_argument("--jobs", type=int, default=2)
    ap.add_argument("--mem-gb", type=float, default=10.0)
    ap.add_argument("ids", nargs="+")
    a = ap.parse_args()
    if a.what == "compare":
        for i in a.ids:
            compare(i)
    elif a.what == "java":
        with cf.ThreadPoolExecutor(max_workers=a.jobs) as ex:
            list(ex.map(lambda i: one("java", i, a.timeout, None), a.ids))
    else:
        for i in a.ids:
            one("rust", i, a.timeout, a.mem_gb)


main()
