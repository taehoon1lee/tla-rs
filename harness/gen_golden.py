"""Generate golden (expected) outputs by running the official Java TLC 1.8.0 on every corpus entry.

Run ONCE by the environment builder. The loop must NOT regenerate or edit goldens.

Usage:
  python harness/gen_golden.py --kind parse -j 8          # SANY on every module  -> harness/golden/parse/
  python harness/gen_golden.py --kind check -j 3          # TLC on every model     -> harness/golden/check/
Options: --filter SUBSTR, --force, --timeout-s S, --no-repeat (skip the determinism re-run)

Determinism: every check model that finished in < REPEAT_LIMIT_MS is run a second time. Fields that differ are
listed in `nondet` (the judge ignores them); if a verdict field differs the entry is marked unscored.
"""
import argparse
import json
import time
from concurrent.futures import ThreadPoolExecutor

from common import (GOLDEN_CHECK, GOLDEN_PARSE, Scratch, eprint, golden_name, java_base, load_corpus, run_proc,
                    sany_args, sany_cwd, tlc_args)
from tlcout import BFS_TRACE_EXITS, parse_sany, parse_tlc

REPEAT_LIMIT_MS = 60000


def verdict_key(p: dict):
    k = [p["exit_code"], p["first_error"], p["violation"], p["init_distinct"], p["reached_init"]]
    if p["exit_code"] == 0:
        k += [p["generated"], p["distinct"], p["depth"]]
    if p["exit_code"] in BFS_TRACE_EXITS:
        k.append(len(p["trace"]))
    return k


def run_check(e, timeout_s):
    with Scratch(e["id"]) as s:
        rc, out, err, ms = run_proc(java_base("tlc2.TLC") + tlc_args(e, s.meta), timeout_s, cwd=s.dir)
    doc = {"schema": 1, "tool": "java-tlc-1.8.0", "id": e["id"], "wall_ms": round(ms, 1)}
    if rc is None:
        doc.update(status="timeout", timeout_s=timeout_s)
        return doc
    p = parse_tlc(out, rc)
    doc.update(status="ok" if p["messages"] else "crash", parsed=p)
    if not p["messages"]:
        doc["stderr_tail"] = (err or out)[-1500:]
    return doc


def run_parse(e, timeout_s):
    rc, out, err, ms = run_proc(java_base("tla2sany.SANY") + sany_args(e), timeout_s, cwd=sany_cwd(e))
    doc = {"schema": 1, "tool": "java-sany-1.8.0", "id": e["id"], "wall_ms": round(ms, 1)}
    if rc is None:
        doc.update(status="timeout")
        return doc
    doc.update(status="ok", parsed=parse_sany(out, rc))
    rc, out, err, ms = run_proc(java_base("tla2sany.SANY") + sany_args(e, syntax_only=True), timeout_s, cwd=sany_cwd(e))
    if rc is None:
        doc.update(status="timeout")
        return doc
    doc["syntax"] = parse_sany(out, rc)
    return doc


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--kind", choices=["parse", "check"], required=True)
    ap.add_argument("-j", type=int, default=1)
    ap.add_argument("--timeout-s", type=float, default=None)
    ap.add_argument("--filter", default=None)
    ap.add_argument("--force", action="store_true")
    ap.add_argument("--no-repeat", action="store_true")
    a = ap.parse_args()

    corpus = load_corpus()[a.kind]
    outdir = GOLDEN_PARSE if a.kind == "parse" else GOLDEN_CHECK
    outdir.mkdir(parents=True, exist_ok=True)
    timeout = a.timeout_s or (120 if a.kind == "parse" else 600)
    todo = [e for e in corpus if (not a.filter or a.filter in e["id"])
            and (a.force or not (outdir / golden_name(e["id"])).exists())]
    todo.sort(key=lambda e: e["lines"])
    eprint(f"{len(todo)}/{len(corpus)} {a.kind} entries to run, timeout={timeout}s, jobs={a.j}")
    t0 = time.time()

    def job(e):
        if a.kind == "parse":
            doc = run_parse(e, timeout)
            info = (doc.get("parsed") or {}).get("status", doc["status"])
        else:
            doc = run_check(e, timeout)
            p = doc.get("parsed")
            if p and not a.no_repeat and doc["wall_ms"] < REPEAT_LIMIT_MS:
                d2 = run_check(e, timeout)
                q = d2.get("parsed")
                if not q:
                    doc["unscored"] = "nondeterministic: second run " + d2["status"]
                else:
                    doc["nondet"] = sorted(k for k in p if k not in ("messages",) and p[k] != q[k])
                    if verdict_key(p) != verdict_key(q):
                        doc["unscored"] = "nondeterministic verdict"
                    doc["wall_ms_2"] = d2["wall_ms"]
            info = f"{doc['status']} " + (f"exit={p['exit_code']} first={p['first_error']} distinct={p['distinct']}"
                                          if p else "") + (f" UNSCORED({doc['unscored']})" if doc.get("unscored") else "")
        (outdir / golden_name(e["id"])).write_text(json.dumps(doc, indent=1), encoding="utf-8")
        eprint(f"[{time.time() - t0:7.1f}s] {e['id']}: {info} ({doc['wall_ms'] / 1000:.1f}s)")

    with ThreadPoolExecutor(max_workers=a.j) as ex:
        list(ex.map(job, todo))
    eprint(f"done in {time.time() - t0:.1f}s")


if __name__ == "__main__":
    main()
