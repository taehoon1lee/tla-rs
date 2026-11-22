"""Ad-hoc experiments: run Java TLC/SANY and/or tlc-rs on ANY spec with exactly the harness flags.

Use it on reduced specs you write under tmp/ (never under reference/ or harness/).

  python harness/oracle.py tlc  tmp/x/Spec.tla [--config tmp/x/Spec.cfg] [--no-deadlock] [--arg -continue ...]
  python harness/oracle.py sany tmp/x/Spec.tla
Modes (default --java):
  --java     run Java only            --rust     run tlc-rs only (target/release/tlc-rs.exe, not rebuilt)
  --diff     run both, print the normalized fields that differ (what check.py would compare)
  --raw      print raw stdout instead of the normalized JSON
Writing goldens from here is forbidden; this tool never touches harness/golden.
"""
import argparse
import json
import sys
from pathlib import Path

from common import ROOT, Scratch, java_base, run_proc, rust_base, sany_args, sany_cwd, tlc_args
from tlcout import parse_sany, parse_tlc


def entry_for(a):
    spec = Path(a.file).resolve()
    e = {"id": "adhoc/" + spec.stem, "path": spec.relative_to(ROOT).as_posix(), "spec": spec.relative_to(ROOT).as_posix(),
         "extra_args": list(a.arg or []), "no_deadlock": a.no_deadlock}
    if a.config:
        e["config"] = Path(a.config).resolve().relative_to(ROOT).as_posix()
    elif spec.with_suffix(".cfg").exists():
        e["config"] = spec.with_suffix(".cfg").relative_to(ROOT).as_posix()
    return e


def run(tool, kind, e, timeout):
    if kind == "sany":
        base = java_base("tla2sany.SANY") if tool == "java" else rust_base("sany")
        rc, out, err, ms = run_proc(base + sany_args(e), timeout, cwd=sany_cwd(e))
        return rc, out, err, ms, (parse_sany(out, rc) if rc is not None else None)
    base = java_base("tlc2.TLC") if tool == "java" else rust_base("tlc")
    with Scratch(e["id"]) as s:
        rc, out, err, ms = run_proc(base + tlc_args(e, s.meta), timeout, cwd=s.dir)
    return rc, out, err, ms, (parse_tlc(out, rc) if rc is not None else None)


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("kind", choices=["tlc", "sany"])
    ap.add_argument("file")
    ap.add_argument("--config")
    ap.add_argument("--no-deadlock", action="store_true", help="pass -deadlock (disables deadlock checking)")
    ap.add_argument("--arg", action="append", help="extra TLC flag (repeatable), e.g. --arg -continue")
    g = ap.add_mutually_exclusive_group()
    g.add_argument("--java", action="store_true")
    g.add_argument("--rust", action="store_true")
    g.add_argument("--diff", action="store_true")
    ap.add_argument("--raw", action="store_true")
    ap.add_argument("--timeout", type=float, default=300)
    a = ap.parse_args()
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")
    e = entry_for(a)
    tools = ["java", "rust"] if a.diff else (["rust"] if a.rust else ["java"])
    res = {t: run(t, a.kind, e, a.timeout) for t in tools}
    for t in tools:
        rc, out, err, ms, doc = res[t]
        print(f"===== {t}: exit={rc} {ms:.0f} ms")
        if a.raw or doc is None:
            print(out)
            if err.strip():
                print("--- stderr ---\n" + err[-3000:])
        elif not a.diff:
            print(json.dumps(doc, indent=1)[:20000])
    if a.diff:
        j, r = res["java"][4] or {}, res["rust"][4] or {}
        same = True
        for k in sorted(set(j) | set(r)):
            if j.get(k) != r.get(k) and k != "messages":
                same = False
                print(f"!= {k}\n   java: {json.dumps(j.get(k))[:600]}\n   rust: {json.dumps(r.get(k))[:600]}")
        print("IDENTICAL (normalized)" if same else "")


if __name__ == "__main__":
    main()
