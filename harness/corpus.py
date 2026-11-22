"""Build harness/corpus.json: what the judge compares.

  parse : every .tla module of the corpora, checked with SANY (`tla2sany.SANY -error-codes FILE`)
  check : (spec, cfg, flags) model-checking runs with TLC (`tlc2.TLC -tool ...`)

Sources
  ex/  reference/examples/specifications   (github.com/tlaplus/Examples) - models from each manifest.json with
       mode "exhaustive search" and recorded runtime <= MAX_RUNTIME (CI used 4 workers; we use 1)
  tt/  reference/tlaplus/tlatools/org.lamport.tlatools/test-model - TLC's own JUnit models: spec/config/flags are
       extracted from the ModelCheckerTestCase subclasses under test/ (only tests with harmless flags)
  cm/  reference/community-modules/modules (parse only)

Usage: python harness/corpus.py      (run once by the environment builder; the loop must not edit corpus.json)
"""
import json
import re
from pathlib import Path

from common import COMMUNITY_MODULES_DIR, CORPUS_FILE, REFERENCE, ROOT, TLATOOLS, rel

EXAMPLES = REFERENCE / "examples"
TEST_MODEL = TLATOOLS / "test-model"
TEST_SRC = TLATOOLS / "test"
MAX_RUNTIME_S = 300

# flags a TLC JUnit test may pass for us to keep it: name -> number of values that follow
ALLOWED_FLAGS = {"-config": 1, "-deadlock": 0, "-nowarning": 0, "-continue": 0, "-view": 0, "-maxSetSize": 1, "-inv": 1}
# JUnit hooks that change JVM-global state or TLC internals we do not reproduce -> skip the test
SKIP_HOOKS = ("beforeSetUp", "getResolver", "getLivenessThreshold", "noRandomFPandSeed", "doCheckpoint")
STR = re.compile(r'"((?:[^"\\]|\\.)*)"')


def lines_of(p: Path) -> int:
    return p.read_text(encoding="utf-8", errors="replace").count("\n") + 1


def secs(s: str) -> int:
    if s == "unknown":
        return 10 ** 9
    h, m, x = map(int, s.split(":"))
    return h * 3600 + m * 60 + x


def parse_entries():
    out = []
    for tag, base in (("ex", EXAMPLES / "specifications"), ("tt", TEST_MODEL), ("cm", COMMUNITY_MODULES_DIR)):
        for p in sorted(base.rglob("*.tla")):
            relp = p.relative_to(base).with_suffix("").as_posix()
            out.append({"id": f"{tag}/{relp}", "path": rel(p), "lines": lines_of(p)})
    return out


def example_checks():
    out = []
    for mf in sorted((EXAMPLES / "specifications").glob("*/manifest.json")):
        spec = json.loads(mf.read_text(encoding="utf-8"))
        for mod in spec["modules"]:
            for m in mod["models"]:
                if m["mode"] != "exhaustive search" or "action composition" in mod["features"]:
                    continue
                if secs(m["runtime"]) > MAX_RUNTIME_S:
                    continue
                tla, cfg = EXAMPLES / mod["path"], EXAMPLES / m["path"]
                if not tla.exists() or not cfg.exists():
                    continue
                cid = "ex/" + cfg.relative_to(EXAMPLES / "specifications").with_suffix("").as_posix()
                out.append({"id": cid, "spec": rel(tla), "config": rel(cfg), "extra_args": [], "no_deadlock": False,
                            "lines": lines_of(tla), "features": mod["features"],
                            "manifest": {k: m[k] for k in ("runtime", "result", "distinctStates", "totalStates",
                                                           "stateDepth") if k in m}})
    return out


def junit_checks():
    out, seen = [], set()
    for f in sorted(TEST_SRC.rglob("*Test.java")):
        t = f.read_text(encoding="utf-8", errors="replace")
        m = re.search(r"class\s+(\w+)\s+extends\s+(\w+)", t)
        if not m or m.group(2) != "ModelCheckerTestCase" or "abstract class" in t:
            continue
        cls = m.group(1)
        if any(re.search(r"protected\s+\w+\s+" + h + r"\s*\(", t) for h in SKIP_HOOKS):
            continue
        sm = re.search(r"super\s*\((.*?)\)\s*;", t, re.S)
        if not sm:
            continue
        body = sm.group(1)
        am = re.search(r"new\s+String\s*\[\s*\]\s*\{(.*?)\}", body, re.S)
        arr = STR.findall(am.group(1)) if am else []
        if am and re.search(r"[A-Za-z_]\w*\s*[,}]", re.sub(STR, "", am.group(1))):
            continue  # array contains non-literal expressions
        rest = body[:am.start()] + body[am.end():] if am else body
        lits = STR.findall(rest)
        if not lits:
            continue
        spec_name, path = lits[0], (lits[1] if len(lits) > 1 else "")
        if re.search(r"\+|BASE_DIR|File\.separator", rest):
            continue  # computed spec/path expressions
        # flags
        extra, cfg_name, ok, i = [], None, True, 0
        while i < len(arr):
            a = arr[i]
            if a not in ALLOWED_FLAGS:
                ok = False
                break
            n = ALLOWED_FLAGS[a]
            vals = arr[i + 1:i + 1 + n]
            if len(vals) != n:
                ok = False
                break
            if a == "-config":
                cfg_name = vals[0]
            else:
                extra += [a] + vals
            i += 1 + n
        if not ok:
            continue
        d = TEST_MODEL / path
        tla = d / (spec_name if spec_name.endswith(".tla") else spec_name + ".tla")
        cfgn = cfg_name or tla.stem
        cfg = d / (cfgn if cfgn.endswith(".cfg") else cfgn + ".cfg")
        if not tla.exists() or not cfg.exists():
            continue
        dl = re.search(r"boolean\s+checkDeadLock\s*\(\s*\)\s*\{\s*return\s+true\s*;", t)
        key = (rel(tla), rel(cfg), tuple(extra), not dl)
        if key in seen:
            continue
        seen.add(key)
        out.append({"id": f"tt/{cls}", "spec": rel(tla), "config": rel(cfg), "extra_args": extra,
                    "no_deadlock": not dl, "lines": lines_of(tla), "features": [],
                    "junit": rel(f)})
    return out


def main():
    parse = parse_entries()
    check = example_checks() + junit_checks()
    ids = [e["id"] for e in check]
    assert len(ids) == len(set(ids)), "duplicate check ids"
    CORPUS_FILE.write_text(json.dumps({"parse": parse, "check": check}, indent=1), encoding="utf-8")
    print(f"parse: {len(parse)} modules; check: {len(check)} models "
          f"({sum(e['id'].startswith('ex/') for e in check)} ex, {sum(e['id'].startswith('tt/') for e in check)} tt)"
          f" -> {CORPUS_FILE.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
