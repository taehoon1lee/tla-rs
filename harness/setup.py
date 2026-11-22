"""Preflight / bootstrap: reference sources (pinned commits), the Java jars, the TLA+ library dir, toolchains.

Usage: python harness/setup.py   (idempotent; the loop driver runs it before starting)
"""
import hashlib
import os
import shutil
import subprocess
import sys
from pathlib import Path

from common import (CORPUS_FILE, GOLDEN_CHECK, GOLDEN_PARSE, JAR_COMMUNITY, JAR_SHA256, JAR_TLA2TOOLS, PINS,
                    REFERENCE, ROOT, TLA_LIBRARY_DIR, ensure_java_home)

ok = True
SPARSE = {"tlapm": "library", "apalache": "src/tla"}


def step(msg, cond, fix=None):
    global ok
    if cond():
        print(f"[ok]   {msg}")
        return
    if fix:
        print(f"[fix]  {msg} ...")
        try:
            fix()
        except Exception as e:  # keep going, report below
            print(f"       {e}")
        if cond():
            print(f"[ok]   {msg}")
            return
    print(f"[FAIL] {msg}")
    ok = False


def run(cmd, cwd=ROOT):
    print("       $ " + " ".join(map(str, cmd)))
    subprocess.run(cmd, cwd=str(cwd), check=False)


def git_head(d: Path) -> str:
    r = subprocess.run(["git", "-C", str(d), "rev-parse", "HEAD"], capture_output=True, text=True)
    return r.stdout.strip()


def clone(name):
    url, sha = PINS[name]
    d = REFERENCE / name
    if not d.exists():
        if name in SPARSE:
            run(["git", "clone", "-q", "--filter=blob:none", "--sparse", "--no-checkout", url, str(d)])
            run(["git", "-C", str(d), "sparse-checkout", "set", SPARSE[name]])
        else:
            run(["git", "clone", "-q", "--filter=blob:none", "--no-checkout", url, str(d)])
    if git_head(d) != sha:
        run(["git", "-C", str(d), "fetch", "-q", "--depth", "1", "origin", sha])
        run(["git", "-C", str(d), "checkout", "-q", sha])


def sha256(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest() if p.exists() else ""


def fetch_jars():
    (REFERENCE / "bin").mkdir(parents=True, exist_ok=True)
    if sha256(JAR_TLA2TOOLS) != JAR_SHA256["tla2tools.jar"]:
        run(["gh", "release", "download", "v1.8.0", "-R", "tlaplus/tlaplus", "-p", "tla2tools.jar",
             "-D", str(JAR_TLA2TOOLS.parent), "--clobber"])
    if sha256(JAR_COMMUNITY) != JAR_SHA256["CommunityModules-deps.jar"]:
        run(["gh", "release", "download", "202611191749", "-R", "tlaplus/CommunityModules", "-p",
             "CommunityModules-deps.jar", "-D", str(JAR_COMMUNITY.parent), "--clobber"])


def library_files():
    """reference/tla-library = TLAPS library modules + Apalache's TLA+ modules (what CI puts on the classpath)."""
    files = sorted((REFERENCE / "tlapm" / "library").glob("*.tla"))
    files += [p for p in sorted((REFERENCE / "apalache" / "src" / "tla").glob("*.tla"))
              if p.name != "DummyForIntegrationTests.tla"]
    return files


def assemble_library():
    TLA_LIBRARY_DIR.mkdir(parents=True, exist_ok=True)
    for p in library_files():
        shutil.copyfile(p, TLA_LIBRARY_DIR / p.name)


def library_ok():
    fs = library_files()
    return bool(fs) and all((TLA_LIBRARY_DIR / p.name).exists() for p in fs)


REFERENCE.mkdir(exist_ok=True)
for name in PINS:
    step(f"reference/{name} @ {PINS[name][1][:10]}", lambda n=name: git_head(REFERENCE / n) == PINS[n][1],
         lambda n=name: clone(n))
step("reference/bin/tla2tools.jar (TLC 1.8.0) + CommunityModules-deps.jar",
     lambda: sha256(JAR_TLA2TOOLS) == JAR_SHA256["tla2tools.jar"]
     and sha256(JAR_COMMUNITY) == JAR_SHA256["CommunityModules-deps.jar"], fetch_jars)
step("reference/tla-library (tlapm library + apalache modules)", library_ok, assemble_library)
step("java on PATH", lambda: shutil.which("java") is not None)
step("TLC telemetry opt-out home (harness/.javahome)", lambda: (ensure_java_home() or True))
cargo = shutil.which("cargo") or (Path.home() / ".cargo" / "bin" / ("cargo.exe" if os.name == "nt" else "cargo"))
step("cargo (Rust toolchain)", lambda: Path(cargo).exists())
step("harness/corpus.json", lambda: CORPUS_FILE.exists(), lambda: run([sys.executable, "harness/corpus.py"]))
step("harness/golden/{parse,check}/*.json",
     lambda: any(GOLDEN_PARSE.glob("*.json")) and any(GOLDEN_CHECK.glob("*.json")))
step("git repository", lambda: (ROOT / ".git").exists())
sys.exit(0 if ok else 1)
