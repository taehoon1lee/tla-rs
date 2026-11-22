"""Preflight / bootstrap: reference sources (git submodules, pinned), the Java jars, the TLA+ library dir, toolchains.

reference/{tlaplus,examples,community-modules,tlapm,apalache} are git submodules (shallow). Their gitlinks must
equal common.PINS: the goldens were generated from exactly these commits. tlapm and apalache are sparse-checked-out
(only library/ and src/tla/ are used). reference/bin and reference/tla-library are generated here (gitignored).

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


def gitlink(name) -> str:
    """Commit the superproject's HEAD records for submodule reference/<name>."""
    r = subprocess.run(["git", "-C", str(ROOT), "rev-parse", f"HEAD:reference/{name}"], capture_output=True, text=True)
    return r.stdout.strip()


def submodule_ok(name) -> bool:
    sha = PINS[name][1]
    if gitlink(name) != sha:
        return False  # never fixed automatically: bumping a reference invalidates the goldens
    d = REFERENCE / name
    if git_head(d) != sha:
        return False
    if name in SPARSE:
        r = subprocess.run(["git", "-C", str(d), "sparse-checkout", "list"], capture_output=True, text=True)
        return r.stdout.split() == [SPARSE[name]]
    return True


def update_submodule(name):
    if gitlink(name) != PINS[name][1]:
        print(f"       gitlink of reference/{name} is {gitlink(name)[:10]}, expected {PINS[name][1][:10]} "
              "(goldens were generated from the pinned commit; restore it with git checkout/restore)")
        return
    run(["git", "submodule", "update", "--init", "--depth", "1", "--", f"reference/{name}"])
    if name in SPARSE:
        run(["git", "-C", str(REFERENCE / name), "sparse-checkout", "set", SPARSE[name]])


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
    step(f"reference/{name} (submodule) @ {PINS[name][1][:10]}", lambda n=name: submodule_ok(n),
         lambda n=name: update_submodule(n))
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
