"""Check the frozen sources and reproduce the characteristic-zero proofs."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "src"
LOCK = "7619243bb824c928b94de0be435df73bdd1cd6213e8c32151f3e0a1666bbff80"
REPORTS = {
    "FullG3": "G3Assembly.complex_three_matrices",
    "CharZeroMatrices": "G3Scalar.charZero_three_matrices",
    "StatementContract": "all_complex_matrices_contract",
}
AXIOMS = "[propext, Classical.choice, Quot.sound]"
VERSION = "4.36.0-rc2"
COMMIT = "b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a"

def checksum(file):
    return hashlib.sha256(file.read_bytes()).hexdigest()

def checked_plan():
    if checksum(ROOT / "lake-manifest.json") != LOCK:
        raise SystemExit("The upstream dependency lock has changed.")
    if (ROOT / "lean-toolchain").read_text().strip() != "leanprover/lean4:v" + VERSION:
        raise SystemExit("Unexpected Lean toolchain.")
    rows = (ROOT / "verification" / "modules.tsv").read_text().splitlines()
    modules = {}
    for row in rows:
        name, digest = row.split("\t")
        src = SOURCE / (name.replace(".", "/") + ".lean")
        if name in modules or checksum(src) != digest:
            raise SystemExit(f"Invalid module entry: {name}")
        modules[name] = src
    if set(modules.values()) != set(SOURCE.rglob("*.lean")) or len(modules) != 138:
        raise SystemExit("Source file set differs from the frozen proof.")
    imports = set()
    earlier = set()
    for name, src in modules.items():
        lines = src.read_text(encoding="utf-8").splitlines()
        for line in lines:
            m = re.match(r"^(?:public )?import\s+([\w.]+)", line)
            if m:
                dep = m.group(1)
                if dep in modules and dep not in earlier:
                    raise SystemExit(f"{name} imports {dep} out of order.")
                if dep.startswith("Mathlib."):
                    imports.add(dep)
        earlier.add(name)
    contract = ROOT / "verification" / "StatementContract.lean"
    expected = (ROOT / "verification" / "contract.sha256").read_text().split()[0]
    if checksum(contract) != expected:
        raise SystemExit("The export client has changed.")
    return modules, sorted(imports)

def compile_file(lean, env, directory, source, target, name):
    target.parent.mkdir(parents=True, exist_ok=True)
    result = subprocess.run([lean, "-o", str(target), str(source.relative_to(directory))],
                            cwd=directory, env=env, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, encoding="utf-8", errors="replace")
    if result.returncode or re.search(r"sorryAx|Lean\.ofReduceBool|Lean\.trustCompiler|error:", result.stdout):
        raise SystemExit(f"{name} failed.\n{result.stdout}")
    if name in REPORTS:
        expected = f"'{REPORTS[name]}' depends on axioms: {AXIOMS}"
        if expected not in result.stdout.splitlines():
            raise SystemExit(f"{name}: missing expected axiom report.\n{result.stdout}")
        print(expected, flush=True)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--sources-only", action="store_true")
    mode.add_argument("--fetch-cache", action="store_true")
    args = parser.parse_args()
    modules, imports = checked_plan()
    print(f"Verified {len(modules)} source hashes, the client and the dependency lock.", flush=True)
    if args.sources_only:
        return
    if args.fetch_cache:
        subprocess.run(["lake", "exe", "cache", "get", *imports], cwd=ROOT, check=True)
        return
    lean = shutil.which("lean")
    if not lean:
        raise SystemExit("Run lake env python3 scripts/replay.py from the repository root.")
    version = subprocess.check_output([lean, "--version"], text=True)
    if VERSION not in version or COMMIT[:12] not in version:
        raise SystemExit(f"Unexpected Lean executable: {version}")
    packages = ROOT / ".lake" / "packages"
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    upstream = []
    for package in manifest["packages"]:
        directory = packages / package["name"]
        rev = subprocess.check_output(["git", "-C", str(directory), "rev-parse", "HEAD"], text=True).strip()
        if rev != package["rev"]:
            raise SystemExit(f"Revision mismatch for {package['name']}")
        lib = directory / ".lake" / "build" / "lib" / "lean"
        if lib.is_dir():
            upstream.append(str(lib))
    with tempfile.TemporaryDirectory(prefix="g3-olean-") as scratch:
        out = Path(scratch)
        env = dict(os.environ, LEAN_PATH=os.pathsep.join([scratch, *upstream]))
        for index, (name, src) in enumerate(modules.items(), start=1):
            print(f"[{index}/{len(modules)}] {name}", flush=True)
            target = out / src.relative_to(SOURCE).with_suffix(".olean")
            compile_file(lean, env, SOURCE, src, target, name)
        contract = ROOT / "verification" / "StatementContract.lean"
        compile_file(lean, env, contract.parent, contract, out / "StatementContract.olean", "StatementContract")
    print("Both endpoints and the complex export client passed.", flush=True)

if __name__ == "__main__":
    main()
