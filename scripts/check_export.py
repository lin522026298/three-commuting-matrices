"""Replay the archived complex theorem with the Rust checker in the Lean distribution."""
import argparse
import gzip
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
EXPECTED = "f95f7999e437cc943f0fc2a27828089f8eb800fcb3e720d0923e7a42f19a6319"

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("proof", type=Path)
    parser.add_argument("--checker", default="nanoda_bin")
    args = parser.parse_args()
    with args.proof.open("rb") as stream:
        digest = hashlib.file_digest(stream, "sha256").hexdigest()
    if digest != EXPECTED:
        raise SystemExit(f"Compressed proof checksum mismatch: {digest}")
    checker = shutil.which(args.checker)
    if not checker:
        raise SystemExit("Pass --checker with the path to nanoda_bin from the pinned Lean distribution.")
    checker = str(Path(checker).resolve())
    with tempfile.TemporaryDirectory() as scratch:
        output = Path(scratch) / "nanoda_type.txt"
        output.touch()
        config = ROOT / "verification" / "nanoda.json"
        with gzip.open(args.proof, "rb") as raw:
            with subprocess.Popen([checker, str(config)], cwd=scratch, stdin=subprocess.PIPE) as child:
                try:
                    with child.stdin:
                        shutil.copyfileobj(raw, child.stdin, length=1024 * 1024)
                except BrokenPipeError:
                    pass
                if child.wait() != 0:
                    raise SystemExit("nanoda rejected the proof or failed to finish.")
        types = output.read_text(encoding="utf-8")
        if types != (ROOT / "verification" / "recorded-nanoda_type.txt").read_text(encoding="utf-8"):
            raise SystemExit("The checker printed different theorem types from the recorded replay.")
    print(json.dumps({"proof_sha256": digest, "printed_types_match": True, "exit_code": 0}))

if __name__ == "__main__":
    main()
