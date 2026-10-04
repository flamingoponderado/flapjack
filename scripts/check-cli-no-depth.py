#!/usr/bin/env python3
"""Bounded CLI timing regression for a DAG with exponentially many call paths.

The original Pancake command is cake --pancake --target=riscv. The checked-in
manifest contains SHA256 hashes of its complete stdout (no normalization).
Use --cake to additionally compare against the original executable live.
The depth-26/30 programs call the next function twice in non-tail position;
the old unused-bound route takes about 26 seconds / seven minutes respectively.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parent.parent
MANIFEST = Path(__file__).with_name("cli-no-depth.json")


def source(depth):
    lines = ["fun 1 main() { return f0(1); }"]
    for n in range(depth):
        lines.append(f"fun 1 f{n}(1 a) {{ var 1 x = f{n+1}(a); "
                     f"var 1 y = f{n+1}(x); return x + y; }}")
    lines.append(f"fun 1 f{depth}(1 a) {{ return a; }}")
    return "\n".join(lines) + "\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--flapjack", default=str(ROOT / ".lake/build/bin/flapjack-compile"))
    parser.add_argument("--cake", help="original executable for a live exact comparison")
    parser.add_argument("--timeout", type=float, default=10,
                        help="per-case bound in seconds (default 10; old depth26 takes 26s)")
    args = parser.parse_args()
    if args.timeout <= 0:
        parser.error("timeout must be positive")
    manifest = json.loads(MANIFEST.read_text())
    with tempfile.TemporaryDirectory(prefix="flapjack-no-depth-") as directory:
        for case in manifest["cases"]:
            program = source(case["depth"]).encode()
            assert hashlib.sha256(program).hexdigest() == case["source_sha256"]
            path = Path(directory) / f"depth{case['depth']}.pnk"
            path.write_bytes(program)
            start = time.monotonic()
            try:
                result = subprocess.run([args.flapjack, "--assembly", str(path)],
                                        capture_output=True, timeout=args.timeout, check=True)
            except (subprocess.TimeoutExpired, subprocess.CalledProcessError) as error:
                raise SystemExit(f"FAIL depth{case['depth']}: {error}") from error
            elapsed = time.monotonic() - start
            digest = hashlib.sha256(result.stdout).hexdigest()
            if digest != case["cake_stdout_sha256"] or len(result.stdout) != case["cake_stdout_bytes"]:
                raise SystemExit(f"FAIL depth{case['depth']}: original stdout mismatch ({digest})")
            if args.cake:
                original = subprocess.run([args.cake, "--pancake", "--target=riscv"],
                                          input=program, capture_output=True,
                                          timeout=args.timeout, check=True)
                if result.stdout != original.stdout:
                    raise SystemExit(f"FAIL depth{case['depth']}: live original stdout mismatch")
            print(f"depth{case['depth']}: {elapsed:.3f}s, complete stdout exact ({len(result.stdout)} bytes)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
