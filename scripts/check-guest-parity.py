#!/usr/bin/env python3
"""Check the pinned stateless Pancake guest against Flapjack.

The source is pinned by the workflow to a commit of the upstream guest
repository.  The expected stdout digest is the output of the authoritative
CakeML Pancake RISC-V compiler for that exact source.  This keeps the large
guest source and Cake executable out of CI while still checking the complete
Pancake-compatible artifact byte-for-byte.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys


MANIFEST = Path(__file__).with_name("guest-parity.json")


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(
        description="Check either pinned guest build against original Pancake output."
    )
    reference = json.loads(MANIFEST.read_text())
    parser.add_argument("source", type=Path)
    parser.add_argument("--variant", choices=reference["variants"], default="accelerated")
    parser.add_argument(
        "--flapjack",
        default=os.environ.get("FLAPJACK", ".lake/build/bin/flapjack-compile"),
        type=Path,
    )
    args = parser.parse_args(argv)

    expected = reference["variants"][args.variant]
    expected_source = expected["source_sha256"]
    expected_stdout = expected["cake_stdout_sha256"]
    source_bytes = args.source.read_bytes()
    source_digest = sha256(source_bytes)
    if source_digest != expected_source:
        print(
            f"guest source hash mismatch: expected {expected_source}, "
            f"got {source_digest}",
            file=sys.stderr,
        )
        return 1

    result = subprocess.run(
        [str(args.flapjack), "--assembly", str(args.source)],
        capture_output=True,
    )
    actual = sha256(result.stdout)
    if result.returncode != 0 or actual != expected_stdout:
        print(
            f"{args.variant} guest parity mismatch: returncode={result.returncode} "
            f"expected={expected_stdout} got={actual}",
            file=sys.stderr,
        )
        if result.stderr:
            sys.stderr.buffer.write(result.stderr)
        return 1

    print(
        f"{args.variant} guest exact Pancake parity "
        f"source={source_digest} stdout={actual}"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
