#!/usr/bin/env python3
"""Check or regenerate the ARMv8 source-to-assembly parity fixtures.

For every `scripts/arm8/parity/<case>.pnk`, runs the original CakeML Pancake
compiler with `--target=arm8` and compares stdout with the checked-in
`<case>.cake.S`.  `--regenerate` rewrites the `.cake.S` files and derives the
`.cake.hex` files from their `.byte` payload.  `lake test` checks the Lean
driver against the same checked-in fixtures without needing CakeML.
"""

import argparse
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
PARITY = ROOT / "scripts" / "arm8" / "parity"


def payload(assembly: str) -> str:
    data: list[str] = []
    for line in assembly.splitlines():
        if line.strip().startswith(".byte"):
            data.extend(re.findall(r"0x([0-9A-Fa-f]{2})", line))
    return " ".join(byte.lower() for byte in data) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cake", default=str(ROOT / "cakeml/developers/bin/cake"),
                        help="original CakeML compiler executable")
    parser.add_argument("--regenerate", action="store_true",
                        help="rewrite .cake.S and .cake.hex from the original compiler")
    args = parser.parse_args()

    cases = sorted(PARITY.glob("*.pnk"))
    if not cases:
        print("no parity cases found", file=sys.stderr)
        return 1
    failures = 0
    for source in cases:
        name = source.stem
        result = subprocess.run(
            [args.cake, "--pancake", "--target=arm8"],
            input=source.read_text(), capture_output=True, text=True)
        if result.returncode != 0:
            print(f"FAIL {name}: cake exited {result.returncode}: {result.stderr.strip()}",
                  file=sys.stderr)
            failures += 1
            continue
        golden = PARITY / f"{name}.cake.S"
        if args.regenerate:
            golden.write_text(result.stdout)
            (PARITY / f"{name}.cake.hex").write_text(payload(result.stdout))
            print(f"WRITE {name}")
        elif golden.read_text() != result.stdout:
            print(f"FAIL {name}: output differs from {golden.relative_to(ROOT)}",
                  file=sys.stderr)
            failures += 1
        elif payload(result.stdout) != (PARITY / f"{name}.cake.hex").read_text():
            print(f"FAIL {name}: .cake.hex disagrees with .cake.S", file=sys.stderr)
            failures += 1
        else:
            print(f"PASS {name}")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
