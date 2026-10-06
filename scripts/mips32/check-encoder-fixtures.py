#!/usr/bin/env python3
"""Check the MIPS32 encoder fixtures against LLVM's MIPS assembler.

Assembles scripts/mips32/encoder-fixtures.s with
`llvm-mc -triple=mipsel-linux-gnu -mcpu=mips32r2 -show-encoding` and compares each
instruction's bytes with the `expected` column of Flapjack/Test/Mips32Encoding.lean.
`lake test` checks the encoder against the same pinned bytes without needing LLVM.
"""

import argparse
import re
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / "scripts/mips32/encoder-fixtures.s"
TEST = ROOT / "Flapjack/Test/Mips32Encoding.lean"


def llvm_bytes(llvm_mc: str) -> list[list[int]]:
    lines = [
        line for line in SOURCE.read_text().splitlines()
        if line.strip() and not line.lstrip().startswith("#")
    ]
    out = subprocess.run(
        [llvm_mc, "-triple=mipsel-linux-gnu", "-mcpu=mips32r2", "-show-encoding",
         "-no-deprecated-warn", "--mips-compact-branches=never"],
        input=".set noreorder\n" + "\n".join(lines) + "\n",
        capture_output=True, text=True, check=True,
    ).stdout
    encodings = re.findall(r"encoding: \[([^\]]*)\]", out)
    result = [[int(b, 16) for b in e.split(",")] for e in encodings]
    if len(result) != len(lines):
        sys.exit(f"llvm-mc produced {len(result)} encodings for {len(lines)} lines")
    return result


def pinned_bytes() -> list[list[int]]:
    rows = re.findall(r"\[(0x[0-9a-f]+, 0x[0-9a-f]+, 0x[0-9a-f]+, 0x[0-9a-f]+)\]",
                      TEST.read_text())
    return [[int(b, 16) for b in row.split(", ")] for row in rows]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--llvm-mc", default=shutil.which("llvm-mc") or "llvm-mc-18")
    args = parser.parse_args()
    expected = llvm_bytes(args.llvm_mc)
    pinned = pinned_bytes()
    if expected != pinned:
        for i, (e, p) in enumerate(zip(expected, pinned)):
            if e != p:
                print(f"fixture {i}: llvm-mc {e}, pinned {p}", file=sys.stderr)
        if len(expected) != len(pinned):
            print(f"{len(expected)} llvm-mc rows, {len(pinned)} pinned rows", file=sys.stderr)
        return 1
    print(f"PASS {len(pinned)} MIPS32 encoder fixtures agree with llvm-mc")
    return 0


if __name__ == "__main__":
    sys.exit(main())
