#!/usr/bin/env python3
"""Compare `flapjack-compile --hex` and `--sections` with original Pancake.

For every checked-in source of the original-Pancake corpus, run the original
CakeML `cake --pancake --target=riscv` and Flapjack's `--hex` and `--sections`
modes.  For a program the original accepts, require that `--hex` equals the
original `.byte` stream after `cake_main:` and that the `--sections`
`<label> <address> <bytes>` lines equal the original `makesym` sections as
(base, bytes) pairs.  A program the original rejects must be rejected by both
Flapjack modes.  The assembly frame itself is checked by
`scripts/parity-small-corpus.py`; this complements it for the other modes.

Usage: python3 scripts/parity-cli-modes.py [--cake PATH] [--flapjack PATH] [FILE...]
"""
import argparse
import glob
import importlib.util
import os
import re
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_CAKE = os.path.expanduser("~/pancake-lean/cakeml/developers/bin/cake")
DEFAULT_FLAPJACK = REPO_ROOT / ".lake" / "build" / "bin" / "flapjack-compile"


def load_parser():
    spec = importlib.util.spec_from_file_location(
        "parity_bytes", REPO_ROOT / "scripts" / "parity-bytes.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--cake", default=DEFAULT_CAKE)
    parser.add_argument("--flapjack", default=str(DEFAULT_FLAPJACK))
    parser.add_argument("files", nargs="*")
    args = parser.parse_args(argv)
    pb = load_parser()
    files = args.files or sorted(
        glob.glob(str(REPO_ROOT / "Flapjack/Test/OriginalPancake/*.pnk")))
    exact = rejected = failures = 0
    for path in files:
        with open(path, "rb") as source:
            cake = subprocess.run([args.cake, "--pancake", "--target=riscv"],
                                  stdin=source, capture_output=True)
        hexed = subprocess.run([args.flapjack, "--hex", path],
                               capture_output=True, text=True)
        sections = subprocess.run([args.flapjack, "--sections", path],
                                  capture_output=True, text=True)
        if cake.returncode != 0:
            rejected += 1
            if hexed.returncode == 0 or sections.returncode == 0:
                failures += 1
                print(f"FAIL original rejects, flapjack accepts: {path}")
            continue
        text = cake.stdout.decode("utf-8", "replace")
        marker = text.find("cake_main:")
        flat = []
        for line in text[marker:].splitlines():
            match = re.search(r"\.byte(.*)", line)
            if match:
                flat.extend(pb.parse_byte_line(match.group(1)))
        original_sections = sorted(
            (base, bytes(data)) for base, data in pb.parse_assembly(text).values())
        if hexed.returncode != 0 or sections.returncode != 0:
            failures += 1
            print(f"FAIL flapjack rejects an accepted program: {path}")
            continue
        hex_bytes = [int(token, 16) for token in hexed.stdout.split()]
        flapjack_sections = sorted(
            (int(fields[1]), bytes(int(token, 16) for token in fields[2:]))
            for fields in (line.split() for line in sections.stdout.splitlines()))
        if hex_bytes == flat and flapjack_sections == original_sections:
            exact += 1
        else:
            failures += 1
            print(f"FAIL {path}: hex_equal={hex_bytes == flat} "
                  f"sections_equal={flapjack_sections == original_sections}")
    print(f"cli-modes exact={exact} original_rejected={rejected} "
          f"failures={failures} total={len(files)}")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
