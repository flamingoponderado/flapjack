#!/usr/bin/env python3
"""Run all native model drift and original capture gates without a HOL runtime.

Original capture regeneration remains a separate pinned-HOL procedure; CI checks
committed evidence. This does not assert complete model/compiler correctness.
"""
import json
from pathlib import Path
import subprocess
import sys
ROOT=Path(__file__).resolve().parents[2]

def commands(root=ROOT):
    lock=json.loads((root / "scripts/l3/rendering-coverage.json").read_text())
    paths=sorted(str(p.relative_to(root)) for p in (root / "scripts/hol-probes").glob("check-l3-*.py"))
    if not set(lock["fixture_checkers"]) <= set(paths):
        raise ValueError("native fixture checker removed: " + repr(sorted(set(lock["fixture_checkers"]) - set(paths))))
    return [[sys.executable,"scripts/l3/check-renderings.py"],
            *[[sys.executable,p] for p in paths],
            [sys.executable,"scripts/l3/check-decode-fixtures.py"],
            [sys.executable,"scripts/check-hol-probe-rows.py"],
            [sys.executable,"-m","unittest","discover","-s","scripts/tests","-p","test_l3_*.py"]]

if __name__ == "__main__":
    for command in commands():
        print("native gate: " + " ".join(command[1:]),flush=True)
        subprocess.run(command,cwd=ROOT,check=True)
