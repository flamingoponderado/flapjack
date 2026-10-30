#!/usr/bin/env python3
"""Compare captured stack and lab explorer stages with pinned CakeML.

This invokes Lake, so run it sequentially with other Lake commands. Build
Flapjack.Compiler.Backend.BackendPasses.Stack before invoking the script.
"""
import argparse
import hashlib
import importlib.util
import json
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
spec = importlib.util.spec_from_file_location('cake_cli_parity', ROOT / 'scripts/check-cake-cli-parity.py')
parity = importlib.util.module_from_spec(spec)
spec.loader.exec_module(parity)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('reference', type=Path, help='pinned original CakeML executable')
    args = parser.parse_args()
    parity.check_pinned_reference(args.reference)
    fixture = json.loads((ROOT / 'scripts/hol-probes/cake_explore_stack.json').read_text())
    if (fixture['cakeml_revision'], fixture['hol_revision']) != (parity.PINNED_REV, parity.HOL_REV):
        raise SystemExit('unexpected stack explorer fixture provenance')
    reference = subprocess.run([str(args.reference), '--target=riscv', '--explore', '--exclude_prelude=true'],
                               input=fixture['source'].encode('ascii'), stdout=subprocess.PIPE,
                               stderr=subprocess.PIPE, timeout=180)
    if reference.returncode or reference.stderr:
        raise SystemExit('pinned CakeML explorer failed')
    start = b'# after word_to_stack\n\n'
    if reference.stdout.count(start) != 1:
        raise SystemExit('pinned CakeML explorer stage boundary differs')
    expected = start + reference.stdout.split(start, 1)[1]
    if len(expected) != fixture['length'] or hashlib.sha256(expected).hexdigest() != fixture['sha256']:
        raise SystemExit('pinned CakeML stack output differs from captured reference')
    actual = subprocess.run(['lake', 'env', 'lean', '--run', 'scripts/CakeStackExplore.lean'],
                            cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=180)
    if actual.returncode or actual.stderr or actual.stdout != expected:
        raise SystemExit(f'Lean stack output differs: exit={actual.returncode}, '
                         f'bytes={len(actual.stdout)}, stderr={actual.stderr[:500]!r}')
    print(f'word-to-stack through skip filtering: {len(expected)} complete output bytes match pinned CakeML')


if __name__ == '__main__':
    main()
