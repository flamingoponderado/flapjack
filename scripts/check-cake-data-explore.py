#!/usr/bin/env python3
"""Compare the captured DataLang explorer stages with pinned CakeML.

This invokes Lake, so run it sequentially with other Lake commands. Build
Flapjack.Compiler.Backend.BackendPasses.Data before invoking the script.
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
    fixture = json.loads((ROOT / 'scripts/hol-probes/cake_explore_data.json').read_text())
    if (fixture['cakeml_revision'], fixture['hol_revision']) != (parity.PINNED_REV, parity.HOL_REV):
        raise SystemExit('unexpected data explorer fixture provenance')
    reference = subprocess.run([str(args.reference), '--target=riscv', '--explore', '--exclude_prelude=true'],
                               input=fixture['source'].encode('ascii'), stdout=subprocess.PIPE,
                               stderr=subprocess.PIPE, timeout=180)
    if reference.returncode or reference.stderr:
        raise SystemExit('pinned CakeML explorer failed')
    start = b'# after bvi_to_data\n\n'
    end = b'# after data_to_word\n\n'
    if reference.stdout.count(start) != 1 or reference.stdout.count(end) != 1:
        raise SystemExit('pinned CakeML explorer stage boundaries differ')
    expected = start + reference.stdout.split(start, 1)[1].split(end, 1)[0]
    if len(expected) != fixture['length'] or hashlib.sha256(expected).hexdigest() != fixture['sha256']:
        raise SystemExit('pinned CakeML data output differs from captured reference')
    actual = subprocess.run(['lake', 'env', 'lean', '--run', 'scripts/CakeDataExplore.lean'],
                            cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=180)
    if actual.returncode or actual.stderr or actual.stdout != expected:
        raise SystemExit(f'Lean data output differs: exit={actual.returncode}, '
                         f'bytes={len(actual.stdout)}, stderr={actual.stderr[:500]!r}')
    print(f'BVI-to-data through data-space: {len(expected)} complete output bytes match pinned CakeML')


if __name__ == '__main__':
    main()
