#!/usr/bin/env python3
"""Compare and time complete linear-scan output against pinned CakeML."""
import argparse
import importlib.util
import subprocess
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
spec = importlib.util.spec_from_file_location('cake_cli_parity', ROOT / 'scripts/check-cake-cli-parity.py')
parity = importlib.util.module_from_spec(spec)
spec.loader.exec_module(parity)


def run(executable, source, algorithm, timeout):
    args = [str(executable), '--target=riscv', '--exclude_prelude=true', f'--reg_alg={algorithm}']
    started = time.monotonic()
    result = subprocess.run(args, input=source, capture_output=True, timeout=timeout)
    return result, time.monotonic() - started


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--reference', type=Path, required=True, help='pinned original CakeML executable')
    parser.add_argument('--cake', type=Path, default=ROOT / '.lake/build/bin/cake')
    parser.add_argument('--alg', type=int, default=5, help='linear-scan allocator setting (at least 4)')
    parser.add_argument('--input', type=Path, help='CakeML input; defaults to a small declaration')
    parser.add_argument('--timeout', type=float, default=300, help='per-executable timeout in seconds')
    args = parser.parse_args()
    if args.alg < 4:
        parser.error('--alg must be at least 4 to select linear scan')
    if args.timeout <= 0:
        parser.error('--timeout must be positive')
    parity.check_pinned_reference(args.reference)
    source = args.input.read_bytes() if args.input else b'val x = 1;\n'
    try:
        reference, reference_time = run(args.reference, source, args.alg, args.timeout)
        actual, actual_time = run(args.cake, source, args.alg, args.timeout)
    except subprocess.TimeoutExpired as error:
        raise SystemExit(f'{error.cmd[0]} exceeded the {args.timeout:g}s timeout') from error
    print(f'pinned CakeML: {reference_time:.2f}s; Flapjack: {actual_time:.2f}s', flush=True)
    if reference.returncode != 0 or not reference.stdout or reference.stderr:
        raise SystemExit(f'pinned compiler failed to emit assembly: exit={reference.returncode}, '
                         f'stderr={reference.stderr!r}')
    if (actual.returncode, actual.stdout, actual.stderr) != (reference.returncode, reference.stdout, reference.stderr):
        raise SystemExit(f'output mismatch: reference exit={reference.returncode}, '
                         f'stdout={len(reference.stdout)} bytes, stderr={len(reference.stderr)} bytes; '
                         f'Flapjack exit={actual.returncode}, stdout={len(actual.stdout)} bytes, '
                         f'stderr={len(actual.stderr)} bytes')
    print(f'complete stdout ({len(actual.stdout)} bytes), stderr, and exit status match pinned CakeML')


if __name__ == '__main__':
    main()
