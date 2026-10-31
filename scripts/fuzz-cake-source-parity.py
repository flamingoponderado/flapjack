#!/usr/bin/env python3
"""Compare generated integer programs against the pinned CakeML compiler.

This is a bounded source-to-assembly differential check, not a correctness
proof. Both complete outputs, standard errors, and exit statuses must match;
a rejection or a timeout is itself a failure. It needs a locally built pinned
original compiler; see docs/PARITY-TESTING.md.
"""
import argparse
import hashlib
import random
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CAKEML_REV = '857f0d98da8f8a3580f34423338e697809308ede'
HOL_REV = 'a390cbabd3a4521bab4ee20281e3e42933a8a3ae'


def expression(rng, depth):
    if depth == 0:
        return rng.choice(['0', '1', '7', '~3', 'x'])
    left, right = expression(rng, depth - 1), expression(rng, depth - 1)
    return rng.choice([
        f'({left} + {right})',
        f'({left} * {right})',
        f'(if {left} < {right} then {right} else {left})',
        f'(let val y = {left} in y + {right} end)',
        f'((fn z => z + {right}) {left})',
    ])


def run(binary, source, timeout):
    return subprocess.run([str(binary), '--target=riscv'], input=source.encode('ascii'),
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=timeout)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--reference', type=Path, required=True, help='pinned original compiler')
    parser.add_argument('--cake', type=Path, default=ROOT / '.lake/build/bin/cake')
    parser.add_argument('--seed', type=int, default=88411)
    parser.add_argument('--count', type=int, default=30)
    parser.add_argument('--timeout', type=float, default=120)
    args = parser.parse_args()
    if args.count < 0 or args.timeout <= 0:
        parser.error('count must be nonnegative and timeout must be positive')
    version = subprocess.check_output([str(args.reference), '--version'], text=True, timeout=args.timeout)
    if f'CakeML: {CAKEML_REV}' not in version or f'HOL4:   {HOL_REV}' not in version:
        raise SystemExit('reference compiler does not report the pinned CakeML and HOL revisions')
    rng = random.Random(args.seed)
    for index in range(args.count):
        source = 'fun f x = ' + expression(rng, rng.randrange(1, 4)) + '; val _ = print_int (f 2);'
        try:
            original = run(args.reference, source, args.timeout)
            candidate = run(args.cake, source, args.timeout)
        except subprocess.TimeoutExpired as error:
            raise SystemExit(f'case {index}, seed {args.seed}: compiler timed out: {error}\n{source}')
        expected = (original.returncode, original.stdout, original.stderr)
        actual = (candidate.returncode, candidate.stdout, candidate.stderr)
        if original.returncode != 0 or actual != expected:
            def describe(result):
                return (f'exit={result.returncode} stdout_sha256={hashlib.sha256(result.stdout).hexdigest()} '
                        f'stderr={result.stderr!r}')
            raise SystemExit(f'case {index}, seed {args.seed}: output mismatch or rejection\n{source}\n'
                             f'original: {describe(original)}\ncandidate: {describe(candidate)}')
        print(f'case {index}: exact output matches', flush=True)
    print(f'{args.count} cases matched (seed {args.seed})')


if __name__ == '__main__':
    main()
