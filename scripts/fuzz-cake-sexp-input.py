#!/usr/bin/env python3
"""Differentially test mutated CakeML S-expression input against a pinned compiler."""
import argparse
import importlib.util
import random
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
spec = importlib.util.spec_from_file_location('cake_cli_parity', ROOT / 'scripts/check-cake-cli-parity.py')
parity = importlib.util.module_from_spec(spec)
spec.loader.exec_module(parity)
SEEDS = [
    b'((Dlet (unk unk) "x" (Lit 1)))',
    b'((Dmod "M" ((Dlet (unk unk) "x" (Var (Short "y"))))))',
    b'((Dlet (unk unk) "z" (App (Arith Add . IntT) ((Lit 1) (Lit 2)))))',
    b'((Denv "a"))',
]
BYTES = [b'(', b')', b' ', b'.', b'\n', b'\t', b'\r', b'"', b'\\', b"'",
         b'0', b'9', b'a', b'_', b'\x00', b'\xff']
FLAGS = ['--target=riscv', '--sexp=true', '--print_sexp', '--exclude_prelude=true',
         '--skip_type_inference=true']


def mutate(rng):
    source = bytearray(rng.choice(SEEDS))
    for _ in range(rng.randrange(1, 5)):
        pos = rng.randrange(len(source) + 1)
        value = rng.choice(BYTES)
        operation = rng.randrange(3)
        if operation == 0 and pos < len(source):
            del source[pos]
        elif operation == 1 and pos < len(source):
            source[pos:pos + 1] = value
        else:
            source[pos:pos] = value
    return bytes(source)


def run(executable, source, timeout):
    result = subprocess.run([str(executable), *FLAGS], input=source, capture_output=True, timeout=timeout)
    return result.returncode, result.stdout, result.stderr


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--reference', type=Path, required=True)
    parser.add_argument('--cake', type=Path, default=ROOT / '.lake/build/bin/cake')
    parser.add_argument('--seed', type=int, default=9127304)
    parser.add_argument('--count', type=int, default=1200)
    parser.add_argument('--timeout', type=float, default=15)
    args = parser.parse_args()
    parity.check_pinned_reference(args.reference)
    rng = random.Random(args.seed)
    for index in range(args.count):
        source = mutate(rng)
        expected = run(args.reference, source, args.timeout)
        actual = run(args.cake, source, args.timeout)
        if actual != expected:
            raise SystemExit(f'case {index}, seed {args.seed}: {source!r}\n'
                             f'original: {expected!r}\nflapjack: {actual!r}')
    print(f'{args.count} mutated S-expression inputs matched (seed {args.seed})')


if __name__ == '__main__':
    main()
