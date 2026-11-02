#!/usr/bin/env python3
"""Differentially test mutated CakeML S-expression input against a pinned compiler."""
import argparse
import hashlib
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
COMPILE_FLAGS = ['--target=riscv', '--sexp=true', '--exclude_prelude=true',
                 '--skip_type_inference=true']
PRIMITIVES = [
    'Opapp', 'Opassign', 'Opref', 'Opderef', 'Equality', 'Aw8alloc', 'Aw8sub',
    'Aw8length', 'Aw8update', 'CopyStrStr', 'CopyStrAw8', 'CopyAw8Str',
    'CopyAw8Aw8', 'Strsub', 'Strlen', 'Implode', 'Explode', 'Strcat',
    'VfromList', 'Vsub', 'Vlength', 'Aalloc', 'AallocEmpty', 'Asub', 'Alength',
    'Aupdate', 'ConfigGC', 'ListAppend', '(FFI . "test")', '(Arith Add . IntT)',
    '(Arith Mul . BoolT)', '(FromTo IntT . StrT)', '(Shift8Lsl . 3)', 'Eval',
    'Envid', 'Vsubunsafe', 'Asubunsafe', 'Aupdateunsafe', 'Aw8subunsafe',
    'Aw8updateunsafe', 'XorAw8Strunsafe', 'AallocFixed', 'ForceThunk',
    '(AllocThunk . Evaluated)', '(UpdateThunk . NotEvaluated)',
]


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


def run(executable, source, timeout, flags=FLAGS):
    result = subprocess.run([str(executable), *flags], input=source, capture_output=True, timeout=timeout)
    return result.returncode, result.stdout, result.stderr


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--reference', type=Path, required=True)
    parser.add_argument('--cake', type=Path, default=ROOT / '.lake/build/bin/cake')
    parser.add_argument('--seed', type=int, default=9127304)
    parser.add_argument('--count', type=int, default=1200)
    parser.add_argument('--timeout', type=float, default=15)
    parser.add_argument('--primitive-arities', action='store_true',
                        help='also compare complete compiled output for bootstrap primitives at arities 0 through 3')
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
    if args.primitive_arities:
        for primitive in PRIMITIVES:
            for arity in range(4):
                arguments = ' '.join(['(Lit 1)'] * arity)
                source = f'((Dlet (unk unk) "x" (App {primitive} ({arguments}))))'.encode('ascii')
                expected = run(args.reference, source, args.timeout, COMPILE_FLAGS)
                actual = run(args.cake, source, args.timeout, COMPILE_FLAGS)
                if actual != expected:
                    def summary(result):
                        code, stdout, stderr = result
                        return (code, len(stdout), hashlib.sha256(stdout).hexdigest(), stderr)
                    raise SystemExit(f'primitive {primitive}, arity {arity}: {source!r}\n'
                                     f'original: {summary(expected)!r}\nflapjack: {summary(actual)!r}')
        print(f'{len(PRIMITIVES) * 4} bootstrap primitive/arity outputs matched')


if __name__ == '__main__':
    main()
