#!/usr/bin/env python3
"""Compare the cake executable's Pancake mode with the pinned CakeML driver."""
import argparse
import importlib.util
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
spec = importlib.util.spec_from_file_location('cake_cli_parity', ROOT / 'scripts/check-cake-cli-parity.py')
parity = importlib.util.module_from_spec(spec)
spec.loader.exec_module(parity)

# Include real compiler output, FFI ordering, globals and warning-producing
# programs; --no_warn lets the last group be compared before warning locations
# are represented by Flapjack's static checker.
CASES = [
    ('Flapjack/Test/OriginalPancake/empty_locals.pnk', []),
    ('Flapjack/Test/OriginalPancake/hello.pnk', []),
    ('Flapjack/Test/OriginalPancake/recursive_global_main.pnk', []),
    ('Flapjack/Test/OriginalPancake/f01189_ffi_stub_order.pnk', ['--no_warn']),
    ('Flapjack/Test/OriginalPancake/f00068_allocator_return.pnk', ['--no_warn']),
    ('Flapjack/Test/OriginalPancake/bitmap_calls.pnk', ['--no_warn', '--reg_alg=0']),
    ('Flapjack/Test/OriginalPancake/bitmap_calls.pnk', ['--no_warn', '--reg_alg=2']),
    ('Flapjack/Test/OriginalPancake/bitmap_calls.pnk', ['--no_warn', '--jump=true', '--hash_size=3']),
    ('Flapjack/Test/OriginalPancake/hello.pnk', ['--no_warn', '--types', '--print_sexp', '--gc=gen10']),
]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--reference', type=Path, required=True)
    parser.add_argument('--cake', type=Path, default=ROOT / '.lake/build/bin/cake')
    args = parser.parse_args()
    parity.check_pinned_reference(args.reference)
    for path, options in CASES:
        source = (ROOT / path).read_bytes()
        results = []
        for executable in (args.reference, args.cake):
            result = subprocess.run([str(executable), '--target=riscv', '--pancake', *options],
                                    input=source, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=180)
            results.append((result.returncode, result.stdout, result.stderr))
        if results[0][0] != 0 or not results[0][1] or results[0][2]:
            raise SystemExit(f'{path} {options}: pinned compiler did not succeed silently')
        if results[0] != results[1]:
            raise SystemExit(f'{path} {options}: exit status or complete output differs')
        print(f'{path} {options}: complete output matches pinned CakeML', flush=True)
    source = (ROOT / 'Flapjack/Test/OriginalPancake/f01189_ffi_stub_order.pnk').read_bytes()
    result = subprocess.run([str(args.cake), '--target=riscv', '--pancake'], input=source,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=180)
    if result.returncode != 2 or result.stdout or b'warning diagnostics are not yet supported' not in result.stderr:
        raise SystemExit('Pancake warnings must not be silently discarded')
    for options in (['--target=bad'], ['--target=bad', '--sexp=bad'],
                    ['--target=riscv', '--sexp=bad', '--exclude_prelude=bad'],
                    ['--target=riscv', '--reg_alg=bad', '--gc=bad']):
        results = []
        for executable in (args.reference, args.cake):
            result = subprocess.run([str(executable), '--pancake', *options], input=b'',
                                    stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=180)
            results.append((result.returncode, result.stdout, result.stderr))
        if results[0] != results[1] or results[0][0] != 1:
            raise SystemExit(f'{options}: Pancake configuration error differs from pinned CakeML')
        print(f'{options}: configuration error matches pinned CakeML', flush=True)


if __name__ == '__main__':
    main()
