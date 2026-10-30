#!/usr/bin/env python3
"""Recheck the source-stage examples in CakeSourceDisplayParity against CakeML."""
import argparse
import importlib.util
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
spec = importlib.util.spec_from_file_location('cake_cli_parity', ROOT / 'scripts/check-cake-cli-parity.py')
parity = importlib.util.module_from_spec(spec)
spec.loader.exec_module(parity)

CASES = [
    (
        b'datatype t = A | B int; fun f x = case x of A => ~1 | B n => n; val x = f (B 7);',
        b'(Dtype (() t ((A ()) (B ((Attup () (Short int)))))))\n\n'
        b'(Dletrec\n   (f x\n      (Lannot\n         (Mat (Lannot (Var (Short x)))\n'
        b'            (((Pcon (some (Short A)) ()) (Lannot (Lit (IntLit ~1))))\n'
        b'               ((Pcon (some (Short B)) ((Pvar n))) (Lannot (Var (Short n)))))))))\n\n'
        b'(Dlet (Pvar x)\n   (Lannot\n      (App Opapp (Lannot (Var (Short f)))\n'
        b'         (Lannot (Con (some (Short B)) ((Lit (IntLit 7))))))))\n\n',
    ),
    (b'val x = "\\255";', b'(Dlet (Pvar x) (Lannot (Lit (StrLit \xff))))\n\n'),
]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('reference', type=Path, help='pinned original CakeML executable')
    args = parser.parse_args()
    parity.check_pinned_reference(args.reference)
    for source, expected in CASES:
        result = subprocess.run([str(args.reference), '--target=riscv', '--explore', '--exclude_prelude=true'],
                                input=source, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=180)
        prefix = b'# original source code\n\n' + expected + b'# after source_let\n\n'
        if result.returncode != 0 or result.stderr or not result.stdout.startswith(prefix):
            raise SystemExit(f'original source-stage output mismatch for {source!r}')
        print(f'original source-stage output matches: {source!r}', flush=True)


if __name__ == '__main__':
    main()
