#!/usr/bin/env python3
"""Recheck the source, flat and closure explorer examples against pinned CakeML."""
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

FLAT_EXPECTED = (
    b'(let none (app (GlobalVarAlloc 3)) (con ConIdNone))\n\n'
    b'(app (GlobalVarInit 0) (app Opref (con ConIdNone)))\n\n'
    b'(letrec<>\n   ((f x\n         (mat (var_local x) ((Pcon) (lit)) ((Pcon (Pvar n)) (var_local n)))))\n'
    b'   (app (GlobalVarInit 1) (var_local f)))\n\n'
    b'(mat\n   (app Opapp (app (GlobalVarLookup 1)) (con (ConIdTyped 0 2) (lit)))\n'
    b'   ((Pvar x) (app (GlobalVarInit 2) (var_local x))))\n\n'
)

CLOS_EXPECTED = (
    b'(dec\n   (let\n      ((b <- (op AllocGlobal (op (Const 1)))) (a <- (op (Cons 0))))\n'
    b'      (op (SetGlobal 0) (var a))))\n\n'
    b'(dec\n   (let\n      ((a <-\n            (let\n               ()\n'
    b'               (op AllocGlobal (op (Const 3))))))\n      (op (Cons 0))))\n\n'
    b'(dec (op (SetGlobal 1) (op Ref (op (Cons 0)))))\n\n'
    b'(dec\n   (letrec<f> none none\n      ((a (b)\n            (let\n               ((c <- (var b)))\n'
    b'               (if (op (TagLenEq 0 0) (var c))\n                  (op (Const ~1))\n'
    b'                  (let\n                     ((d <- (op El (op (Const 0)) (var c))))\n'
    b'                     (let\n                        ((e <- (var d)))\n                        (var e)))))))\n'
    b'      (op (SetGlobal 2) (var a))))\n\n'
    b'(dec\n   (let\n      ((a <-\n            (app none (op (Global 2))\n'
    b'               (op (Constant (ConstCons 0 ((ConstInt 7))))))))\n'
    b'      (let\n         ((b <- (var a)))\n         (op (SetGlobal 3) (var b)))))\n\n'
)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('reference', type=Path, help='pinned original CakeML executable')
    args = parser.parse_args()
    parity.check_pinned_reference(args.reference)
    for index, (source, expected) in enumerate(CASES):
        result = subprocess.run([str(args.reference), '--target=riscv', '--explore', '--exclude_prelude=true'],
                                input=source, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=180)
        prefix = b'# original source code\n\n' + expected + b'# after source_let\n\n'
        if result.returncode != 0 or result.stderr or not result.stdout.startswith(prefix):
            raise SystemExit(f'original source-stage output mismatch for {source!r}')
        if index == 0:
            flat = b'# after source_to_flat\n\n' + FLAT_EXPECTED + b'# after remove_flat\n\n'
            if flat not in result.stdout:
                raise SystemExit(f'original flat-stage output mismatch for {source!r}')
            print('original flat-stage output matches', flush=True)
            clos = b'# after flat_to_clos\n\n' + CLOS_EXPECTED + b'# after clos_mti\n\n'
            if clos not in result.stdout:
                raise SystemExit(f'original closure-stage output mismatch for {source!r}')
            print('original closure-stage output matches', flush=True)
        print(f'original source-stage output matches: {source!r}', flush=True)


if __name__ == '__main__':
    main()
