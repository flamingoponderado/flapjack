#!/usr/bin/env python3
"""Recheck source through data explorer examples against pinned CakeML."""
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

BVL_STUB = (
    b'(func bvl_stub@31 (h g f e d c b a)\n'
    b'   (let\n      (i <- (op (ElemAt 2) (var a)))\n'
    b'      (call none (var h) (var g) (var f) (var e) (var d)\n'
    b'         (var c) (var b) (op (ElemAt 3) (var a)) (var i)\n'
    b'         (op (ElemAt 0) (var i)))))\n\n'
)

BVI_STUB = (
    b'(func AllocGlobal@62 (a)\n   (let\n      (b <- (op GlobalsPtr))\n'
    b'      (let\n         (c <- (op El (op (Const 0)) (var b)))\n'
    b'         (let\n            (d <- (op Add (var c) (var a)))\n'
    b'            (let\n               (e <- (op Length (var b)))\n'
    b'               (let\n                  (f <- (op Update (var d) (op (Const 0)) (var b)))\n'
    b'                  (if (op Less (var e) (var d)) (var f)\n'
    b'                     (let\n                        (g <- (op RefArray (op (Const 0)) (op Add (var d) (var d))))\n'
    b'                        (let\n                           (h <- (op SetGlobalsPtr (var g)))\n'
    b'                           (call CopyGlobals@63 (var g) (var b)\n'
    b'                              (op Sub (op (Const 1)) (var e))))))))))))\n\n'
)

BVI_START = (
    b'(func start@64 ()\n   (let\n      (a <- (op RefArray (op (Const 0)) (op (Const 3))))\n'
    b'      (let\n         (b <- (op Update (op (Const 1)) (op (Const 0)) (var a)))\n'
    b'         (let\n            (c <- (op SetGlobalsPtr (var a)))\n'
    b'            (call bvl_init@296 (handler d -> (var d)))))))\n\n'
)

DATA_STUB = (
    b'(func AllocGlobal@62 (0)\n   (seq\n      skip\n      (1 := GlobalsPtr () none)\n'
    b'      skip\n      (2 := (Const 0) () none)\n      skip\n      (3 := El (1 2) none)\n'
    b'      skip\n      skip\n      (4 := Add (0 3) (some {0,1,3}))\n'
    b'      skip\n      (5 := Length (1) none)\n      skip\n      skip\n'
    b'      (6 := (Const 0) () none)\n      skip\n      (7 := Update (1 6 4) none)\n'
    b'      skip\n      skip\n      (8 := Less (4 5) (some {0,1,3,4,5,7}))\n'
    b'      (if 8 (return (7))\n         (seq\n            skip\n            (10 := (Const 0) () none)\n'
    b'            skip\n            skip\n            (11 := Add (4 4) (some {0,1,3,4,5,7,10}))\n'
    b'            (12 := RefArray (11 10) (some {0,1,3,4,5,7,10,11}))\n'
    b'            skip\n            (13 := SetGlobalsPtr (12) none)\n'
    b'            skip\n            skip\n            skip\n            (14 := (Const 1) () none)\n'
    b'            skip\n            (15 := Sub (5 14) (some {0,1,3,4,5,7,12,13,14}))\n'
    b'            (call none CopyGlobals@63 (12 1 15) none)))))\n\n'
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
            bvl = result.stdout.split(b'# after clos_to_bvl\n\n', 1)[1].split(b'# after bvl_inline', 1)[0]
            bvi = result.stdout.split(b'# after bvl_to_bvi\n\n', 1)[1].split(b'# after bvi_tailrec', 1)[0]
            if not bvl.startswith(BVL_STUB) or not bvi.startswith(BVI_STUB) or BVI_START not in bvi:
                raise SystemExit(f'original BVL or BVI output mismatch for {source!r}')
            print('original BVL and BVI runtime stubs match', flush=True)
            data = result.stdout.split(b'# after bvi_to_data\n\n', 1)[1]
            if not data.startswith(DATA_STUB):
                raise SystemExit(f'original data-stage output mismatch for {source!r}')
            print('original data-stage runtime stub matches', flush=True)
        print(f'original source-stage output matches: {source!r}', flush=True)


if __name__ == '__main__':
    main()
