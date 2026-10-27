#!/usr/bin/env python3
"""Check complete executable output against captures from the pinned CakeML compiler."""
import argparse
import hashlib
import importlib.util
import json
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
FIXTURE = ROOT / 'scripts/hol-probes/cake_cli_pinned_extra.json'
spec = importlib.util.spec_from_file_location('cake_cli_parity', ROOT / 'scripts/check-cake-cli-parity.py')
parity = importlib.util.module_from_spec(spec)
spec.loader.exec_module(parity)

# Each program makes the computed result observable through an output call.
CASES = {
    'string_pattern': 'fun f s = case s of "abc" => 1 | _ => 0; val _ = print_int (f "abc");',
    'large_integer_pattern': 'fun f n = case n of 2305843009213693952 => 1 | _ => 0; val _ = print_int (f 2305843009213693952);',
    'array_update_and_sub': 'val a = Array.array 3 1; val _ = Array.update a 1 4; val _ = print_int (Array.sub a 1);',
    'byte_array_update_and_sub': 'val b = Word8Array.array 3 (Word8.fromInt 9); val _ = Word8Array.update b 1 (Word8.fromInt 7); val _ = print_int (Word8.toInt (Word8Array.sub b 1));',
    'string_concat': 'val _ = print (String.concat ["abc","def"]);',
    'tail_recursive_sum': 'fun loop n acc = if n = 0 then acc else loop (n-1) (acc+n); val _ = print_int (loop 20 0);',
    'exception_payload': 'exception E int; val _ = print_int ((raise E 3) handle E n => n);',
    'captured_closure': 'fun make x = fn y => x+y; val _ = print_int ((make 7) 8);',
    'list_filter_length': 'val _ = print_int (List.length (List.filter (fn x => x > 2) [1,2,3,4,5]));',
    'vector_sub': 'val _ = print_int (Vector.sub (Vector.fromList [3,4,5]) 2);',
    'negative_int_to_string': 'val _ = print (Int.toString (~123456789));',
    'word64_xor': 'val _ = print_int (Word64.toInt (Word64.xorb 0w123 0w77));',
    'substring_size': 'val _ = print_int (String.size (String.substring "abcdef" 2 3));',
    'recursive_factorial': 'fun fact n = if n <= 1 then 1 else n * fact (n - 1); val _ = print_int (fact 7);',
    'mutual_recursion': 'fun even n = if n = 0 then True else odd (n-1) and odd n = if n = 0 then False else even (n-1); val _ = print_int (if even 9 then 1 else 0);',
    'byte_array_copy_vector': 'val a = Word8Array.array 4 (Word8.fromInt 1); val _ = Word8Array.copyVec "abc" 0 3 a 1; val _ = print_int (Word8.toInt (Word8Array.sub a 2));',
    'exception_through_function': 'exception E int; fun f n = if n = 0 then raise E 17 else n; val _ = print_int (f 0 handle E x => x);',
    'large_integer_to_string': 'val _ = print (Int.toString 999999999999999999999999999999);',
    'integer_modulo': 'val _ = print_int (10 mod 3);',
    'negative_integer_division': 'val _ = print_int (~10 div 3);',
    'foldr_subtraction': 'val _ = print_int (List.foldr (fn x => fn y => x-y) 0 [1,2,3]);',
    'recursive_tree_match': 'datatype tree = Leaf int | Node (tree * tree); fun sum t = case t of Leaf x => x | Node (a,b) => sum a + sum b; val _ = print_int (sum (Node (Leaf 3, Leaf 4)));',
    'string_char_roundtrip': 'val _ = print_int (String.size (String.implode (String.explode "abcdef")));',
    'vector_tabulate': 'val v = Vector.tabulate 5 (fn n => n*n); val _ = print_int (Vector.sub v 3);',
    'types_before_print_sexp': 'val x = 42;',
    'print_sexp_before_types': 'val id = fn x => x;',
    'types_before_explore': 'val x = 42;',
    'explore_before_types': 'val id = fn x => x;',
    'types_print_sexp_type_error': 'val x = missing;',
    'types_explore_parse_error': 'val x = ;',
    'print_sexp_empty': '',
    'print_sexp_datatype': 'datatype t = A | B int; fun f x = case x of A => 0 | B n => n;',
    'print_sexp_exception': 'exception E int; val _ = (raise E 4) handle E n => n;',
    'print_sexp_module': 'structure A = struct type t = int; val x = 12; end; val y = A.x;',
    'print_sexp_control_bytes': 'val x = "\\000\\255\\\\";',
    'print_sexp_with_prelude': 'val _ = print "Hi";',
    'print_sexp_input': '((Dlet ((0 0) (0 11)) "x" (Lannot (Lit 1) ((0 11) (0 11)))))',
    'print_sexp_explore': 'val n = 42;',
    'print_sexp_type_error': 'val x = missing;',
    'print_sexp_parse_error': 'val x = ;',
}

CASE_ARGS = {
    'types_before_print_sexp': ['--types', '--print_sexp', '--exclude_prelude=true'],
    'print_sexp_before_types': ['--print_sexp', '--types', '--exclude_prelude=true'],
    'types_before_explore': ['--types', '--explore', '--exclude_prelude=true'],
    'explore_before_types': ['--explore', '--types', '--exclude_prelude=true'],
    'types_print_sexp_type_error': ['--print_sexp', '--types', '--exclude_prelude=true'],
    'types_explore_parse_error': ['--explore', '--types', '--exclude_prelude=true'],
    'print_sexp_empty': ['--print_sexp', '--exclude_prelude=true'],
    'print_sexp_datatype': ['--print_sexp', '--exclude_prelude=true'],
    'print_sexp_exception': ['--print_sexp', '--exclude_prelude=true'],
    'print_sexp_module': ['--print_sexp', '--exclude_prelude=true'],
    'print_sexp_control_bytes': ['--print_sexp', '--exclude_prelude=true'],
    'print_sexp_with_prelude': ['--print_sexp'],
    'print_sexp_input': ['--sexp=true', '--print_sexp', '--exclude_prelude=true'],
    'print_sexp_explore': ['--print_sexp', '--explore', '--exclude_prelude=true'],
    'print_sexp_type_error': ['--print_sexp', '--exclude_prelude=true'],
    'print_sexp_parse_error': ['--print_sexp', '--exclude_prelude=true'],
}
ERROR_CASES = {'types_print_sexp_type_error', 'types_explore_parse_error',
               'print_sexp_type_error', 'print_sexp_parse_error'}

def run(executable, source, name):
    process = subprocess.run([str(executable), '--target=riscv', *CASE_ARGS.get(name, [])], input=source.encode('ascii'),
                             stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=180)
    return {'exit_code': process.returncode,
            'stdout_bytes': len(process.stdout), 'stdout_sha256': hashlib.sha256(process.stdout).hexdigest(),
            'stderr_bytes': len(process.stderr), 'stderr_sha256': hashlib.sha256(process.stderr).hexdigest()}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--record-reference', type=Path, help='capture outputs from the pinned compiler')
    parser.add_argument('--check-reference', type=Path, help='also compare against the pinned compiler')
    parser.add_argument('--cake', type=Path, default=ROOT / '.lake/build/bin/cake')
    args = parser.parse_args()
    if args.record_reference:
        parity.check_pinned_reference(args.record_reference)
        rows = {name: run(args.record_reference, source, name) for name, source in CASES.items()}
        for name, row in rows.items():
            expected_exit = 1 if name in ERROR_CASES else 0
            is_types = name in CASE_ARGS
            if (row['exit_code'] != expected_exit or
                    (row['stdout_bytes'] != 0 if is_types else row['stdout_bytes'] == 0) or
                    (row['stderr_bytes'] == 0 if is_types else row['stderr_bytes'] != 0)):
                raise SystemExit(f'{name}: original compiler did not successfully emit assembly: {row}')
        FIXTURE.write_text(json.dumps({'cakeml_revision': parity.PINNED_REV,
                                       'hol_revision': parity.HOL_REV, 'cases': rows}, indent=2) + '\n')
    expected = json.loads(FIXTURE.read_text())
    if (expected['cakeml_revision'], expected['hol_revision']) != (parity.PINNED_REV, parity.HOL_REV):
        raise SystemExit('unexpected reference provenance')
    if set(expected['cases']) != set(CASES):
        raise SystemExit('reference case list has changed')
    if args.check_reference:
        parity.check_pinned_reference(args.check_reference)
    for name, source in CASES.items():
        want = expected['cases'][name]
        if args.check_reference and run(args.check_reference, source, name) != want:
            raise SystemExit(f'{name}: pinned reference no longer matches its capture')
        got = run(args.cake, source, name)
        if got != want:
            raise SystemExit(f'{name}: output mismatch\nexpected {want}\nactual   {got}')
        print(f'{name}: complete stdout, stderr and exit status match pinned CakeML', flush=True)


if __name__ == '__main__':
    main()
