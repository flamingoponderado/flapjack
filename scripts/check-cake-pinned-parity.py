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
    'no_prelude_mutual_recursion': 'fun even x = case x of [] => True | h::t => odd t and odd x = case x of [] => False | h::t => even t; val n = even [1,2];',
    'no_prelude_higher_order_conditional': 'val f = fn x => fn y => if x then y else 0; val z = f True 42;',
    'no_prelude_recursive_mixed_arity': 'datatype t = A | B int | C t t; fun pick x = case x of A => 0 | B n => n | C a b => pick a; val n = pick (C A (B 3));',
    'no_prelude_overlapping_tuple_patterns': 'fun f x = case x of (0,_) => 3 | (_,0) => 4 | (x,y) => x; val n = f (1,2);',
    'recursive_array_fill': 'val a = Array.array 8 0; fun fill i = if i = 8 then () else (Array.update a i (i*i); fill (i+1)); val _ = fill 0; val _ = print_int (Array.sub a 7);',
    'two_captured_closures': 'fun f x = let fun g y = x+y in g end; val a = f 3; val b = f 4; val _ = print_int (a 8 + b 9);',
    'sequential_reference_calls': 'val r = Ref 1; fun next x = (r := !r + x; !r); val _ = print_int (next 3 + next 4);',
    'transitive_module_dependency': 'structure A = struct val x = 17; fun f y = x+y; end; structure B = struct val x = A.f 8; end; val _ = print_int B.x;',
    'explore_frontend': 'datatype t = A | B int; fun f x = case x of A => ~1 | B n => n; val x = f (B 7);',
    'explore_basis': 'val _ = print "x";',
    'explore_no_optimisations': 'fun f x = x; val y = f 3;',
    'explore_linear_scan': 'val x = 1;',
    'list_take_length': 'val _ = print_int (List.length (List.take [1,2,3] 2));',
    'list_drop_length': 'val _ = print_int (List.length (List.drop [1,2,3] 1));',
    'let_tuple_pattern': 'fun f x = let val (a,b) = x in a+b end; val _ = print_int (f (4,5));',
    'basis_simple_allocator': 'fun f x = x + 1; val _ = print_int (f 5);',
    'basis_linear_scan': 'val _ = print "x";',
    'basis_generational_gc': 'fun f x = x + 1; val _ = print_int (f 5);',
    'basis_without_closure_optimisations': 'fun f x = x + 1; val _ = print_int (f 5);',
    'basis_skip_inference': 'fun f x = x + 1; val _ = print_int (f 5);',
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
    'polymorphic_tree': "datatype 'a tree = L 'a | N ('a tree * 'a tree); fun f x = case x of L a => a | N (a,b) => f a + f b; val _ = print_int (f (N (L 2,L 3)));",
    'local_declaration': 'local val x = 42 in val y = x end; val _ = print_int y;',
    'module_dependency': 'structure A = struct val x = 1; val y = x + 2; end; val _ = print_int A.y;',
    'exception_function_handler': 'exception E int; fun f x = (raise E x) handle E n => n; val _ = print_int (f 7);',
    'recursive_list_sum': 'fun f xs = case xs of [] => 0 | x::xs => x + f xs; val _ = print_int (f [1,2,3]);',
    'vector_length': 'val _ = print_int (Vector.length (Vector.fromList [1,2,3]));',
    'string_concat_with': 'val _ = print (String.concatWith "," ["a","b"]);',
    'tuple_match': 'fun f x = case x of (a,b) => a+b; val _ = print_int (f (1,2));',
    'list_reverse_length': 'val _ = print_int (List.length (List.rev [1,2,3,4]));',
    'array_update_first': 'val x = Array.array 4 1; val _ = Array.update x 0 9; val _ = print_int (Array.sub x 0);',
    'string_sub_char_ord': 'val _ = print_int (Char.ord (String.sub "hello" 1));',
    'datatype_payload_match': 'datatype t = A int | B; fun f x = case x of A n => n | B => 0; val _ = print_int (f (A 9));',
    'foldl_addition': 'val _ = print_int (List.foldl (fn x => fn y => x+y) 0 [1,2,3]);',
    'substring_output': 'val _ = print (String.substring "abcdef" 1 3);',
    'local_captured_function': 'fun f x = let fun g y = x+y in g 3 end; val _ = print_int (f 5);',
    'short_circuit_boolean': 'val _ = print_int (if True andalso False orelse True then 1 else 0);',
    'partial_application': 'fun curry x y z = x+y+z; val f = curry 1; val _ = print_int (f 2 3);',
    'triple_constructor_match': 'datatype t = T (int * int * int) | U; val _ = print_int (case T (1,2,3) of T (x,y,z) => x+y+z | U => 0);',
    'escaped_byte_subscript': 'val _ = print_int (Char.ord (String.sub "\\000\\255" 1));',
    'let_captured_closure': 'fun f x = let val y = x + 2 in fn z => y + z end; val _ = print_int (f 3 4);',
    'negative_large_product': 'val _ = print (Int.toString (~1 * 999999999999999999999999999999999999));',
    'module_datatype_match': 'structure X = struct datatype t = A | B int; fun f x = case x of A => 0 | B n => n; end; val _ = print_int (X.f (X.B 4));',
    'reference_mutation': 'val r = Ref 3; val _ = r := !r + 4; val _ = print_int (!r);',
    'nested_exception_handlers': 'exception E int; exception F int; fun f x = ((raise E x) handle E n => raise F (n + 1)) handle F n => n; val _ = print_int (f 5);',
    'mixed_constructor_arities': 'datatype t = A | B int | C (int * int); fun f x = case x of A => 0 | B x => x | C (x,y) => x+y; val _ = print_int (f (C (1,2)));',
    'captured_reference_mutation': 'fun f x = let val r = Ref x; val _ = r := !r + 2 in !r end; val _ = print_int (f 3);',
    'array_tabulate': 'val a = Array.tabulate 5 (fn x => x * x); val _ = print_int (Array.sub a 3);',
    'word64_shift': 'val _ = print_int (Word64.toInt (Word64.<< 0w1 4));',
    'local_tail_recursive_product': 'fun f x = let fun loop n a = if n = 0 then a else loop (n-1) (a*n) in loop x 1 end; val _ = print_int (f 10);',
    'division_exception': 'fun f x = (x div 0) handle Div => 9; val _ = print_int (f 4);',
    'list_map_length': 'val _ = print_int (List.length (List.map (fn x => x + 1) [1,2,3]));',
    'array_bounds_handler': 'val a = Array.array 2 5; val _ = print_int ((Array.sub a 8) handle Subscript => 17);',
    'word_boundary_shift': 'val _ = print_int (Word64.toInt (Word64.>> (Word64.<< 0w1 63) 63));',
    'nested_list_pattern': 'val _ = print_int (case [1,2,3] of x::y::z => x+y | _ => 0);',
    'negative_division_and_modulo': 'fun f x = (x div ~5) + (x mod 5); val _ = print_int (f ~42);',
    'large_integer_dynamic_addition': 'fun f x = x + 123456789012345678901234567890; val _ = print (Int.toString (f 1));',
    'nested_tuple_projection': 'fun f x = case x of (a,(b,(c,d))) => a+b+c+d; val _ = print_int (f (1,(2,(3,4))));',
    'recursive_fibonacci': 'fun f n = if n < 2 then n else f (n-1) + f (n-2); val _ = print_int (f 8);',
    'foldl_captured_arithmetic': 'fun f xs = List.foldl (fn x => fn a => a + x*x) 0 xs; val _ = print_int (f [1,2,3]);',
    'string_case_branches': 'fun f n = case n of 0 => "zero" | 1 => "one" | _ => "other"; val _ = print (f 2);',
    'reused_captured_function': 'fun f x = let val g = fn y => x*y in g 3 + g 5 end; val _ = print_int (f 4);',
    'nullary_exception_handler': 'exception E; val _ = (raise E) handle E => print "caught";',
    'two_payload_constructors': 'datatype t = A int | B int | C; fun f x = case x of A n => n | B n => ~n | C => 0; val _ = print_int (f (B 7));',
    'tabulated_array_update': 'val a = Array.tabulate 8 (fn x => x); val _ = Array.update a 7 42; val _ = print_int (Array.sub a 7);',
    'curried_closure': 'fun f x = (fn y => fn z => x + y + z); val _ = print_int (f 1 2 3);',
    'datatype_string_branch': 'datatype t = A int | B string; fun g x = case x of A y => y | B s => String.size s; val _ = print_int (g (B "hello"));',
    'recursive_list_fold_product': 'fun q n = if n < 1 then [] else n::q (n-1); val _ = print_int (List.foldl (fn x => fn y => x*y) 1 (q 6));',
    'byte_array_max_update': 'val x = Word8Array.array 5 (Word8.fromInt 0); val _ = Word8Array.update x 3 (Word8.fromInt 255); val _ = print_int (Word8.toInt (Word8Array.sub x 3));',
    'vector_concat_length': 'val v = Vector.concat [Vector.fromList [1,2], Vector.fromList [3,4]]; val _ = print_int (Vector.length v);',
    'tuple_captured_curried_closure': 'fun f (x,y) = let val z = x+y in (fn a => fn b => z+a+b) end; val _ = print_int (f (1,2) 3 4);',
    'nested_recursive_list_match': 'fun f xs = case xs of [] => 0 | x::ys => (case ys of [] => x | y::zs => x+y+f zs); val _ = print_int (f [1,2,3]);',
    'char_max_roundtrip': 'val _ = print_int (Char.ord (Char.chr 255));',
    'list_concat_length': 'val _ = print_int (List.length (List.concat [[1,2],[3],[4,5]]));',
    'signed_division_pair': 'fun f a b = (a div b, a mod b); val _ = print_int (case f ~100 7 of (a,b) => a+b);',
    'word8_bitwise_and': 'val _ = print_int (Word8.toInt (Word8.andb (Word8.fromInt 123) (Word8.fromInt 25)));',
    'word8_bitwise_not': 'val _ = print_int (Word8.toInt (Word8.notb (Word8.fromInt 3)));',
    'byte_array_overlapping_copy': 'val a = Word8Array.array 3 (Word8.fromInt 1); val _ = Word8Array.update a 1 (Word8.fromInt 2); val _ = Word8Array.copy a 0 2 a 1; val _ = print_int (Word8.toInt (Word8Array.sub a 2));',
    'exception_tuple_payload': 'exception E (int * int); val _ = print_int ((raise E (1,2)) handle E (a,b) => a+b);',
    'negative_bigint_division': 'val _ = print (Int.toString (~999999999999999999999999999999 div 3));',
    'nested_closure_reuse': 'fun f x = let val g = fn y => let val h = fn z => x+y+z in h 5 end in g 6 + g 7 end; val _ = print_int (f 5);',
    'short_circuit_reference_update': 'val r = Ref 5; val x = (False andalso (r := 6; True)) orelse (True andalso (r := 7; True)); val _ = print_int (!r + (if x then 1 else 0));',
    'recursive_list_fold_sum': 'fun f n = if n = 0 then [] else n::f (n-1); val _ = print_int (List.foldl (fn x => fn y => x+y) 0 (f 10));',
    'vector_tabulate_sum': 'val v = Vector.tabulate 5 (fn x => x+6); val _ = print_int (Vector.sub v 2 + Vector.length v);',
    'nested_exception_rethrow': 'exception E int; exception F int; fun f x = ((raise E x) handle E y => raise F (y+5)) handle F z => z*6; val _ = print_int (f 7);',
    'types_before_print_sexp': 'val x = 42;',
    'print_sexp_before_types': 'val id = fn x => x;',
    'types_before_explore': 'val x = 42;',
    'explore_before_types': 'val id = fn x => x;',
    'types_print_sexp_type_error': 'val x = missing;',
    'types_explore_parse_error': 'val x = ;',
    'explore_parse_error': 'val x = ;',
    'explore_type_error': 'val x = missing;',
    'explore_sexp_parse_error': '(',
    'explore_sexp_type_error': '((Denv "x"))',
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
    'no_prelude_mutual_recursion': ['--exclude_prelude=true'],
    'no_prelude_higher_order_conditional': ['--exclude_prelude=true'],
    'no_prelude_recursive_mixed_arity': ['--exclude_prelude=true'],
    'no_prelude_overlapping_tuple_patterns': ['--exclude_prelude=true'],
    'explore_frontend': ['--explore', '--exclude_prelude=true'],
    'explore_basis': ['--explore'],
    'explore_no_optimisations': ['--explore', '--exclude_prelude=true', '--multi=false', '--known=false', '--call=false'],
    'explore_linear_scan': ['--explore', '--exclude_prelude=true', '--reg_alg=4'],
    'basis_simple_allocator': ['--reg_alg=0'],
    'basis_linear_scan': ['--reg_alg=4'],
    'basis_generational_gc': ['--gc=gen100'],
    'basis_without_closure_optimisations': ['--multi=false', '--known=false', '--call=false'],
    'basis_skip_inference': ['--skip_type_inference=true'],
    'types_before_print_sexp': ['--types', '--print_sexp', '--exclude_prelude=true'],
    'print_sexp_before_types': ['--print_sexp', '--types', '--exclude_prelude=true'],
    'types_before_explore': ['--types', '--explore', '--exclude_prelude=true'],
    'explore_before_types': ['--explore', '--types', '--exclude_prelude=true'],
    'types_print_sexp_type_error': ['--print_sexp', '--types', '--exclude_prelude=true'],
    'types_explore_parse_error': ['--explore', '--types', '--exclude_prelude=true'],
    'explore_parse_error': ['--explore'],
    'explore_type_error': ['--explore'],
    'explore_sexp_parse_error': ['--explore', '--sexp=true'],
    'explore_sexp_type_error': ['--explore', '--sexp=true'],
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
               'explore_parse_error', 'explore_type_error', 'explore_sexp_parse_error', 'explore_sexp_type_error',
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
            is_types = (any(flag in CASE_ARGS.get(name, []) for flag in ('--types', '--print_sexp')) or
                        (name in ERROR_CASES and '--explore' in CASE_ARGS.get(name, [])))
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
