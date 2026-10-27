#!/usr/bin/env python3
"""Compare complete CakeML CLI output against explicitly versioned reference captures.

The current reference executable predates the pinned source revision. Its
CakeML compiler backend, parsing, inference, semantics and basis directories
are unchanged at the two revisions; the compiler driver changed in unrelated
Pancake feature handling. These captures are exploratory evidence, not a
replacement for regeneration with a pinned original executable.
"""
import argparse
import hashlib
import json
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
FIXTURE = ROOT / 'scripts/hol-probes/cake_cli_exploratory.json'
REFERENCE_REV = 'e8eca63affd1653105ca4b9cc2f5ca87a01cd0af'
PINNED_REV = '857f0d98da8f8a3580f34423338e697809308ede'
HOL_REV = 'a390cbabd3a4521bab4ee20281e3e42933a8a3ae'
CASES = {
    'empty': '',
    'config_error_reg_alg': '',
    'config_error_gc': '',
    'config_error_gc_generation': '',
    'config_error_bool': '',
    'config_error_bool_multiple': '',
    'config_error_bool_before_backend': '',
    'config_error_target_bool': '',
    'no_prelude_bool_duplicate': 'val x = 42;',
    'no_prelude_target_duplicate': 'val x = 42;',
    'no_prelude_reg_alg_0': 'fun id x = x; val a = id (1, 2);',
    'no_prelude_reg_alg_1': 'fun id x = x; val a = id (1, 2);',
    'no_prelude_reg_alg_2': 'fun id x = x; val a = id (1, 2);',
    'no_prelude_reg_alg_3': 'fun id x = x; val a = id (1, 2);',
    'no_prelude_reg_alg_4': 'fun id x = x; val a = id (1, 2);',
    'no_prelude_reg_alg_duplicate': 'fun id x = x; val a = id (1, 2);',
    'no_prelude_reg_alg_empty': 'fun id x = x; val a = id (1, 2);',
    'no_prelude_gc_none': 'fun id x = x; val a = id (1, 2);',
    'no_prelude_gc_simple': 'fun id x = x; val a = id (1, 2);',
    'no_prelude_gc_generational': 'fun id x = x; val a = id (1, 2);',
    'no_prelude_gc_empty': 'fun id x = x; val a = id (1, 2);',
    'no_prelude_gc_multiple': 'fun id x = x; val a = id (1, 2);',
    'no_prelude_gc_duplicate': 'fun id x = x; val a = id (1, 2);',
    'hello': 'val _ = print "Hello";',
    'identity': 'val id = fn x => x;',
    'module': 'structure M = struct val x = 1; end;',
    'datatype': 'datatype t = A | B; val x = A;',
    'list': 'val xs = [1,2,3]; val ys = List.map (fn x => x + 1) xs;',
    'recursive': 'fun fact n = if n = 0 then 1 else n * fact (n - 1); val x = fact 5;',
    'word64': 'val x = Word64.+ 0w1 0w2;',
    'array': 'val a = Array.array 3 5; val _ = Array.update a 0 7;',
    'string': 'val x = String.concat ["a", "b"];',
    'match': 'val x = case [1] of [] => 0 | a::b => a;',
    'print_int': 'val _ = print_int 42;',
    'exception': 'exception E; val x = (raise E) handle E => 42;',
    'module_call': 'structure M = struct fun id x = x; end; val _ = print (M.id "ok");',
    'polymorphic': 'val id = fn x => x; val a = id 1; val b = id True;',
    'local': 'local val n = 4 in val a = n end;',
    'big_integer': 'val n = 9999999999999999999999999999999999;',
    'closure': 'fun make x = fn y => x + y; val z = (make 3) 4;',
    'tailrec': 'fun loop n a = if n = 0 then a else loop (n - 1) (a + n); val z = loop 10 0;',
    'list_append': 'val x = [1,2] @ [3,4];',
    'list_append_function': 'fun f xs ys = xs @ ys; val x = f [1,2] [3];',
    'list_append_empty': 'val x = [] @ [1];',
    'list_fold': 'val z = List.foldl (fn x => fn a => x + a) 0 [1,2,3];',
    'byte_array': 'val b = Word8.fromInt 12; val a = Word8Array.array 4 b;',
    'nested_modules': 'structure A = struct structure B = struct val n = 4; end; end; val x = A.B.n;',
    'string_subscript': 'val x = String.sub "hello" 1;',
    'letrec': 'val f = let fun g n = if n = 0 then 0 else g (n - 1) in g end;',
    'tuple': 'val x = (1, True, "a");',
    'exception_function': 'exception E; fun f x = if x then raise E else 1; val y = f True handle E => 5;',
    'word64_shift': 'val x = Word64.<< 0w1 5;',
    'word64_shift_right': 'val x = Word64.>> 0w18446744073709551615 65;',
    'word64_shift_arithmetic': 'val x = Word64.~>> 0w9223372036854775808 65;',
    'vector_subscript': 'val v = Vector.fromList [1,2,3]; val x = Vector.sub v 1;',
    'vector_length': 'val v = Vector.fromList [1,2,3]; val x = Vector.length v;',
    'word64_conversion': 'val x = Word64.fromInt 123456789; val y = Word64.toInt x;',
    'word64_negative_conversion': 'val x = Word64.fromInt (~1); val y = Word64.toInt x;',
    'word64_bignum_conversion': 'val x = Word64.fromInt 999999999999999999999999999999;',
    'word64_large_to_int': 'val x = Word64.toInt 0w18446744073709551615;',
    'string_compare': 'val x = String.compare "z" "aa";',
    'string_compare_equal_length': 'val x = String.compare "abc" "abd";',
    'string_less': 'val x = String.< "z" "aa";',
    'char_ord': 'val x = Char.ord #"a";',
    'char_chr': 'val x = Char.chr 65;',
    'word64_bitwise': 'val x = Word64.andb 0w255 0w15;',
    'vector_equal': 'val x = Vector.fromList [1,2] = Vector.fromList [1,2];',
    'integer_to_string': 'val x = Int.toString 12345;',
    'byte_array_subscript': 'val a = Word8Array.array 3 (Word8.fromInt 7); val x = Word8Array.sub a 1;',
    'large_integer_division': 'val x = 99999999999999999999999 div 13;',
    'double_from_int': 'val x = Double.fromInt 42;',
    'double_add': 'val x = Double.+ (Double.fromInt 1) (Double.fromInt 2);',
    'double_compare': 'val x = Double.< (Double.fromInt 1) (Double.fromInt 2);',
    'double_negate': 'val x = Double.~ (Double.fromInt 3);',
    'double_fma': 'val x = Double.fma (Double.fromInt 1) (Double.fromInt 2) (Double.fromInt 3);',
    'array_copy_vector': 'val v = Vector.fromList [1,2]; val b = Array.array 3 0; val _ = Array.copyVec v b 0;',
    'vector_map': 'val v = Vector.fromList [1,2,3]; val x = Vector.map v (fn n => n+1);',
    'byte_array_copy': 'val a = Word8Array.array 3 (Word8.fromInt 1); val b = Word8Array.array 3 (Word8.fromInt 2); val _ = Word8Array.copy a 0 3 b 0;',
    'string_substring': 'val x = String.substring "abcdef" 1 3;',
    'word64_signed_conversion': 'val x = Word64.toIntSigned 0w18446744073709551615;',
    'word64_rotate': 'val x = Word64.ror 0w128 9;',
    'double_word_conversion': 'val x = Double.toWord (Double.fromWord 0w0);',
    'nested_constructor_pattern': 'datatype t = A | B int; fun f x = case x of B 0 => 1 | B n => n | A => 0; val z = f (B 2);',
    'as_pattern': 'fun f (x as (a,b)) = a + b; val z = f (1,2);',
    'recursive_list': 'fun len xs = case xs of [] => 0 | x::rest => 1 + len rest; val z = len [1,2,3];',
    'word8_shift': 'val x = Word8.<< (Word8.fromInt 3) 2;',
    'byte_array_copy_vector': 'val a = Word8Array.array 3 (Word8.fromInt 0); val _ = Word8Array.copyVec "abc" 0 3 a 0;',
    'double_sqrt': 'val x = Double.sqrt (Double.fromInt 4);',
    'double_multiply': 'val x = Double.* (Double.fromInt 2) (Double.fromInt 3);',
    'no_prelude_empty': '',
    'no_prelude_val': 'val x = 42;',
    'no_prelude_identity': 'val id = fn x => x;',
    'undefined_variable': 'val x = foo;',
    'undefined_qualified': 'val x = A.foo;',
    'undefined_nested': 'val x = (fn a => missing);',
    'undefined_multiline': 'val x =\n missing;',
    'undefined_ref': 'val x = ref 0; val _ = x := 3;',
    'undefined_constructor': 'val Foo = 1;',
    'undefined_pattern_constructor': 'val x = case 1 of Foo => 2;',
    'undefined_qualified_constructor': 'val x = case 1 of M.C => 0;',
    'undefined_type_constructor': 'val x : missing = 1;',
    'undefined_qualified_type': 'val x : A.missing = 1;',
    'undefined_type_abbreviation': 'type t = missing;',
    'parse_error_missing': 'val x = ;',
    'parse_error_after_decl': 'val x = 1; val y = ;',
    'parse_error_multiline': 'val x = 1;\nval y = ;',
    'parse_error_character': 'val x = #"ab";',
    'parse_error_expression': 'if',
    'type_error_apply': 'val x = 1 + True;',
    'type_error_condition': 'val x = if 1 then 2 else 3;',
    'type_error_annotation': 'val x : int = True;',
    'type_error_tuple': 'val x = (1,False) : bool * int;',
    'type_error_list': 'val x : int list = [True];',
    'type_error_function': 'val x : int -> bool = fn y => y + 1;',
    'type_error_multiline': 'val x = 1;\nval y = if x then 2 else 3;',
    'type_error_polymorphism': 'val x = fn f => f 1 + f True;',
    'type_error_value_restriction': 'val r = (fn x => x) (fn y => y);',
    'type_error_value_restriction_array': 'val a = Array.array 1 [];',
    'type_error_value_restriction_raise': 'val x = (fn x => x) (raise Bind);',
    'type_error_value_restriction_multiline': 'val n = 1;\nval r = (fn x => x) (fn y => y);',
    'type_error_value_restriction_local': 'local val r = (fn x => x) (fn x => x) in val q = r end;',
    'type_error_value_restriction_module': 'structure M = struct val r = (fn x => x) (fn y => y) end;',
    'type_error_named': 'datatype t = A; val x : t = 1;',
    'type_error_qualified': 'structure M = struct datatype t = A; end; val x : M.t = 1;',
    'type_error_alias': 'datatype t = A; type alias = t; val x : alias = 1;',
    'type_error_two_modules': 'structure A = struct datatype t = A; end; structure B = struct datatype t = B; end; val x : A.t = B.B;',
    'type_error_duplicate_binding': 'val (x,x) = (1,2);',
    'type_error_duplicate_pattern': 'val x = case (1,2) of (a,a) => a;',
    'type_error_duplicate_function_pattern': 'fun f (x,x) = x;',
    'type_error_duplicate_function': 'fun f x = x and f y = y;',
    'type_error_duplicate_abbreviation': "type ('a,'a) t = 'a;",
    'type_error_constructor_arity': 'val x : (int,bool) list = [];',
    'type_error_constructor_value_arity': 'val x = True 1;',
    'type_error_constructor_pattern_arity': 'val x = case True of True a => a;',
    'type_error_constructor_qualified_arity': 'structure M = struct datatype t = A; end; val x = M.A 1;',
    'type_error_constructor_multiline_arity': 'val v = 1;\nval x = True 1;',
    'type_error_duplicate_constructor': 'datatype t = A | A;',
    'type_error_duplicate_type': 'datatype t = A and t = B;',
    'type_error_duplicate_variable': "datatype ('a,'a) t = A;",
    'type_error_duplicate_order': 'datatype t = A | B | A | B;',
    'type_error_duplicate_mutual': 'datatype t = A and u = B | B;',
}

def run(executable, source, name):
    flags = ['--target=riscv']
    if name.startswith('no_prelude_'): flags.append('--exclude_prelude=true')
    if name == 'config_error_reg_alg': flags.append('--reg_alg=bad')
    if name == 'config_error_gc': flags.append('--gc=bad')
    if name == 'config_error_gc_generation': flags.append('--gc=gen1,,bad')
    if name == 'config_error_bool': flags.append('--exclude_prelude=foo')
    if name == 'config_error_bool_multiple': flags.extend(['--skip_type_inference=foo', '--exclude_prelude=bad'])
    if name == 'config_error_bool_before_backend': flags.extend(['--reg_alg=bad', '--exclude_prelude=bad'])
    if name == 'config_error_target_bool': flags = ['--target=bad', '--exclude_prelude=bad']
    if name == 'no_prelude_bool_duplicate': flags.extend(['--exclude_prelude=false', '--skip_type_inference=false', '--skip_type_inference=bad'])
    if name == 'no_prelude_target_duplicate': flags.append('--target=bad')
    gc_options = {
        'no_prelude_gc_none': ['--gc=none'],
        'no_prelude_gc_simple': ['--gc=simple'],
        'no_prelude_gc_generational': ['--gc=gen1000'],
        'no_prelude_gc_empty': ['--gc=gen'],
        'no_prelude_gc_multiple': ['--gc=gen1000,,2000'],
        'no_prelude_gc_duplicate': ['--gc=none', '--gc=bad'],
    }
    flags.extend(gc_options.get(name, []))
    if name == 'no_prelude_reg_alg_duplicate': flags.extend(['--reg_alg=1', '--reg_alg=bad'])
    elif name == 'no_prelude_reg_alg_empty': flags.extend(['--reg_alg=', '--reg_alg=3'])
    elif name.startswith('no_prelude_reg_alg_'): flags.append('--reg_alg=' + name.rsplit('_', 1)[1])
    p = subprocess.run([str(executable), *flags], input=source.encode('ascii'),
                       stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=180)
    return {'exit_code': p.returncode, 'stdout_bytes': len(p.stdout),
            'stdout_sha256': hashlib.sha256(p.stdout).hexdigest(),
            'stderr_bytes': len(p.stderr), 'stderr_sha256': hashlib.sha256(p.stderr).hexdigest()}

def check_reference(executable):
    version = subprocess.check_output([str(executable), '--version'], text=True)
    if f'CakeML: {REFERENCE_REV}' not in version or f'HOL4:   {HOL_REV}' not in version:
        raise SystemExit('reference executable does not report the expected historical revisions')
    actual = subprocess.check_output(['git', '-C', str(ROOT / 'cakeml'), 'rev-parse', 'HEAD'], text=True).strip()
    if actual != PINNED_REV:
        raise SystemExit('CakeML submodule is not at the expected pinned revision')
    paths = ['compiler/backend', 'compiler/parsing', 'compiler/inference', 'basis',
             'semantics', 'translator', 'cv_translator']
    changed = subprocess.check_output(['git', '-C', str(ROOT / 'cakeml'), 'diff', '--name-only',
                                       REFERENCE_REV, PINNED_REV, '--', *paths], text=True).strip()
    if changed:
        raise SystemExit('reference and pinned CakeML compiler sources differ: ' + changed)

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--record-reference', type=Path, help='recapture from the explicitly versioned historical executable')
    parser.add_argument('--check-reference', type=Path, help='also verify captures against that historical executable')
    parser.add_argument('--cake', type=Path, default=ROOT / '.lake/build/bin/cake')
    args = parser.parse_args()
    if args.record_reference:
        check_reference(args.record_reference)
        rows = {name: run(args.record_reference, source, name) for name, source in CASES.items()}
        for name, row in rows.items():
            rejected = name.startswith(('undefined_', 'parse_error_', 'type_error_', 'config_error_'))
            if row['exit_code'] != (1 if rejected else 0) or (row['stderr_bytes'] == 0) == rejected:
                raise SystemExit(f'{name}: reference outcome did not match the expected category')
        FIXTURE.write_text(json.dumps({'reference_revision': REFERENCE_REV, 'hol_revision': HOL_REV,
                                       'pinned_revision': PINNED_REV, 'cases': rows}, indent=2) + '\n')
    expected = json.loads(FIXTURE.read_text())
    if (expected['reference_revision'], expected['hol_revision'], expected['pinned_revision']) != (REFERENCE_REV, HOL_REV, PINNED_REV):
        raise SystemExit('unexpected reference provenance')
    if set(expected['cases']) != set(CASES): raise SystemExit('reference case list has changed')
    if args.check_reference: check_reference(args.check_reference)
    for name, source in CASES.items():
        want = expected['cases'][name]
        if args.check_reference and run(args.check_reference, source, name) != want:
            raise SystemExit(f'{name}: historical reference no longer matches its capture')
        got = run(args.cake, source, name)
        if got != want: raise SystemExit(f'{name}: output mismatch\nexpected {want}\nactual   {got}')
        print(f'{name}: complete stdout, stderr and exit status match the historical reference', flush=True)
