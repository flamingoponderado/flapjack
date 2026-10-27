#!/usr/bin/env python3
"""Compare CakeML S-expression input mode against the pinned compiler."""
import argparse
import hashlib
import importlib.util
import json
import os
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
FIXTURE = ROOT / 'scripts/hol-probes/cake_sexp_cli_pinned.json'
spec = importlib.util.spec_from_file_location('cake_cli_parity', ROOT / 'scripts/check-cake-cli-parity.py')
parity = importlib.util.module_from_spec(spec)
spec.loader.exec_module(parity)

# The original compiler itself exports these declarations as S-expressions.
PROGRAMS = {
    'empty': '',
    'literal': 'val x = 1;',
    'string': 'val x = "hi";',
    'word': 'val x = 0w42;',
    'function': 'fun f x = x + 1; val _ = print_int (f 3);',
    'datatype_match': 'datatype t = A | B int; val _ = print_int (case B 3 of A => 0 | B n => n);',
    'exception': 'exception E int; val _ = print_int ((raise E 4) handle E n => n);',
    'module': 'structure M = struct val x = 42; end; val _ = print_int M.x;',
    'conditional': 'fun f x = if x then 1 else 2; val _ = print_int (f True);',
    'list': 'val _ = print_int (List.length [1,2,3]);',
    'local': 'local val x = 1 in val y = x end;',
    'type_alias': 'type t = int list; val x : t = [1];',
    'array': 'val a = Array.array 3 1; val _ = Array.update a 1 4; val _ = print_int (Array.sub a 1);',
    'closure': 'val x = fn x => fn y => x+y;',
    'recursive_list': 'fun f n = if n = 0 then [] else n :: f (n - 1); val _ = print_int (List.length (f 7));',
    'annotated_function': 'fun f (x : int) = x + 1; val _ = print_int (f 7);',
    'boolean_logic': 'val _ = print_int (if True andalso False orelse True then 1 else 0);',
}
BAD_INPUTS = ['', '(', '(1 . 2)', '(garbage)', '((Dlet))', '((Denv "\\\\20"))']
TYPE_ERRORS = [
    '((Dlet (unk unk) "x" (Var (Short "missing"))))',
    '((Dlet ((0 0) (0 1)) "x" (Var (Short "missing"))))',
    '((Dlet (unk unk) "x" (If (Lit 1) (Lit 2) (Lit 3))))',
    '((Dlet (unk unk) "x" (App (Arith Add . IntT) ((Lit 1) (Con (SOME (Short "True")) nil)))))',
]
STRESS_INPUTS = {
    'many_declarations': b'(' + b'(Denv "a") ' * 20000 + b')',
    'long_byte_string': b'((Denv "' + b'x' * 100000 + b'"))',
}
STRESS_FLAGS = ['--sexp=true', '--types', '--exclude_prelude=true', '--skip_type_inference=true']


def capture(executable, source, flags, env=None):
    result = subprocess.run([str(executable), *flags], input=source, capture_output=True, timeout=180, env=env)
    return {'exit_code': result.returncode,
            'stdout_bytes': len(result.stdout), 'stdout_sha256': hashlib.sha256(result.stdout).hexdigest(),
            'stderr_bytes': len(result.stderr), 'stderr_sha256': hashlib.sha256(result.stderr).hexdigest()}


def export(executable, source):
    result = subprocess.run([str(executable), '--print_sexp', '--exclude_prelude=true',
                             '--skip_type_inference=true'], input=source.encode('ascii'),
                            capture_output=True, timeout=180)
    if result.returncode or result.stdout or not result.stderr:
        raise SystemExit(f'original S-expression export failed for {source!r}')
    return result.stderr.decode('ascii')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--record-reference', type=Path)
    parser.add_argument('--check-reference', type=Path)
    parser.add_argument('--bootstrap-sexp', type=Path, help='also compare a large exported compiler AST')
    parser.add_argument('--cake', type=Path, default=ROOT / '.lake/build/bin/cake')
    args = parser.parse_args()
    flags = {'types': ['--sexp=true', '--types'], 'assembly': ['--sexp=true', '--target=riscv']}
    if args.record_reference:
        parity.check_pinned_reference(args.record_reference)
        rows = {}
        for name, source in PROGRAMS.items():
            sexp = export(args.record_reference, source)
            outputs = {mode: capture(args.record_reference, sexp.encode('ascii'), fs) for mode, fs in flags.items()}
            if any(row['exit_code'] for row in outputs.values()) or not outputs['assembly']['stdout_bytes']:
                raise SystemExit(f'original compilation failed for {name}')
            rows[name] = {'sexp': sexp, 'outputs': outputs}
        failures = [capture(args.record_reference, s.encode('ascii'), flags['types']) for s in BAD_INPUTS]
        if any(row['exit_code'] != 1 or row['stdout_bytes'] or not row['stderr_bytes'] for row in failures):
            raise SystemExit('original rejected-input outcome is unexpected')
        type_errors = [capture(args.record_reference, s.encode('ascii'), flags['types']) for s in TYPE_ERRORS]
        if any(row['exit_code'] != 1 or row['stdout_bytes'] or not row['stderr_bytes'] for row in type_errors):
            raise SystemExit('original type-error outcome is unexpected')
        stress = {name: capture(args.record_reference, s, STRESS_FLAGS) for name, s in STRESS_INPUTS.items()}
        if any(row['exit_code'] or row['stdout_bytes'] or not row['stderr_bytes'] for row in stress.values()):
            raise SystemExit('original stress-input outcome is unexpected')
        FIXTURE.write_text(json.dumps({'cakeml_revision': parity.PINNED_REV, 'hol_revision': parity.HOL_REV,
                                       'programs': rows, 'failures': failures, 'type_errors': type_errors,
                                       'stress': stress}, indent=2) + '\n')
    fixture = json.loads(FIXTURE.read_text())
    if (fixture['cakeml_revision'], fixture['hol_revision']) != (parity.PINNED_REV, parity.HOL_REV):
        raise SystemExit('unexpected reference provenance')
    if (set(fixture['programs']) != set(PROGRAMS) or len(fixture['failures']) != len(BAD_INPUTS) or
            len(fixture['type_errors']) != len(TYPE_ERRORS) or set(fixture['stress']) != set(STRESS_INPUTS)):
        raise SystemExit('reference case list has changed')
    if args.check_reference:
        parity.check_pinned_reference(args.check_reference)
    for name, source in PROGRAMS.items():
        row = fixture['programs'][name]
        if args.check_reference and export(args.check_reference, source) != row['sexp']:
            raise SystemExit(f'{name}: original S-expression export differs')
        for mode, fs in flags.items():
            data = row['sexp'].encode('ascii')
            want = row['outputs'][mode]
            if args.check_reference and capture(args.check_reference, data, fs) != want:
                raise SystemExit(f'{name}/{mode}: reference differs from capture')
            got = capture(args.cake, data, fs)
            if got != want:
                raise SystemExit(f'{name}/{mode}: output mismatch\nexpected {want}\nactual   {got}')
        print(f'{name}: type and complete RISC-V output match pinned CakeML', flush=True)
    for i, source in enumerate(BAD_INPUTS):
        want = fixture['failures'][i]
        for executable in ([args.check_reference, args.cake] if args.check_reference else [args.cake]):
            if capture(executable, source.encode('ascii'), flags['types']) != want:
                raise SystemExit(f'rejected input {i}: output differs for {executable}')
    print('malformed S-expression outputs match pinned CakeML')
    for i, source in enumerate(TYPE_ERRORS):
        want = fixture['type_errors'][i]
        for executable in ([args.check_reference, args.cake] if args.check_reference else [args.cake]):
            if capture(executable, source.encode('ascii'), flags['types']) != want:
                raise SystemExit(f'type-error input {i}: output differs for {executable}')
    print('S-expression type-error diagnostics match pinned CakeML')
    for name, source in STRESS_INPUTS.items():
        for executable in ([args.check_reference, args.cake] if args.check_reference else [args.cake]):
            if capture(executable, source, STRESS_FLAGS) != fixture['stress'][name]:
                raise SystemExit(f'{name}: output differs for {executable}')
        print(f'{name}: large-input output matches pinned CakeML')
    if args.bootstrap_sexp:
        if not args.check_reference:
            raise SystemExit('--bootstrap-sexp requires --check-reference')
        source = args.bootstrap_sexp.read_bytes()
        env = os.environ.copy()
        env.update(CML_STACK_SIZE='8000', CML_HEAP_SIZE='8000')
        reference = capture(args.check_reference, source, STRESS_FLAGS, env)
        actual = capture(args.cake, source, STRESS_FLAGS, env)
        if reference['exit_code'] != 0 or actual != reference:
            raise SystemExit(f'bootstrap AST output mismatch\nexpected {reference}\nactual   {actual}')
        print(f'bootstrap AST ({len(source)} bytes): output matches pinned CakeML')


if __name__ == '__main__':
    main()
