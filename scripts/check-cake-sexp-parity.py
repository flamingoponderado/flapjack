#!/usr/bin/env python3
"""Compare CakeML S-expression input mode against the pinned compiler."""
import argparse
import hashlib
import importlib.util
import json
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
}
BAD_INPUTS = ['', '(', '(1 . 2)', '(garbage)', '((Dlet))', '((Denv "\\\\20"))']


def capture(executable, source, flags):
    result = subprocess.run([str(executable), *flags], input=source, capture_output=True, timeout=180)
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
        FIXTURE.write_text(json.dumps({'cakeml_revision': parity.PINNED_REV, 'hol_revision': parity.HOL_REV,
                                       'programs': rows, 'failures': failures}, indent=2) + '\n')
    fixture = json.loads(FIXTURE.read_text())
    if (fixture['cakeml_revision'], fixture['hol_revision']) != (parity.PINNED_REV, parity.HOL_REV):
        raise SystemExit('unexpected reference provenance')
    if set(fixture['programs']) != set(PROGRAMS) or len(fixture['failures']) != len(BAD_INPUTS):
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


if __name__ == '__main__':
    main()
