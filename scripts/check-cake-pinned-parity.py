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
}


def run(executable, source):
    process = subprocess.run([str(executable), '--target=riscv'], input=source.encode('ascii'),
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
        rows = {name: run(args.record_reference, source) for name, source in CASES.items()}
        for name, row in rows.items():
            if row['exit_code'] != 0 or row['stdout_bytes'] == 0 or row['stderr_bytes'] != 0:
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
        if args.check_reference and run(args.check_reference, source) != want:
            raise SystemExit(f'{name}: pinned reference no longer matches its capture')
        got = run(args.cake, source)
        if got != want:
            raise SystemExit(f'{name}: output mismatch\nexpected {want}\nactual   {got}')
        print(f'{name}: complete stdout, stderr and exit status match pinned CakeML', flush=True)


if __name__ == '__main__':
    main()
