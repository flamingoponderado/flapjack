#!/usr/bin/env python3
"""Check help output and precedence against the pinned CakeML driver source."""
import argparse
import importlib.util
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
spec = importlib.util.spec_from_file_location('cake_help', ROOT / 'scripts/generate-cake-help.py')
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)
expected = module.source_help().encode('ascii')
cake = ROOT / '.lake/build/bin/cake'
parser = argparse.ArgumentParser()
parser.add_argument('--pinned-reference', type=Path,
                    help='also compare output against a pinned-revision compiler executable')
args = parser.parse_args()
if args.pinned_reference:
    version = subprocess.check_output([str(args.pinned_reference), '--version'], text=True)
    if ('CakeML: 857f0d98da8f8a3580f34423338e697809308ede' not in version or
            'HOL4:   a390cbabd3a4521bab4ee20281e3e42933a8a3ae' not in version):
        raise SystemExit('reference executable does not report the pinned revisions')

for flags in (['--help'], ['--target=bad', '--help'],
              ['--help', '--version', '--sexp=bad'],
              ['--pancake_feature=structs', '--help'],
              ['--print_sexp', '--help', '--unknown']):
    result = subprocess.run([str(cake), *flags], input=b'invalid CakeML',
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                            timeout=30)
    if (result.returncode, result.stdout, result.stderr) != (0, expected, b''):
        raise SystemExit(f'CakeML help output or precedence differs for {flags!r}')
    if args.pinned_reference:
        reference = subprocess.run([str(args.pinned_reference), *flags], input=b'invalid CakeML',
                                   stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=30)
        if (result.returncode, result.stdout, result.stderr) != (reference.returncode, reference.stdout, reference.stderr):
            raise SystemExit(f'pinned executable help differs for {flags!r}')
    print(f'{flags!r}: complete pinned-source help output matches')

# Interactive mode has higher precedence than help in the original wrapper.
# It is not implemented here, so verify the port does not silently print help.
for flag in ('--repl', '--candle'):
    result = subprocess.run([str(cake), flag, '--help'], input=b'',
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                            timeout=30)
    if result.returncode != 2 or result.stdout or b'interactive mode is not supported' not in result.stderr:
        raise SystemExit(f'unsupported interactive mode not reported for {flag}')
