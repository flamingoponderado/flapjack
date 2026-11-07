#!/usr/bin/env python3
"""Check the CakeML feature-query mode against pinned source and optionally a compiler."""
import argparse
import importlib.util
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
spec = importlib.util.spec_from_file_location('cake_features', ROOT / 'scripts/generate-cake-features.py')
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)
parser = argparse.ArgumentParser()
parser.add_argument('--pinned-reference', type=Path)
args = parser.parse_args()
if args.pinned_reference:
    version = subprocess.check_output([str(args.pinned_reference), '--version'], text=True)
    if ('CakeML: 857f0d98da8f8a3580f34423338e697809308ede' not in version or
            'HOL4:   a390cbabd3a4521bab4ee20281e3e42933a8a3ae' not in version):
        raise SystemExit('reference executable does not report the pinned revisions')

features = {}
for name, enabled in module.feature_events():
    features.setdefault(name, enabled)
cases = [([f'--pancake_feature={name}'], b'true' if enabled else b'false')
         for name, enabled in features.items()]
cases += [(['--pancake_feature='], b'false'),
          (['--pancake_feature=not_a_feature', '--target=bad'], b'false'),
          (['--pancake_feature=structs', '--pancake_feature=not_a_feature'], b'true'),
          (['--pancake_feature=not_a_feature', '--pancake_feature=structs'], b'false'),
          (['--sexp=bad', '--pancake_feature=structs'], b'true')]

for flags, expected in cases:
    result = subprocess.run([str(ROOT / '.lake/build/bin/cake'), *flags], input=b'invalid CakeML',
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=30)
    if (result.returncode, result.stdout, result.stderr) != (0, expected, b''):
        raise SystemExit(f'feature output differs for {flags!r}: {result!r}')
    if args.pinned_reference:
        reference = subprocess.run([str(args.pinned_reference), *flags], input=b'invalid CakeML',
                                   stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=30)
        if (result.returncode, result.stdout, result.stderr) != (reference.returncode, reference.stdout, reference.stderr):
            raise SystemExit(f'pinned executable feature output differs for {flags!r}')
print(f'{len(cases)} feature queries match the pinned source' +
      (' and compiler' if args.pinned_reference else ''))
