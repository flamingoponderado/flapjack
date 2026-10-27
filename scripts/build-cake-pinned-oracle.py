#!/usr/bin/env python3
"""Build an unverified compiler from the pinned CakeML translated AST.

Requires the pinned HOL and CakeML checkouts with compiler64ProgTheory already
built, plus the historical bootstrap binary in CakeML's developers/bin/cake.
All generated files go into the caller-provided output directory. This follows
CakeML's unverified sexpr bootstrap and does not establish compiler correctness.
"""
import argparse
import os
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CAKEML_REV = '857f0d98da8f8a3580f34423338e697809308ede'
HOL_REV = 'a390cbabd3a4521bab4ee20281e3e42933a8a3ae'
BOOTSTRAP_REV = 'e8eca63affd1653105ca4b9cc2f5ca87a01cd0af'


def revision(path):
    return subprocess.check_output(['git', '-C', str(path), 'rev-parse', 'HEAD'], text=True).strip()


def version(binary):
    return subprocess.check_output([str(binary), '--version'], text=True)


def require_version(binary, cakeml_rev):
    info = version(binary)
    if f'CakeML: {cakeml_rev}' not in info or f'HOL4:   {HOL_REV}' not in info:
        raise SystemExit(f'unexpected revision in {binary} --version')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cakeml', type=Path, required=True)
    parser.add_argument('--hol', type=Path, required=True)
    parser.add_argument('--output-dir', type=Path, required=True)
    parser.add_argument('--reuse-sexpr', type=Path,
                        help='reuse an already exported S-expression instead of running HOL')
    args = parser.parse_args()
    cakeml, hol, out = (path.resolve() for path in (args.cakeml, args.hol, args.output_dir))
    if revision(cakeml) != CAKEML_REV or revision(hol) != HOL_REV:
        raise SystemExit('CakeML or HOL checkout is not at the pinned revision')
    if out == cakeml or cakeml in out.parents or out == hol or hol in out.parents:
        raise SystemExit('output directory must be outside both reference checkouts')
    bootstrap = cakeml / 'developers/bin/cake'
    require_version(bootstrap, BOOTSTRAP_REV)
    if not (cakeml / 'compiler/bootstrap/translation/.hol/objs/compiler64ProgTheory.dat').is_file():
        raise SystemExit('build pinned compiler64ProgTheory before exporting the compiler AST')
    out.mkdir(parents=True, exist_ok=True)
    sexpr = args.reuse_sexpr.resolve() if args.reuse_sexpr else out / 'cake-sexpr-x64-64'
    if not args.reuse_sexpr:
        env = os.environ.copy()
        env['CAKE_SEXPR_OUTPUT'] = str(sexpr)
        with (out / 'export.log').open('wb') as log:
            subprocess.run([str(hol / 'bin/hol'), 'run',
                            str(ROOT / 'scripts/hol-probes/cake_pinned_sexpr_export.sml')],
                           cwd=cakeml / 'compiler/bootstrap/translation', env=env,
                           stdout=log, stderr=subprocess.STDOUT, check=True)
    env = os.environ.copy()
    env.update(CML_STACK_SIZE='8000', CML_HEAP_SIZE='8000')
    assembly, binary = out / 'cake.S', out / 'cake'
    with sexpr.open('rb') as source, assembly.open('wb') as output, (out / 'compile.log').open('wb') as log:
        subprocess.run([str(bootstrap), '--sexp=true', '--exclude_prelude=true',
                        '--skip_type_inference=true', '--emit_empty_ffi=true', '--reg_alg=0'],
                       stdin=source, stdout=output, stderr=log, env=env, check=True)
    subprocess.run(['cc', '-O2', '-DEVAL', str(assembly), str(cakeml / 'basis/basis_ffi.c'),
                    '-o', str(binary), '-lm'], check=True)
    require_version(binary, CAKEML_REV)
    print(f'Built unverified pinned-source compiler: {binary}')


if __name__ == '__main__':
    main()
