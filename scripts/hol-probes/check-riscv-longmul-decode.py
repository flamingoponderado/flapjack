#!/usr/bin/env python3
"""Pin source-reviewed unrestricted native LongMul decode proof/evidence.

These syntactic regression checks do not independently prove HOL-to-Lean
correspondence. Both universal identities are kernel-checked in Lean and freshly
replayed with proofs using original native definitions in HOL.
"""
from pathlib import Path
import hashlib
ROOT = Path(__file__).resolve().parents[2]
CHECKS = {'Flapjack/RiscV/CorrectnessEncoding/DecodeLongMul.lean': '6637fb01a5b619bc9478edba91f4f8bd2b2f8b91687af00919999a398de2057e', 'scripts/hol-probes/riscv_longmul_decode_probeScript.sml': 'd919404d4dcf653ab9205ca7efa033d5802d879ca599dbd16eb0fbc805b9399b', 'scripts/hol-probes/riscv_longmul_decode_probe.out': '3de16c333167c40058027f04d310221411019f7de94959eb3d747176c6c32b14'}
LABELS = ['mulhu_decode_universal', 'mulhu_decode_hypotheses', 'mulhu_decode_zero', 'mulhu_decode_all_ones', 'mulhu_decode_high_bit', 'mulhu_decode_alias', 'mulhu_encode_source_clause', 'mulhu_carrier_types', 'mul_decode_universal', 'mul_decode_hypotheses', 'mul_decode_zero', 'mul_decode_all_ones', 'mul_decode_high_bit', 'mul_decode_alias', 'mul_encode_source_clause', 'mul_carrier_types']
def check(root=ROOT):
    for name, digest in CHECKS.items():
        if hashlib.sha256((root / name).read_bytes()).hexdigest() != digest:
            raise ValueError('native LongMul decode proof/evidence drift: ' + name)
    commands = (root / 'scripts/hol-probes/regenerate.sh').read_text().replace(chr(92)+chr(10), ' ').splitlines()
    rows = [s for s in commands if s.startswith('run_probe riscv_longmul_decode_probeScript.sml ')]
    if len(rows) != 1:
        raise ValueError('LongMul decode requires one complete original registration')
    for label in LABELS:
        if label not in rows[0]:
            raise ValueError('missing LongMul original row: ' + label)
    return True
if __name__ == '__main__':
    check()
    print('Native MULHU/MUL unrestricted decoder proofs and original evidence PASS')
