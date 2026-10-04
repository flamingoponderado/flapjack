#!/usr/bin/env python3
"""Pin source-reviewed unrestricted native SLTU decode proof/evidence.

These syntactic regression checks do not independently prove HOL-to-Lean
correspondence. Both universal identities are kernel-checked in Lean and freshly
replayed with proofs using original native definitions in HOL.
"""
from pathlib import Path
import hashlib
ROOT = Path(__file__).resolve().parents[2]
CHECKS = {'Flapjack/RiscV/CorrectnessEncoding/DecodeSltu.lean': '42c32aff0c395582ca20ed2d89fee40731a34d5ca7029c1c182ae628fb330b10', 'scripts/hol-probes/riscv_sltu_decode_probeScript.sml': '8155ba47247eacc08ff44107756ed3f1d65fd7d2c201f94a1006a856e3f7a47a', 'scripts/hol-probes/riscv_sltu_decode_probe.out': '71e60e5262ec26da3146eebb0d37179897c043944a9246dff1d45faa549a4729'}
LABELS = ['sltu_decode_universal', 'sltu_decode_hypotheses', 'sltu_decode_zero', 'sltu_decode_all_ones', 'sltu_decode_high_bit', 'sltu_decode_alias', 'sltu_encode_source_clause', 'sltu_carrier_types']
def check(root=ROOT):
    for name, digest in CHECKS.items():
        if hashlib.sha256((root / name).read_bytes()).hexdigest() != digest:
            raise ValueError('native SLTU decode proof/evidence drift: ' + name)
    commands = (root / 'scripts/hol-probes/regenerate.sh').read_text().replace(chr(92)+chr(10), ' ').splitlines()
    rows = [s for s in commands if s.startswith('run_probe riscv_sltu_decode_probeScript.sml ')]
    if len(rows) != 1:
        raise ValueError('SLTU decode requires one complete original registration')
    for label in LABELS:
        if label not in rows[0]:
            raise ValueError('missing SLTU original row: ' + label)
    return True
if __name__ == '__main__':
    check()
    print('Native SLTU unrestricted decoder proofs and original evidence PASS')
