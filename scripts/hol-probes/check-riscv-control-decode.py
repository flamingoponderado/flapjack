#!/usr/bin/env python3
"""Pin source-reviewed unrestricted native JAL/JALR decode proof/evidence.

These syntactic regression checks do not independently prove HOL-to-Lean
correspondence. Both universal identities are kernel-checked in Lean and freshly
replayed with proofs using original native definitions in HOL.
"""
from pathlib import Path
import hashlib
ROOT = Path(__file__).resolve().parents[2]
CHECKS = {'Flapjack/RiscV/CorrectnessEncoding/DecodeControl.lean': 'cc7fd1fbbdc3db0695be080de4dfde750d89d4e6f0db4769b6bcedefc5a28d07', 'scripts/hol-probes/riscv_control_decode_probeScript.sml': '10dd8bc27f923d059f68cfd2d8a2922e0a9868f4d547cc430f963f1703fc0b02', 'scripts/hol-probes/riscv_control_decode_probe.out': 'f676d5352c4f72450564a70d87bbf9bd37b77bcf3696273f9b4f245292ba40d2'}
LABELS = ['jal_decode_universal', 'jal_decode_hypotheses', 'jalr_decode_universal', 'jalr_decode_hypotheses', 'jal_zero', 'jal_all_ones', 'jal_link_sign', 'jal_scattered_bits', 'jalr_zero', 'jalr_all_ones', 'jalr_link_alias', 'jalr_mixed', 'jal_source_clause', 'jal_carrier_types', 'jalr_source_clause', 'jalr_carrier_types']
def check(root=ROOT):
    for name, digest in CHECKS.items():
        if hashlib.sha256((root / name).read_bytes()).hexdigest() != digest:
            raise ValueError('native JAL/JALR decode proof/evidence drift: ' + name)
    commands = (root / 'scripts/hol-probes/regenerate.sh').read_text().replace(chr(92)+chr(10), ' ').splitlines()
    rows = [s for s in commands if s.startswith('run_probe riscv_control_decode_probeScript.sml ')]
    if len(rows) != 1:
        raise ValueError('JAL/JALR decode requires one complete original registration')
    for label in LABELS:
        if label not in rows[0]:
            raise ValueError('missing JAL/JALR original row: ' + label)
    return True
if __name__ == '__main__':
    check()
    print('Native JAL/JALR unrestricted decoder proofs and original evidence PASS')
