#!/usr/bin/env python3
"""Pin source-reviewed unrestricted native conditional-branch decode proof/evidence.

These syntactic regression checks do not independently prove HOL-to-Lean
correspondence. All six universal identities are kernel-checked in Lean and freshly
replayed with proofs using original native definitions in HOL.
"""
from pathlib import Path
import hashlib
ROOT = Path(__file__).resolve().parents[2]
CHECKS = {'Flapjack/RiscV/CorrectnessEncoding/DecodeBranches.lean': '6997b24d2372afc5905f1e574af0b0aae35d91646b914b0ad26297f5d1a9d711', 'scripts/hol-probes/riscv_branch_decode_probeScript.sml': '77c774c1bd047011283bae7d172ceeca79db882046decd47718fc9c03173dd04', 'scripts/hol-probes/riscv_branch_decode_probe.out': 'c27f9a705bd301518400ddc46642e4f82ff8c9e282407b1f2a95632ac518a78a'}
LABELS = ['beq_decode_universal', 'beq_decode_hypotheses', 'beq_zero', 'beq_all_ones', 'beq_alias_sign', 'beq_mixed', 'beq_source_clause', 'beq_carrier_types', 'bne_decode_universal', 'bne_decode_hypotheses', 'bne_zero', 'bne_all_ones', 'bne_alias_sign', 'bne_mixed', 'bne_source_clause', 'bne_carrier_types', 'blt_decode_universal', 'blt_decode_hypotheses', 'blt_zero', 'blt_all_ones', 'blt_alias_sign', 'blt_mixed', 'blt_source_clause', 'blt_carrier_types', 'bltu_decode_universal', 'bltu_decode_hypotheses', 'bltu_zero', 'bltu_all_ones', 'bltu_alias_sign', 'bltu_mixed', 'bltu_source_clause', 'bltu_carrier_types', 'bge_decode_universal', 'bge_decode_hypotheses', 'bge_zero', 'bge_all_ones', 'bge_alias_sign', 'bge_mixed', 'bge_source_clause', 'bge_carrier_types', 'bgeu_decode_universal', 'bgeu_decode_hypotheses', 'bgeu_zero', 'bgeu_all_ones', 'bgeu_alias_sign', 'bgeu_mixed', 'bgeu_source_clause', 'bgeu_carrier_types']
def check(root=ROOT):
    for name, digest in CHECKS.items():
        if hashlib.sha256((root / name).read_bytes()).hexdigest() != digest:
            raise ValueError('native conditional-branch decode proof/evidence drift: ' + name)
    commands = (root / 'scripts/hol-probes/regenerate.sh').read_text().replace(chr(92)+chr(10), ' ').splitlines()
    rows = [s for s in commands if s.startswith('run_probe riscv_branch_decode_probeScript.sml ')]
    if len(rows) != 1:
        raise ValueError('conditional-branch decode requires one complete original registration')
    for label in LABELS:
        if label not in rows[0]:
            raise ValueError('missing conditional-branch original row: ' + label)
    return True
if __name__ == '__main__':
    check()
    print('Native conditional-branch unrestricted decoder proofs and original evidence PASS')
