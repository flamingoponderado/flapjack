#!/usr/bin/env python3
"""Pinned unrestricted upper immediate composition signature and original ground oracles.
Syntactic regression only; Lean checks the proof and source review establishes shape.
"""
from pathlib import Path
import hashlib
ROOT = Path(__file__).resolve().parents[2]
CHECKS = {'Flapjack/RiscV/CorrectnessEncoding/DecodeUpperImmediates.lean': '6d8fd25a3fbbf24a03b29ed90e669016c2f78bc37ebc9362da7f43cc4a1fff30', 'scripts/hol-probes/riscv_upper_decode_probeScript.sml': 'de10518377c0eff945bf485c793affec1540c365402945bf34a95bb68c50ebf8', 'scripts/hol-probes/riscv_upper_decode_probe.out': '8421bc51c10b6d98630daa4a4161fdbf6c782ccdcf6550cfb8a2ec07b075e519'}
def check(root=ROOT):
    for name, expected in CHECKS.items():
        text = (root / name).read_text()
        if name.endswith('DecodeUpperImmediates.lean'):
            text = '\n'.join(text.split('theorem ' + decl, 1)[1].split(' := by', 1)[0] for decl in ('decode_encode_lui', 'decode_encode_auipc'))
        if hashlib.sha256(text.encode()).hexdigest() != expected:
            raise ValueError('full upper immediate original statement/evidence drift: ' + name)
    driver = (root / 'scripts/hol-probes/regenerate.sh').read_text()
    commands = driver.replace(chr(92) + chr(10), ' ').splitlines()
    registered = [c for c in commands if c.startswith('run_probe riscv_upper_decode_probeScript.sml ')]
    if len(registered) != 1:
        raise ValueError('upper immediate probe must have one full registration')
    for label in ('lui_decode_zero', 'lui_decode_all_ones', 'lui_decode_sign_bit', 'lui_decode_positive_max', 'auipc_decode_zero', 'auipc_decode_all_ones', 'auipc_decode_sign_bit', 'auipc_decode_positive_max'):
        if label not in registered[0]:
            raise ValueError('missing original upper immediate evidence row: ' + label)
    return True
if __name__ == '__main__':
    check()
    print('Full original native upper immediate full-domain statement/boundary evidence PASS')
