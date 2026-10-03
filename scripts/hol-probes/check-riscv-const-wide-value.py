#!/usr/bin/env python3
"""Pinned unrestricted wide Const value composition signature and original ground oracles.
Syntactic regression only; Lean checks the proof and source review establishes shape.
"""
from pathlib import Path
import hashlib
ROOT = Path(__file__).resolve().parents[2]
CHECKS = {'Flapjack/RiscV/CorrectnessEncoding/ConstWide.lean': '9a7508be35c76e47f00867721be67ecb3fb425cfd2942606c5ac29945c2fa8b1', 'scripts/hol-probes/riscv_const_wide_value_probeScript.sml': '1b4fef2451a8dfb6d093bbc64a0bcc13c9061d373dfa114a4be04317be67c63e', 'scripts/hol-probes/riscv_const_wide_value_probe.out': '5497c1363cc17094cf426fa6bd2621e856fd7e9b4bac00f959db21fe12e413c5'}
def check(root=ROOT):
    for name, expected in CHECKS.items():
        text = (root / name).read_text()
        if name.endswith('ConstWide.lean'):
            text = '\n'.join(text.split('theorem ' + decl, 1)[1].split(' := by', 1)[0] for decl in ('const_wide_value_reconstruction',))
        if hashlib.sha256(text.encode()).hexdigest() != expected:
            raise ValueError('full wide Const value original statement/evidence drift: ' + name)
    driver = (root / 'scripts/hol-probes/regenerate.sh').read_text()
    commands = driver.replace(chr(92) + chr(10), ' ').splitlines()
    registered = [c for c in commands if c.startswith('run_probe riscv_const_wide_value_probeScript.sml ')]
    if len(registered) != 1:
        raise ValueError('wide Const value probe must have one full registration')
    for label in ('const_wide_value_zero', 'const_wide_value_low_positive_max', 'const_wide_value_low_sign_bit', 'const_wide_value_low_all_ones', 'const_wide_value_high_one', 'const_wide_value_high_one_low_sign', 'const_wide_value_positive_max', 'const_wide_value_negative_min', 'const_wide_value_negative_min_low_sign', 'const_wide_value_negative_high_low_positive', 'const_wide_value_negative_high_low_sign', 'const_wide_value_all_ones'):
        if label not in registered[0]:
            raise ValueError('missing original wide Const value evidence row: ' + label)
    return True
if __name__ == '__main__':
    check()
    print('Full original native wide Const value full-domain statement/boundary evidence PASS')
