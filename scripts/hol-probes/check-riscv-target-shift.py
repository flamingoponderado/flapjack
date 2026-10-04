#!/usr/bin/env python3
"""Pinned full original Shift case statement and original specialization evidence.
Syntactic regression only; Lean checks the proof and source review establishes shape.
"""
from pathlib import Path
import hashlib
import re
ROOT = Path(__file__).resolve().parents[2]
CHECKS = {'Flapjack/RiscV/CorrectnessEncoding/Shift.lean': 'a3fb89b6e3c1ade3f9511d0ddd47beb38ee281c2e187b620e6550b7fe73e7810', 'cakeml/compiler/encoders/asm/asmPropsScript.sml': '3b295bd11d778523bad8673ff1be15e83ab12f63f2e3aee2b7796f1319465a39', 'scripts/hol-probes/riscv_target_shift_probeScript.sml': 'eb513e58a7530fc436ea97f77e1e2c6c2c5fad7e177d1ce56be13201c6240642', 'scripts/hol-probes/riscv_target_shift_probe.out': '54589757ee0230f4dcbb7004b1d9e521a7634fa702116dfcbd385a6c4f4ebc04'}
def check(root=ROOT):
    for name, expected in CHECKS.items():
        text = (root / name).read_text()
        if name.endswith('Shift.lean'):
            text = text.split('theorem riscv_encoder_correct_shift', 1)[1].split(' := by', 1)[0]
        elif name.endswith('asmPropsScript.sml'):
            text = text.split('Definition encoder_correct_def:', 1)[1].split('\nEnd', 1)[0]
        if hashlib.sha256(text.encode()).hexdigest() != expected:
            raise ValueError('full Shift original statement/evidence drift: ' + name)
    driver = (root / 'scripts/hol-probes/regenerate.sh').read_text()
    commands = driver.replace(chr(92) + chr(10), ' ').splitlines()
    registered = [c for c in commands if c.startswith('run_probe riscv_target_shift_probeScript.sml ')]
    if len(registered) != 1:
        raise ValueError('Shift probe must have one full registration')
    for label in ('statement', 'types', 'hypotheses', 'proved'):
        if 'riscv_encoder_correct_shift_' + label not in registered[0]:
            raise ValueError('missing original Shift evidence row: ' + label)
    return True
if __name__ == '__main__':
    check()
    print('Full original native Shift constructor statement/evidence PASS')
