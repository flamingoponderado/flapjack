#!/usr/bin/env python3
"""Pinned full original AddCarry case statement and original specialization evidence.
Syntactic regression only; Lean checks the proof and source review establishes shape.
"""
from pathlib import Path
import hashlib
import re
ROOT = Path(__file__).resolve().parents[2]
CHECKS = {'Flapjack/RiscV/CorrectnessEncoding/AddCarry.lean': '4a31efe08ff3668fd638619782c15f31113c07f7f2513e20267603afda7b3712', 'cakeml/compiler/encoders/asm/asmPropsScript.sml': '3b295bd11d778523bad8673ff1be15e83ab12f63f2e3aee2b7796f1319465a39', 'scripts/hol-probes/riscv_target_addcarry_probeScript.sml': 'b86e471104b78c7d9746528f5c7316ade44d1924d957f96b0bc02868bc09a95d', 'scripts/hol-probes/riscv_target_addcarry_probe.out': 'dc5fab33f9bd80732ef00d4ab317673e36abc47d42e4c70f411fe4728b19f049', 'Flapjack/RiscV/CorrectnessEncoding/AddCarry/Post.lean': 'e0395d4131d4fc43269da2f446fb4549e156b312611a1f1ba5d7a3b4227c456b'}
def check(root=ROOT):
    for name, expected in CHECKS.items():
        text = (root / name).read_text()
        if name.endswith('AddCarry.lean'):
            text = text.split('theorem riscv_encoder_correct_addcarry', 1)[1].split(' := by', 1)[0]
        elif name.endswith('Post.lean'):
            text = text.split('def program', 1)[1].split('/--', 1)[0]
        elif name.endswith('asmPropsScript.sml'):
            text = text.split('Definition encoder_correct_def:', 1)[1].split('\nEnd', 1)[0]
        if hashlib.sha256(text.encode()).hexdigest() != expected:
            raise ValueError('full AddCarry original statement/evidence drift: ' + name)
    driver = (root / 'scripts/hol-probes/regenerate.sh').read_text()
    commands = driver.replace(chr(92) + chr(10), ' ').splitlines()
    registered = [c for c in commands if c.startswith('run_probe riscv_target_addcarry_probeScript.sml ')]
    if len(registered) != 1:
        raise ValueError('AddCarry probe must have one full registration')
    for label in ('statement', 'types', 'hypotheses', 'proved'):
        if 'riscv_encoder_correct_addcarry_' + label not in registered[0]:
            raise ValueError('missing original AddCarry evidence row: ' + label)
    return True
if __name__ == '__main__':
    check()
    print('Full original native AddCarry constructor statement/evidence PASS')
