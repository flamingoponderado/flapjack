#!/usr/bin/env python3
"""Pinned full original ShiftRorRegister case statement and original specialization evidence.
Syntactic regression only; Lean checks the proof and source review establishes shape.
"""
from pathlib import Path
import hashlib
import re
ROOT = Path(__file__).resolve().parents[2]
CHECKS = {'Flapjack/RiscV/CorrectnessEncoding/ShiftRorRegister.lean': '48138ada8ff5395ca6212048c8f19c3376fd5df7b4d93761ebeaac79fa1a392f', 'cakeml/compiler/encoders/asm/asmPropsScript.sml': '3b295bd11d778523bad8673ff1be15e83ab12f63f2e3aee2b7796f1319465a39', 'scripts/hol-probes/riscv_target_shift_ror_register_probeScript.sml': 'a89ceb8e42e9345bff8cd5101a1ec4e3e232bddc1ae0a7738e070c2ec25dd91d', 'scripts/hol-probes/riscv_target_shift_ror_register_probe.out': '71b862702371f4dd533b0d509ac8f591c69a7bcf2a193d207c56061724728620'}
def check(root=ROOT):
    for name, expected in CHECKS.items():
        text = (root / name).read_text()
        if name.endswith('ShiftRorRegister.lean'):
            text = text.split('theorem riscv_encoder_correct_shiftRorRegister', 1)[1].split(' := by', 1)[0]
        elif name.endswith('asmPropsScript.sml'):
            text = text.split('Definition encoder_correct_def:', 1)[1].split('\nEnd', 1)[0]
        if hashlib.sha256(text.encode()).hexdigest() != expected:
            raise ValueError('full ShiftRorRegister original statement/evidence drift: ' + name)
    driver = (root / 'scripts/hol-probes/regenerate.sh').read_text()
    commands = driver.replace(chr(92) + chr(10), ' ').splitlines()
    registered = [c for c in commands if c.startswith('run_probe riscv_target_shift_ror_register_probeScript.sml ')]
    if len(registered) != 1:
        raise ValueError('ShiftRorRegister probe must have one full registration')
    for label in ('statement', 'types', 'hypotheses', 'proved'):
        if 'riscv_encoder_correct_shiftRorRegister_' + label not in registered[0]:
            raise ValueError('missing original ShiftRorRegister evidence row: ' + label)
    return True
if __name__ == '__main__':
    check()
    print('Full original native ShiftRorRegister constructor statement/evidence PASS')
