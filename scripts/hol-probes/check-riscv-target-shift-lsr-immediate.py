#!/usr/bin/env python3
"""Pinned full original ShiftLsrImmediate case statement and original specialization evidence.
Syntactic regression only; Lean checks the proof and source review establishes shape.
"""
from pathlib import Path
import hashlib
import re
ROOT = Path(__file__).resolve().parents[2]
CHECKS = {'Flapjack/RiscV/CorrectnessEncoding/ShiftLsrImmediate.lean': '83dc9ff9a7ad1ad3a8e4f8cb9a66c09773b480f89822015c2642c0d7795632a3', 'cakeml/compiler/encoders/asm/asmPropsScript.sml': '3b295bd11d778523bad8673ff1be15e83ab12f63f2e3aee2b7796f1319465a39', 'scripts/hol-probes/riscv_target_shift_lsr_immediate_probeScript.sml': '15bf177e97533f3bcf00cfeb3ef4e9467b4c21b0eb89d103183ed380409980ba', 'scripts/hol-probes/riscv_target_shift_lsr_immediate_probe.out': '782f9d7dd179ed46b8331a2e6df4231f1ba537e9432282cc7f2669b95bc0c2c6'}
def check(root=ROOT):
    for name, expected in CHECKS.items():
        text = (root / name).read_text()
        if name.endswith('ShiftLsrImmediate.lean'):
            text = text.split('theorem riscv_encoder_correct_shiftLsrImmediate', 1)[1].split(' := by', 1)[0]
        elif name.endswith('asmPropsScript.sml'):
            text = text.split('Definition encoder_correct_def:', 1)[1].split('\nEnd', 1)[0]
        if hashlib.sha256(text.encode()).hexdigest() != expected:
            raise ValueError('full ShiftLsrImmediate original statement/evidence drift: ' + name)
    driver = (root / 'scripts/hol-probes/regenerate.sh').read_text()
    commands = driver.replace(chr(92) + chr(10), ' ').splitlines()
    registered = [c for c in commands if c.startswith('run_probe riscv_target_shift_lsr_immediate_probeScript.sml ')]
    if len(registered) != 1:
        raise ValueError('ShiftLsrImmediate probe must have one full registration')
    for label in ('statement', 'types', 'hypotheses', 'proved'):
        if 'riscv_encoder_correct_shiftLsrImmediate_' + label not in registered[0]:
            raise ValueError('missing original ShiftLsrImmediate evidence row: ' + label)
    return True
if __name__ == '__main__':
    check()
    print('Full original native ShiftLsrImmediate constructor statement/evidence PASS')
