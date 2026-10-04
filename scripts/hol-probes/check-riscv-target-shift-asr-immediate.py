#!/usr/bin/env python3
"""Pinned full original ShiftAsrImmediate case statement and original specialization evidence.
Syntactic regression only; Lean checks the proof and source review establishes shape.
"""
from pathlib import Path
import hashlib
import re
ROOT = Path(__file__).resolve().parents[2]
CHECKS = {'Flapjack/RiscV/CorrectnessEncoding/ShiftAsrImmediate.lean': 'b57445b542ab432704ea5365ed3dbdd048dbb1f0b955e8304d7ab74de8381f9f', 'cakeml/compiler/encoders/asm/asmPropsScript.sml': '3b295bd11d778523bad8673ff1be15e83ab12f63f2e3aee2b7796f1319465a39', 'scripts/hol-probes/riscv_target_shift_asr_immediate_probeScript.sml': '1c8aeedd8344d7f9be9f9ade05f7ca81eed6fb85e1f819bb2deef74fe259c209', 'scripts/hol-probes/riscv_target_shift_asr_immediate_probe.out': 'af8c93156c7f614430f831bbeabe74b21accb9aabd5cb42b93136abd9c80f41a'}
def check(root=ROOT):
    for name, expected in CHECKS.items():
        text = (root / name).read_text()
        if name.endswith('ShiftAsrImmediate.lean'):
            text = text.split('theorem riscv_encoder_correct_shiftAsrImmediate', 1)[1].split(' := by', 1)[0]
        elif name.endswith('asmPropsScript.sml'):
            text = text.split('Definition encoder_correct_def:', 1)[1].split('\nEnd', 1)[0]
        if hashlib.sha256(text.encode()).hexdigest() != expected:
            raise ValueError('full ShiftAsrImmediate original statement/evidence drift: ' + name)
    driver = (root / 'scripts/hol-probes/regenerate.sh').read_text()
    commands = driver.replace(chr(92) + chr(10), ' ').splitlines()
    registered = [c for c in commands if c.startswith('run_probe riscv_target_shift_asr_immediate_probeScript.sml ')]
    if len(registered) != 1:
        raise ValueError('ShiftAsrImmediate probe must have one full registration')
    for label in ('statement', 'types', 'hypotheses', 'proved'):
        if 'riscv_encoder_correct_shiftAsrImmediate_' + label not in registered[0]:
            raise ValueError('missing original ShiftAsrImmediate evidence row: ' + label)
    return True
if __name__ == '__main__':
    check()
    print('Full original native ShiftAsrImmediate constructor statement/evidence PASS')
