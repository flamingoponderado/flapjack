#!/usr/bin/env python3
"""Pinned full original ShiftRorImmediate case statement and original specialization evidence.
Syntactic regression only; Lean checks the proof and source review establishes shape.
"""
from pathlib import Path
import hashlib
import re
ROOT = Path(__file__).resolve().parents[2]
CHECKS = {'Flapjack/RiscV/CorrectnessEncoding/ShiftRorImmediate.lean': 'e872a60d27bddfe86d24564a5ff3da5f32cbbcb21540d4a647562175167610be', 'cakeml/compiler/encoders/asm/asmPropsScript.sml': '3b295bd11d778523bad8673ff1be15e83ab12f63f2e3aee2b7796f1319465a39', 'scripts/hol-probes/riscv_target_shift_ror_immediate_probeScript.sml': '753ffc3b08360899fa25f17cc2ed344ef96091702614adea048967e21d14ac82', 'scripts/hol-probes/riscv_target_shift_ror_immediate_probe.out': 'ce2c5c46f25b7ab62044a94f443bdb00dd59a0c6e160998a65b73342ebd40f2a'}
def check(root=ROOT):
    for name, expected in CHECKS.items():
        text = (root / name).read_text()
        if name.endswith('ShiftRorImmediate.lean'):
            text = text.split('theorem riscv_encoder_correct_shiftRorImmediate', 1)[1].split(' := by', 1)[0]
        elif name.endswith('asmPropsScript.sml'):
            text = text.split('Definition encoder_correct_def:', 1)[1].split('\nEnd', 1)[0]
        if hashlib.sha256(text.encode()).hexdigest() != expected:
            raise ValueError('full ShiftRorImmediate original statement/evidence drift: ' + name)
    driver = (root / 'scripts/hol-probes/regenerate.sh').read_text()
    commands = driver.replace(chr(92) + chr(10), ' ').splitlines()
    registered = [c for c in commands if c.startswith('run_probe riscv_target_shift_ror_immediate_probeScript.sml ')]
    if len(registered) != 1:
        raise ValueError('ShiftRorImmediate probe must have one full registration')
    for label in ('statement', 'types', 'hypotheses', 'proved'):
        if 'riscv_encoder_correct_shiftRorImmediate_' + label not in registered[0]:
            raise ValueError('missing original ShiftRorImmediate evidence row: ' + label)
    return True
if __name__ == '__main__':
    check()
    print('Full original native ShiftRorImmediate constructor statement/evidence PASS')
