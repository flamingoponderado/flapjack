#!/usr/bin/env python3
"""Pinned full original ShiftLslImmediate case statement and original specialization evidence.
Syntactic regression only; Lean checks the proof and source review establishes shape.
"""
from pathlib import Path
import hashlib
import re
ROOT = Path(__file__).resolve().parents[2]
CHECKS = {'Flapjack/RiscV/CorrectnessEncoding/ShiftLslImmediate.lean': '0be898afa4ab5d2f956790f3893e4d124fad6311a629aa7c3b99a99150898e6a', 'cakeml/compiler/encoders/asm/asmPropsScript.sml': '3b295bd11d778523bad8673ff1be15e83ab12f63f2e3aee2b7796f1319465a39', 'scripts/hol-probes/riscv_target_shift_lsl_immediate_probeScript.sml': '4b5fdeac13d5164462449318aad2c60e6ce88cde87d0fd994e5e5a19a99bfedb', 'scripts/hol-probes/riscv_target_shift_lsl_immediate_probe.out': '8a4a43a1f9b90e4319b0a9a53d71ec1a1621544ad50e8be6b44384ffca2b9521'}
def check(root=ROOT):
    for name, expected in CHECKS.items():
        text = (root / name).read_text()
        if name.endswith('ShiftLslImmediate.lean'):
            text = text.split('theorem riscv_encoder_correct_shiftLslImmediate', 1)[1].split(' := by', 1)[0]
        elif name.endswith('asmPropsScript.sml'):
            text = text.split('Definition encoder_correct_def:', 1)[1].split('\nEnd', 1)[0]
        if hashlib.sha256(text.encode()).hexdigest() != expected:
            raise ValueError('full ShiftLslImmediate original statement/evidence drift: ' + name)
    driver = (root / 'scripts/hol-probes/regenerate.sh').read_text()
    commands = driver.replace(chr(92) + chr(10), ' ').splitlines()
    registered = [c for c in commands if c.startswith('run_probe riscv_target_shift_lsl_immediate_probeScript.sml ')]
    if len(registered) != 1:
        raise ValueError('ShiftLslImmediate probe must have one full registration')
    for label in ('statement', 'types', 'hypotheses', 'proved'):
        if 'riscv_encoder_correct_shiftLslImmediate_' + label not in registered[0]:
            raise ValueError('missing original ShiftLslImmediate evidence row: ' + label)
    return True
if __name__ == '__main__':
    check()
    print('Full original native ShiftLslImmediate constructor statement/evidence PASS')
