#!/usr/bin/env python3
"""Pinned full original LongMul case statement and original specialization evidence.
Syntactic regression only; Lean checks the proof and source review establishes shape.
"""
from pathlib import Path
import hashlib
import re
ROOT = Path(__file__).resolve().parents[2]
CHECKS = {'Flapjack/RiscV/CorrectnessEncoding/LongMul.lean': '8e2ebb27b1ef31733fdc60273b6a8bb04c06e87abfd0c2e814ae6e31c50eacdb', 'cakeml/compiler/encoders/asm/asmPropsScript.sml': '3b295bd11d778523bad8673ff1be15e83ab12f63f2e3aee2b7796f1319465a39', 'scripts/hol-probes/riscv_target_longmul_probeScript.sml': '6a355a073c4139f26e0369fd2064f9efc025729baade99e87eb306caffa91e49', 'scripts/hol-probes/riscv_target_longmul_probe.out': '0ffb2c0a548582bc6cf72ddf558524e980d85868d665e55ae3bcc54f91574136'}
def check(root=ROOT):
    for name, expected in CHECKS.items():
        text = (root / name).read_text()
        if name.endswith('LongMul.lean'):
            text = text.split('theorem riscv_encoder_correct_longmul', 1)[1].split(' := by', 1)[0]
        elif name.endswith('asmPropsScript.sml'):
            text = text.split('Definition encoder_correct_def:', 1)[1].split('\nEnd', 1)[0]
        if hashlib.sha256(text.encode()).hexdigest() != expected:
            raise ValueError('full LongMul original statement/evidence drift: ' + name)
    driver = (root / 'scripts/hol-probes/regenerate.sh').read_text()
    commands = driver.replace(chr(92) + chr(10), ' ').splitlines()
    registered = [c for c in commands if c.startswith('run_probe riscv_target_longmul_probeScript.sml ')]
    if len(registered) != 1:
        raise ValueError('LongMul probe must have one full registration')
    for label in ('statement', 'types', 'hypotheses', 'proved'):
        if 'riscv_encoder_correct_longmul_' + label not in registered[0]:
            raise ValueError('missing original LongMul evidence row: ' + label)
    return True
if __name__ == '__main__':
    check()
    print('Full original native LongMul constructor statement/evidence PASS')
