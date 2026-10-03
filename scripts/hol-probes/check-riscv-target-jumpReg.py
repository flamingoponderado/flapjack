#!/usr/bin/env python3
"""Pinned full original JumpReg case statement and original specialization evidence.
Syntactic regression only; Lean checks the proof and source review establishes shape.
"""
from pathlib import Path
import hashlib
import re
ROOT = Path(__file__).resolve().parents[2]
CHECKS = {'Flapjack/RiscV/CorrectnessEncoding/JumpReg.lean': '80d299bc3f034e277840bb2769a479c82ed875f5214ce0705ea3c1cd5067051e', 'cakeml/compiler/encoders/asm/asmPropsScript.sml': '3b295bd11d778523bad8673ff1be15e83ab12f63f2e3aee2b7796f1319465a39', 'scripts/hol-probes/riscv_target_jumpReg_probeScript.sml': '933669a6e3994e783c55f258c9bfe44ef7c728d1a7f629d4c3a9c6dee3219ad7', 'scripts/hol-probes/riscv_target_jumpReg_probe.out': '48ab88197c81dce1ed44e413e7f18fe33f4f76bf57c495901621cd7e5cd8eea0'}
def check(root=ROOT):
    for name, expected in CHECKS.items():
        text = (root / name).read_text()
        if name.endswith('JumpReg.lean'):
            text = text.split('theorem riscv_encoder_correct_jumpReg', 1)[1].split(' := by', 1)[0]
        elif name.endswith('asmPropsScript.sml'):
            text = text.split('Definition encoder_correct_def:', 1)[1].split('\nEnd', 1)[0]
        if hashlib.sha256(text.encode()).hexdigest() != expected:
            raise ValueError('full JumpReg original statement/evidence drift: ' + name)
    driver = (root / 'scripts/hol-probes/regenerate.sh').read_text()
    commands = driver.replace(chr(92) + chr(10), ' ').splitlines()
    registered = [c for c in commands if c.startswith('run_probe riscv_target_jumpReg_probeScript.sml ')]
    if len(registered) != 1:
        raise ValueError('JumpReg probe must have one full registration')
    for label in ('statement', 'types', 'hypotheses', 'proved'):
        if 'riscv_encoder_correct_jumpReg_' + label not in registered[0]:
            raise ValueError('missing original JumpReg evidence row: ' + label)
    return True
if __name__ == '__main__':
    check()
    print('Full original native JumpReg constructor statement/evidence PASS')
