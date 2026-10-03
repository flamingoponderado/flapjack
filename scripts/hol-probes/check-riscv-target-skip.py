#!/usr/bin/env python3
"""Pinned full original Skip case statement and original specialization evidence.
Syntactic regression only; Lean checks the proof and source review establishes shape.
"""
from pathlib import Path
import hashlib
import re
ROOT = Path(__file__).resolve().parents[2]
CHECKS = {'Flapjack/RiscV/CorrectnessEncoding/Skip.lean': 'cc6f3beb8e4be136da20d7cdb7ff0915a1ecb80e4ec611a40a338f37e273869b', 'cakeml/compiler/encoders/asm/asmPropsScript.sml': '3b295bd11d778523bad8673ff1be15e83ab12f63f2e3aee2b7796f1319465a39', 'scripts/hol-probes/riscv_target_skip_probeScript.sml': '9cd0f18a592b1c4c58774efaf71419f78819f80993943bd08ab997da585cb0f6', 'scripts/hol-probes/riscv_target_skip_probe.out': '50b6315f4b41aad22593f13c92d91c253ad5c9cbae1f5110e7b8dbe5c5faefb9'}
def check(root=ROOT):
    for name, expected in CHECKS.items():
        text = (root / name).read_text()
        if name.endswith('Skip.lean'):
            text = text.split('theorem riscv_encoder_correct_skip', 1)[1].split(' := by', 1)[0]
        elif name.endswith('asmPropsScript.sml'):
            text = text.split('Definition encoder_correct_def:', 1)[1].split('\nEnd', 1)[0]
        if hashlib.sha256(text.encode()).hexdigest() != expected:
            raise ValueError('full Skip original statement/evidence drift: ' + name)
    driver = (root / 'scripts/hol-probes/regenerate.sh').read_text()
    commands = driver.replace(chr(92) + chr(10), ' ').splitlines()
    registered = [c for c in commands if c.startswith('run_probe riscv_target_skip_probeScript.sml ')]
    if len(registered) != 1:
        raise ValueError('Skip probe must have one full registration')
    for label in ('statement', 'types', 'hypotheses', 'proved'):
        if 'riscv_encoder_correct_skip_' + label not in registered[0]:
            raise ValueError('missing original Skip evidence row: ' + label)
    return True
if __name__ == '__main__':
    check()
    print('Full original native Skip constructor statement/evidence PASS')
