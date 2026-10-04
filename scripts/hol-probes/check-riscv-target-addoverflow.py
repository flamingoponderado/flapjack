#!/usr/bin/env python3
"""Pinned full original AddOverflow case statement and original specialization evidence.
Syntactic regression only; Lean checks the proof and source review establishes shape.
"""
from pathlib import Path
import hashlib
import re
ROOT = Path(__file__).resolve().parents[2]
CHECKS = {'Flapjack/RiscV/CorrectnessEncoding/AddOverflow.lean': 'b2e0f683749ff93572a6528f95d19d624827d03e153be6a3a4c598e8a15f938e', 'cakeml/compiler/encoders/asm/asmPropsScript.sml': '3b295bd11d778523bad8673ff1be15e83ab12f63f2e3aee2b7796f1319465a39', 'scripts/hol-probes/riscv_target_addoverflow_probeScript.sml': '0895b0bd7b76c56f2bc77ab6b8c8b0468eb0abb93d407f2ba4445d0c3b838a4f', 'scripts/hol-probes/riscv_target_addoverflow_probe.out': '7b2b8c70ffe8d98fd6e778794e66f639a4af446a6d408b9470fcffa8133071bc', 'Flapjack/RiscV/CorrectnessEncoding/AddOverflow/Post.lean': '673fde5c24cc106f7dd4713c95b891f2cae299794d8fbd09970942457feac637'}
def check(root=ROOT):
    for name, expected in CHECKS.items():
        text = (root / name).read_text()
        if name.endswith('AddOverflow.lean'):
            text = text.split('theorem riscv_encoder_correct_addoverflow', 1)[1].split(' := by', 1)[0]
        elif name.endswith('Post.lean'):
            text = text.split('def program', 1)[1].split('/--', 1)[0]
        elif name.endswith('asmPropsScript.sml'):
            text = text.split('Definition encoder_correct_def:', 1)[1].split('\nEnd', 1)[0]
        if hashlib.sha256(text.encode()).hexdigest() != expected:
            raise ValueError('full AddOverflow original statement/evidence drift: ' + name)
    driver = (root / 'scripts/hol-probes/regenerate.sh').read_text()
    commands = driver.replace(chr(92) + chr(10), ' ').splitlines()
    registered = [c for c in commands if c.startswith('run_probe riscv_target_addoverflow_probeScript.sml ')]
    if len(registered) != 1:
        raise ValueError('AddOverflow probe must have one full registration')
    for label in ('statement', 'types', 'hypotheses', 'proved'):
        if 'riscv_encoder_correct_addoverflow_' + label not in registered[0]:
            raise ValueError('missing original AddOverflow evidence row: ' + label)
    return True
if __name__ == '__main__':
    check()
    print('Full original native AddOverflow constructor statement/evidence PASS')
