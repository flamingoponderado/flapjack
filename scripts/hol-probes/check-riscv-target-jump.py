#!/usr/bin/env python3
"""Pinned full original Jump case statement and original specialization evidence.
Syntactic regression only; Lean checks the proof and source review establishes shape.
"""
from pathlib import Path
import hashlib
import re
ROOT = Path(__file__).resolve().parents[2]
CHECKS = {'Flapjack/RiscV/CorrectnessEncoding/Jump.lean': 'bc896643b0a56f1c69b9f6da808cc64eafa11aeb8d81575d0ffbcb4bc701df08', 'Flapjack/RiscV/CorrectnessEncoding/Jump/Native.lean': '40d985f0a14fcf406bb844b8382eb0e638f6bc577286ab9624dfc0baa3dd0039', 'Flapjack/RiscV/CorrectnessEncoding/Jump/Near.lean': '41f45ab5ae7d8c2f671f6f60dd506d5836bd272e8a6cd010661777cafd31e9e3', 'Flapjack/RiscV/CorrectnessEncoding/Jump/Far.lean': 'cf3d7da1b6bbb4922a57cfdf97df5fd93d73faecae3d44f534d242068ecc6b35', 'Flapjack/RiscV/CorrectnessEncoding/Skip.lean': '1209ac0c00ce51a2b8fce4c7c01f3ff326a70816669432b2c6a0200607984d2f', 'Flapjack/RiscV/CorrectnessEncoding/InstructionStep.lean': '2fa64bc6c267eefa46b7a9547c6b7d3f5b531b220d5b6303ba8861a13d9f2f2a', 'cakeml/compiler/encoders/asm/asmPropsScript.sml': '3b295bd11d778523bad8673ff1be15e83ab12f63f2e3aee2b7796f1319465a39', 'scripts/hol-probes/riscv_target_jump_probeScript.sml': '0cbd2a6b3724cce55b7d58f9fe7774093ddf7f517f4864e4903a6cd44b780b60', 'scripts/hol-probes/riscv_target_jump_probe.out': '8c1f3bfa2880b673990b862e1aaa8a76335418e832e1d49de3dc47540d7ff4e5'}
def check(root=ROOT):
    for name, expected in CHECKS.items():
        text = (root / name).read_text()
        if name.endswith('Jump.lean'):
            text = text.split('theorem riscv_encoder_correct_jump', 1)[1].split(' := by', 1)[0]
        elif name.endswith('asmPropsScript.sml'):
            text = text.split('Definition encoder_correct_def:', 1)[1].split('\nEnd', 1)[0]
        if hashlib.sha256(text.encode()).hexdigest() != expected:
            raise ValueError('full Jump original statement/evidence drift: ' + name)
    driver = (root / 'scripts/hol-probes/regenerate.sh').read_text()
    commands = driver.replace(chr(92) + chr(10), ' ').splitlines()
    registered = [c for c in commands if c.startswith('run_probe riscv_target_jump_probeScript.sml ')]
    if len(registered) != 1:
        raise ValueError('Jump probe must have one full registration')
    for label in ('statement', 'types', 'hypotheses', 'proved'):
        if 'riscv_encoder_correct_jump_' + label not in registered[0]:
            raise ValueError('missing original Jump evidence row: ' + label)
    return True
if __name__ == '__main__':
    check()
    print('Full original native Jump constructor statement/evidence PASS')
