#!/usr/bin/env python3
"""Pinned full original Jump case statement and original specialization evidence.
Syntactic regression only; Lean checks the proof and source review establishes shape.
"""
from pathlib import Path
import hashlib
import re
ROOT = Path(__file__).resolve().parents[2]
CHECKS = {'Flapjack/RiscV/CorrectnessEncoding/Jump.lean': 'bc896643b0a56f1c69b9f6da808cc64eafa11aeb8d81575d0ffbcb4bc701df08', 'Flapjack/RiscV/CorrectnessEncoding/Jump/Native.lean': 'a6ef3f2594450b292651d8c98e3346e1e3cc93199483579c354ef58cab11e49a', 'Flapjack/RiscV/CorrectnessEncoding/Jump/Near.lean': '52f5851c00b1a90f8ddc4abb189cde37a81afd17efdaae06ecaeae196bba7aa7', 'Flapjack/RiscV/CorrectnessEncoding/Jump/Far.lean': 'ef9138a100108755a93d873cf240ddd97d08fdd069f919133d2183328feb8f68', 'Flapjack/RiscV/CorrectnessEncoding/Skip.lean': '44117f00633d330a389c61b27b356e5c06bee258bfef6ee09ac52a71c11ebea8', 'Flapjack/RiscV/CorrectnessEncoding/InstructionStep.lean': '443c2218c14e85d5165e588fe75b22f0c9c3707e4db842fb0a5f53a99ede5adf', 'cakeml/compiler/encoders/asm/asmPropsScript.sml': '3b295bd11d778523bad8673ff1be15e83ab12f63f2e3aee2b7796f1319465a39', 'scripts/hol-probes/riscv_target_jump_probeScript.sml': '0cbd2a6b3724cce55b7d58f9fe7774093ddf7f517f4864e4903a6cd44b780b60', 'scripts/hol-probes/riscv_target_jump_probe.out': '8c1f3bfa2880b673990b862e1aaa8a76335418e832e1d49de3dc47540d7ff4e5'}
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
