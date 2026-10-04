#!/usr/bin/env python3
"""Pinned full original Mem case statement and original specialization evidence.
Syntactic regression only; Lean checks the proof and source review establishes shape.
"""
from pathlib import Path
import hashlib
ROOT = Path(__file__).resolve().parents[2]
CHECKS = {'Flapjack/RiscV/CorrectnessEncoding/MemoryAssertions.lean': 'ca4def86c11b5746b99ff2ea5bbbaf150469954296ab4d8bed70dbefc265814f', 'scripts/hol-probes/riscv_target_mem_probeScript.sml': '75e1ed035c9300f688257a8dfb47506d96f7f74c0bf360b22685528fbf14c0bd', 'scripts/hol-probes/riscv_target_mem_probe.out': '322ff82febe4df0fedcd7c1b83a6c28706e1fbdbcff65777898bf97107781c7b', 'cakeml/compiler/encoders/asm/asmPropsScript.sml': '3b295bd11d778523bad8673ff1be15e83ab12f63f2e3aee2b7796f1319465a39'}
def check(root=ROOT):
    for name, expected in CHECKS.items():
        text = (root / name).read_text()
        if name.endswith('MemoryAssertions.lean'):
            text = text.split('theorem riscv_encoder_correct_mem', 1)[1].split(' := by', 1)[0]
        elif name.endswith('asmPropsScript.sml'):
            text = text.split('Definition encoder_correct_def:', 1)[1].split('\nEnd', 1)[0]
        if hashlib.sha256(text.encode()).hexdigest() != expected:
            raise ValueError('full Mem original statement/evidence drift: ' + name)
    driver = (root / 'scripts/hol-probes/regenerate.sh').read_text()
    commands = driver.replace(chr(92) + chr(10), ' ').splitlines()
    registered = [c for c in commands if c.startswith('run_probe riscv_target_mem_probeScript.sml ')]
    if len(registered) != 1:
        raise ValueError('Mem probe must have one full registration')
    for label in ('statement', 'types', 'hypotheses', 'proved'):
        if 'riscv_encoder_correct_mem_' + label not in registered[0]:
            raise ValueError('missing original Mem evidence row: ' + label)
    return True
if __name__ == '__main__':
    check()
    print('Full original native Mem constructor statement/evidence PASS')
