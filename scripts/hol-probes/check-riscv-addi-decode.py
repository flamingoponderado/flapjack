#!/usr/bin/env python3
"""Pinned unrestricted ADDI composition signature and original ground oracles.
Syntactic regression only; Lean checks the proof and source review establishes shape.
"""
from pathlib import Path
import hashlib
ROOT = Path(__file__).resolve().parents[2]
CHECKS = {'Flapjack/RiscV/CorrectnessEncoding/DecodeAddi.lean': '1479ec298009eba758079d02a0ddc521a3177268c174f59b099b013e7f5afa99', 'scripts/hol-probes/riscv_addi_decode_probeScript.sml': '130ac37122e3cbe7a6e298dd4e4d5a827030b7aafe945b9382fc471f5429d3ce', 'scripts/hol-probes/riscv_addi_decode_probe.out': 'd140d2daf5d41250d06f795e36239942e1f05a1a5a0c23656cb8fc283434ce71'}
def check(root=ROOT):
    for name, expected in CHECKS.items():
        text = (root / name).read_text()
        if name.endswith('DecodeAddi.lean'):
            text = text.split('theorem decode_encode_addi', 1)[1].split(' := by', 1)[0]
        if hashlib.sha256(text.encode()).hexdigest() != expected:
            raise ValueError('full ADDI original statement/evidence drift: ' + name)
    driver = (root / 'scripts/hol-probes/regenerate.sh').read_text()
    commands = driver.replace(chr(92) + chr(10), ' ').splitlines()
    registered = [c for c in commands if c.startswith('run_probe riscv_addi_decode_probeScript.sml ')]
    if len(registered) != 1:
        raise ValueError('ADDI probe must have one full registration')
    for label in ('zero', 'all_ones', 'sign_bit', 'positive_max'):
        if 'addi_decode_' + label not in registered[0]:
            raise ValueError('missing original ADDI evidence row: ' + label)
    return True
if __name__ == '__main__':
    check()
    print('Full original native ADDI full-domain statement/boundary evidence PASS')
