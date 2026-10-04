#!/usr/bin/env python3
"""Pinned full original SubOverflow case statement and original specialization evidence.
Syntactic regression only; Lean checks the proof and source review establishes shape.
"""
from pathlib import Path
import hashlib
import re
ROOT = Path(__file__).resolve().parents[2]
CHECKS = {'Flapjack/RiscV/CorrectnessEncoding/SubOverflow.lean': '2f15094b402b96aee6c2c0eda76310881d461a0c05f1b422a0486326fbcff6fd', 'cakeml/compiler/encoders/asm/asmPropsScript.sml': '3b295bd11d778523bad8673ff1be15e83ab12f63f2e3aee2b7796f1319465a39', 'scripts/hol-probes/riscv_target_suboverflow_probeScript.sml': '0dccef068c132945abcf3003973259fab14347b7eb110a8afc32116ee3e770e1', 'scripts/hol-probes/riscv_target_suboverflow_probe.out': '405982f684aa190016e0863015e3493a078a7e1240f1314772a1605f6fe12c4f', 'Flapjack/RiscV/CorrectnessEncoding/SubOverflow/Post.lean': '8091ac1259a0a4a3c685c96f7c11e9ee4acfa3a0ab1f7ef5cbf63832d52e428c'}
def check(root=ROOT):
    for name, expected in CHECKS.items():
        text = (root / name).read_text()
        if name.endswith('SubOverflow.lean'):
            text = text.split('theorem riscv_encoder_correct_suboverflow', 1)[1].split(' := by', 1)[0]
        elif name.endswith('Post.lean'):
            text = text.split('def program', 1)[1].split('/--', 1)[0]
        elif name.endswith('asmPropsScript.sml'):
            text = text.split('Definition encoder_correct_def:', 1)[1].split('\nEnd', 1)[0]
        if hashlib.sha256(text.encode()).hexdigest() != expected:
            raise ValueError('full SubOverflow original statement/evidence drift: ' + name)
    driver = (root / 'scripts/hol-probes/regenerate.sh').read_text()
    commands = driver.replace(chr(92) + chr(10), ' ').splitlines()
    registered = [c for c in commands if c.startswith('run_probe riscv_target_suboverflow_probeScript.sml ')]
    if len(registered) != 1:
        raise ValueError('SubOverflow probe must have one full registration')
    for label in ('statement', 'types', 'hypotheses', 'proved'):
        if 'riscv_encoder_correct_suboverflow_' + label not in registered[0]:
            raise ValueError('missing original SubOverflow evidence row: ' + label)
    return True
if __name__ == '__main__':
    check()
    print('Full original native SubOverflow constructor statement/evidence PASS')
