#!/usr/bin/env python3
"""Pinned full original native encoder theorem statement and original specialization evidence.
Syntactic regression only; Lean checks the proof and source review establishes shape.
"""
from pathlib import Path
import hashlib
ROOT = Path(__file__).resolve().parents[2]
CHECKS = {'Flapjack/RiscV/CorrectnessEncoding/Complete.lean': 'b135e04356842d2b697374ed9f2472327b83902753e8c8aad0108f3686add33b', 'scripts/hol-probes/riscv_target_complete_probeScript.sml': '78764512c392bd469a258b4543d930c9faafe2d98ef8498b04801ff8f57581a2', 'scripts/hol-probes/riscv_target_complete_probe.out': '78f4d4c1b087cfdb4b2a5b537537000930e9b1b9b12f0380b31b1b337a5363d2', 'Flapjack/Compiler/Encoders/AsmProps/EncoderCorrect.lean': 'e68c1c5f42c5e1f6a77eba68da2306d20eef69f344f893982f03522c17b3603b', 'cakeml/compiler/encoders/asm/asmPropsScript.sml': '3b295bd11d778523bad8673ff1be15e83ab12f63f2e3aee2b7796f1319465a39'}
def check(root=ROOT):
    for name, expected in CHECKS.items():
        text = (root / name).read_text()
        if name.endswith('Complete.lean'):
            text = text.split('theorem riscv_encoder_correct', 1)[1].split(' := by', 1)[0]
        elif name.endswith('EncoderCorrect.lean'):
            text = text.split('noncomputable def encoderCorrect', 1)[1].split('\n/--', 1)[0]
        elif name.endswith('asmPropsScript.sml'):
            text = text.split('Definition encoder_correct_def:', 1)[1].split('\nEnd', 1)[0]
        if hashlib.sha256(text.encode()).hexdigest() != expected:
            raise ValueError('full native encoder original statement/evidence drift: ' + name)
    driver = (root / 'scripts/hol-probes/regenerate.sh').read_text()
    commands = driver.replace(chr(92) + chr(10), ' ').splitlines()
    registered = [c for c in commands if c.startswith('run_probe riscv_target_complete_probeScript.sml ')]
    if len(registered) != 1:
        raise ValueError('Complete encoder probe must have one full registration')
    for label in ('statement', 'expanded', 'hypotheses', 'proved'):
        if 'riscv_encoder_correct_' + label not in registered[0]:
            raise ValueError('missing complete encoder evidence row: ' + label)
    return True
if __name__ == '__main__':
    check()
    print('Full original native encoder theorem statement/evidence PASS')
