#!/usr/bin/env python3
"""Pinned full original Call case statement and original specialization evidence.
Syntactic regression only; Lean checks the proof and source review establishes shape.
"""
from pathlib import Path
import hashlib
import re
ROOT = Path(__file__).resolve().parents[2]
CHECKS = {'Flapjack/RiscV/CorrectnessEncoding/Call.lean': 'b5323dfad61ba624025bcf21079486e2d5ca260325e98047991770fa2391e905', 'Flapjack/RiscV/CorrectnessEncoding/Call/Native.lean': 'a09ebffeb6dcc56f73c79a4960e4a330c509a6a28f6245546631035b71835786', 'Flapjack/RiscV/CorrectnessEncoding/Call/Near.lean': 'd5455df4c08d5ca84939f8e91165e2875057414c40378604caee62310ca2e2ff', 'Flapjack/RiscV/CorrectnessEncoding/Call/Far.lean': 'ea9e90bbc7d78a863c80bc4f2c7c007080e6a3db8316d2cdfddf44ac83f0a411', 'cakeml/compiler/encoders/asm/asmPropsScript.sml': '3b295bd11d778523bad8673ff1be15e83ab12f63f2e3aee2b7796f1319465a39', 'scripts/hol-probes/riscv_target_call_probeScript.sml': 'e365d6faa958d90542e703500500eed69e6cf8df3ccf1242852547c82287757f', 'scripts/hol-probes/riscv_target_call_probe.out': '30aaaf6cca1920fe6ada906aa5075ba3ab4ca768085b5c60d2c8cd7e0c692227'}
def check(root=ROOT):
    for name, expected in CHECKS.items():
        text = (root / name).read_text()
        if name.endswith('Call.lean'):
            text = text.split('theorem riscv_encoder_correct_call', 1)[1].split(' := by', 1)[0]
        elif name.endswith('asmPropsScript.sml'):
            text = text.split('Definition encoder_correct_def:', 1)[1].split('\nEnd', 1)[0]
        if hashlib.sha256(text.encode()).hexdigest() != expected:
            raise ValueError('full Call original statement/evidence drift: ' + name)
    driver = (root / 'scripts/hol-probes/regenerate.sh').read_text()
    commands = driver.replace(chr(92) + chr(10), ' ').splitlines()
    registered = [c for c in commands if c.startswith('run_probe riscv_target_call_probeScript.sml ')]
    if len(registered) != 1:
        raise ValueError('Call probe must have one full registration')
    for label in ('statement', 'types', 'hypotheses', 'proved'):
        if 'riscv_encoder_correct_call_' + label not in registered[0]:
            raise ValueError('missing original Call evidence row: ' + label)
    return True
if __name__ == '__main__':
    check()
    print('Full original native Call constructor statement/evidence PASS')
