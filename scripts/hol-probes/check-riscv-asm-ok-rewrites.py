#!/usr/bin/env python3
"""Full generated asm_ok statement/evidence regression; not an equivalence proof."""
from pathlib import Path
import hashlib
ROOT = Path(__file__).resolve().parents[2]
CHECKS = {'Flapjack/Compiler/Encoders/RiscV/Target/AsmOkRewrites.lean': 'd65469f00914f2711a646d8c8c62d0c3b4e292dd8d0446e3e80ae753cd3875d1', 'scripts/hol-probes/riscv_asm_ok_rewrites_probeScript.sml': 'f9b15ff1b468008d7e532601a3bb3fefc00847a9e488cfee0f24162870ac2874', 'scripts/hol-probes/riscv_asm_ok_rewrites_probe.out': '0ffced4507d08d5da5e12db1d79b529af9d9596a5d2f9e2b039bb1386f63b97c', 'cakeml/compiler/encoders/riscv/riscv_targetScript.sml': '9b9385038524f92fbe1066ca3c0b07358259a705fbaf59f3f185801efa85c14e'}
def check(root=ROOT):
    for name, expected in CHECKS.items():
        text = (root / name).read_text()
        if name.endswith('AsmOkRewrites.lean'):
            text = text.split('theorem riscvAsmOkRewrites',1)[1].split(' := by',1)[0]
            if text.count('asmOkExact ') != 41:
                raise ValueError('full original asm_ok requires all41 forms')
        elif name.endswith('riscv_targetScript.sml'):
            text = text.split('Definition riscv_config_def:',1)[1].split('\nEnd',1)[0]
        if hashlib.sha256(text.encode()).hexdigest() != expected:
            raise ValueError('full generated asm_ok statement/evidence drift: '+name)
    driver = (root / 'scripts/hol-probes/regenerate.sh').read_text()
    commands = driver.replace(chr(92)+chr(10),' ').splitlines()
    registered = [c for c in commands if c.startswith('run_probe riscv_asm_ok_rewrites_probeScript.sml ')]
    if len(registered) != 1:
        raise ValueError('asm_ok probe must have one complete registration')
    for label in ('statement','types','conjuncts','hypotheses','proved'):
        if 'riscv_asm_ok_full_'+label not in registered[0]:
            raise ValueError('missing original full asm_ok evidence: '+label)
    return True
if __name__ == '__main__':
    check()
    print('Full original41-clause riscv_asm_ok statement/evidence PASS')
