#!/usr/bin/env python3
"""Restricted asm_ok statement and full original evidence regression.

riscv-mi removes the asm FP carrier, so the Lean bundle keeps exactly the 25
integer conjuncts of the original 41-clause statement (the sixteen FP rejection
clauses are absent) and is not tagged as the exact HOL theorem. The captured
HOL evidence still records the complete original 41-clause statement. This is
not an equivalence proof."""
from pathlib import Path
import hashlib
ROOT = Path(__file__).resolve().parents[2]
CHECKS = {'Flapjack/Compiler/Encoders/RiscV/Target/AsmOkRewrites.lean': '23f1026ab3a7663e8d78896305c6ba0d01923eba3616ee6b449a4215954ccbb9', 'scripts/hol-probes/riscv_asm_ok_rewrites_probeScript.sml': 'f9b15ff1b468008d7e532601a3bb3fefc00847a9e488cfee0f24162870ac2874', 'scripts/hol-probes/riscv_asm_ok_rewrites_probe.out': '0ffced4507d08d5da5e12db1d79b529af9d9596a5d2f9e2b039bb1386f63b97c', 'cakeml/compiler/encoders/riscv/riscv_targetScript.sml': '9b9385038524f92fbe1066ca3c0b07358259a705fbaf59f3f185801efa85c14e'}
# Original 41 conjuncts minus the sixteen FP rejection clauses.
INTEGER_FORMS = 25
FP_TOKENS = ('.fp ', '(.fp', 'HolFp', 'asmFp', ' d1 ', ' d2 ', ' d3 ')
def check(root=ROOT):
    for name, expected in CHECKS.items():
        text = (root / name).read_text()
        if name.endswith('AsmOkRewrites.lean'):
            header, text = text.split('theorem riscvAsmOkRewrites',1)
            if '@[hol' in header.rsplit('-/',1)[-1]:
                raise ValueError('restricted asm_ok bundle must not carry an exact HOL tag')
            text = text.split(' := by',1)[0]
            if text.count('asmOkExact ') != INTEGER_FORMS:
                raise ValueError('restricted asm_ok requires all%d integer forms' % INTEGER_FORMS)
            if any(token in text for token in FP_TOKENS):
                raise ValueError('restricted asm_ok must not mention removed FP forms')
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
    print('Restricted 25-clause riscv_asm_ok statement and original41-clause evidence PASS')
