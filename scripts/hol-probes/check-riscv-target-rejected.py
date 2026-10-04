#!/usr/bin/env python3
"""Complete LongDiv/FP original case regression guard; not equivalence proof."""
from pathlib import Path
import hashlib
ROOT=Path(__file__).resolve().parents[2]
CHECKS={'Flapjack/RiscV/CorrectnessEncoding/Rejected.lean': 'a055ebbeb0061da6d9b14732921085a9f309063bdaf08a895d896b43897b41f6', 'scripts/hol-probes/riscv_target_rejected_probeScript.sml': '135c75fb0caa1a0beade62a11a9edc01c76949da3744402d6d0874a4e07c8f71', 'scripts/hol-probes/riscv_target_rejected_probe.out': 'eb43d93db01ba6504547cba69c1354f1ff68dd27362b060b4b910e855863267f', 'cakeml/compiler/encoders/asm/asmScript.sml': 'd445b1dcfe679c20f1429dfec4453b374d525c073abf636cdf9d631593638686', 'cakeml/compiler/encoders/asm/asmSemScript.sml': '47e614f8edb7c37cdcd7888a75ce2c564f3d81e1b994c9a2b156d9d4671bb092', 'cakeml/compiler/encoders/asm/asmPropsScript.sml': 'f14128fdbcf2479e74f26ccbd111850c78257e30e7b8b60bb750caeede956bfa', 'cakeml/compiler/encoders/riscv/riscv_targetScript.sml': 'e87d7e7b67bae40f96ac966209786bcaf4094df86abaa80552c22e6ecb533926'}
def check(root=ROOT):
    for name,digest in CHECKS.items():
        if hashlib.sha256((root/name).read_bytes()).hexdigest()!=digest:
            raise ValueError('full original rejected case/source/evidence drift: '+name)
    if 'import Flapjack.RiscV.CorrectnessEncoding.Rejected' not in (root/'Flapjack.lean').read_text().splitlines():
        raise ValueError('missing full case root import')
    commands=(root/'scripts/hol-probes/regenerate.sh').read_text().replace(chr(92)+chr(10),' ').splitlines()
    registered=[c for c in commands if c.startswith('run_probe riscv_target_rejected_probeScript.sml ')]
    if len(registered)!=1:
        raise ValueError('must register one complete original case capture')
    for case in ('longdiv','fp'):
        for suffix in ('statement','types','hypotheses','proved'):
            if 'riscv_encoder_correct_'+case+'_'+suffix not in registered[0]:
                raise ValueError('missing full original case evidence: '+case+'_'+suffix)
    return True
if __name__=='__main__':
    check()
    print('Full original LongDiv and all sixteen FP encoder cases/source/evidence PASS')
