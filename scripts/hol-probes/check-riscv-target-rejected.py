#!/usr/bin/env python3
"""LongDiv rejected-case regression guard for the FP-free riscv-mi branch.

The asm FP carrier is removed here, so only the integer LongDiv case of the
original rejected cases remains in Lean, untagged. The captured original HOL
evidence for both the LongDiv and FP cases stays registered. Not an
equivalence proof."""
from pathlib import Path
import hashlib
ROOT=Path(__file__).resolve().parents[2]
CHECKS={'Flapjack/RiscV/CorrectnessEncoding/Rejected.lean': '0aff986199d334121de46ec1eddb0daeb73acf900568797f94981cfc0f48be19', 'scripts/hol-probes/riscv_target_rejected_probeScript.sml': '135c75fb0caa1a0beade62a11a9edc01c76949da3744402d6d0874a4e07c8f71', 'scripts/hol-probes/riscv_target_rejected_probe.out': 'eb43d93db01ba6504547cba69c1354f1ff68dd27362b060b4b910e855863267f', 'cakeml/compiler/encoders/asm/asmScript.sml': 'd445b1dcfe679c20f1429dfec4453b374d525c073abf636cdf9d631593638686', 'cakeml/compiler/encoders/asm/asmSemScript.sml': '47e614f8edb7c37cdcd7888a75ce2c564f3d81e1b994c9a2b156d9d4671bb092', 'cakeml/compiler/encoders/asm/asmPropsScript.sml': 'f14128fdbcf2479e74f26ccbd111850c78257e30e7b8b60bb750caeede956bfa', 'cakeml/compiler/encoders/riscv/riscv_targetScript.sml': 'e87d7e7b67bae40f96ac966209786bcaf4094df86abaa80552c22e6ecb533926'}
def check(root=ROOT):
    for name,digest in CHECKS.items():
        if hashlib.sha256((root/name).read_bytes()).hexdigest()!=digest:
            raise ValueError('full original rejected case/source/evidence drift: '+name)
    lean=(root/'Flapjack/RiscV/CorrectnessEncoding/Rejected.lean').read_text()
    if any(token in lean for token in ('HolFp','(.fp','asmFp','riscv_encoder_correct_fp')):
        raise ValueError('removed FP rejected case reappeared')
    if '@[hol' in lean:
        raise ValueError('restricted rejected case must not carry an exact HOL tag')
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
    print('LongDiv rejected case and original LongDiv/FP evidence PASS')
