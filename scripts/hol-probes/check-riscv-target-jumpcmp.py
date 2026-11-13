#!/usr/bin/env python3
"""Pinned full original JumpCmp case statement and original specialization evidence.
Syntactic regression only; Lean checks the proof and source review establishes shape.
"""
from pathlib import Path
import hashlib
import re
ROOT = Path(__file__).resolve().parents[2]
CHECKS = {'Flapjack/RiscV/CorrectnessEncoding/JumpCmp.lean': '2b17d59b01cd4e88838d5f5605159b3a02dd5414a03af70cb4a219acd75b5aee', 'Flapjack/RiscV/CorrectnessEncoding/JumpCmp/Arithmetic.lean': 'df90b5d08dcc456f85adc9207f2bcf0804a6645f0b3515b44db7a213aaa0db99', 'Flapjack/RiscV/CorrectnessEncoding/JumpCmp/Comparison.lean': 'ddefc66fdf19fdbc47c2f20290a8c2c9963e041c22e185c9878bab7442fc68f6', 'Flapjack/RiscV/CorrectnessEncoding/JumpCmp/Encoding.lean': '848568e83b5190e4cc04f473bef1c4510a978be8ec015559a1331279ceb62fe1', 'Flapjack/RiscV/CorrectnessEncoding/JumpCmp/FarImm.lean': '60db1895da9a03f498f21104bfc9460ccd3ba3c5b2c919659bfbdee2c7ffbcc8', 'Flapjack/RiscV/CorrectnessEncoding/JumpCmp/FarNative.lean': '27adf8e088155f1319cdc0fd38af44b22a3fcff1b5dfe4046c5f9da93cf8b585', 'Flapjack/RiscV/CorrectnessEncoding/JumpCmp/FarReg.lean': '2866841d477812d97369ef2a6602aaee47838b53d5992ae7a796e35e1e371874', 'Flapjack/RiscV/CorrectnessEncoding/JumpCmp/FarRegTest.lean': '9677bc0f4067cebd6474c49ae98b9eda7d578095518124abd705e060e21d3f20', 'Flapjack/RiscV/CorrectnessEncoding/JumpCmp/Native.lean': '62d66c4bd1eb122b065a5c784face3d28395fe4a17d17b4370a9ce65be160991', 'Flapjack/RiscV/CorrectnessEncoding/Skip.lean': '44117f00633d330a389c61b27b356e5c06bee258bfef6ee09ac52a71c11ebea8', 'Flapjack/RiscV/CorrectnessEncoding/JumpCmp/Near.lean': '0fe2ca0c9b7f019c1c18708169655b885be701aa0a597fad1ccb1275884e3949', 'Flapjack/RiscV/CorrectnessEncoding/JumpCmp/NearImm.lean': 'd604e506f7c0310da9ddbaaff4a65bb7dc473cdc1e40fc4da9d5bf58788427bd', 'Flapjack/RiscV/CorrectnessEncoding/JumpCmp/NearReg.lean': '5071cd8d01903f38c2dc1f0381f6d0a793322c1e398a50f40df264c4d10bbb6d', 'Flapjack/RiscV/CorrectnessEncoding/JumpCmp/NearRegTest.lean': '909a1ef5855f110fe9e495d3764d0146c4204d5c0be338a7850f5757786b2c0b', 'Flapjack/RiscV/CorrectnessEncoding/JumpCmp/Prefix.lean': '569383e07ee63858ddd48a0425ff86b4b6f46a446df5c075af5d3f8539ba151d', 'Flapjack/RiscV/CorrectnessEncoding/JumpCmp/Source.lean': 'f66da8f8a189e90f1c427599a86423edead6472c47ead7ebf6e2d38171d8e939', 'cakeml/compiler/encoders/asm/asmPropsScript.sml': '3b295bd11d778523bad8673ff1be15e83ab12f63f2e3aee2b7796f1319465a39', 'scripts/hol-probes/riscv_target_jumpcmp_probeScript.sml': '3a500b606c7195557749897a0dd8844df286a75ea1686b64f45d46d748b8ff85', 'scripts/hol-probes/riscv_target_jumpcmp_probe.out': 'c61bc641bdba93cac7f1bf039aeff29e93463cdf13c7f6bc630c0ec3449cd35b'}
def check(root=ROOT):
    for name, expected in CHECKS.items():
        text = (root / name).read_text()
        if name.endswith('JumpCmp.lean'):
            text = text.split('theorem riscv_encoder_correct_jumpCmp', 1)[1].split(' := by', 1)[0]
        elif name.endswith('asmPropsScript.sml'):
            text = text.split('Definition encoder_correct_def:', 1)[1].split('\nEnd', 1)[0]
        if hashlib.sha256(text.encode()).hexdigest() != expected:
            raise ValueError('full JumpCmp original statement/evidence drift: ' + name)
    driver = (root / 'scripts/hol-probes/regenerate.sh').read_text()
    commands = driver.replace(chr(92) + chr(10), ' ').splitlines()
    registered = [c for c in commands if c.startswith('run_probe riscv_target_jumpcmp_probeScript.sml ')]
    if len(registered) != 1:
        raise ValueError('JumpCmp probe must have one full registration')
    for label in ('statement', 'types', 'hypotheses', 'proved'):
        if 'riscv_encoder_correct_jumpcmp_' + label not in registered[0]:
            raise ValueError('missing original JumpCmp evidence row: ' + label)
    return True
if __name__ == '__main__':
    check()
    print('Full original native JumpCmp constructor statement/evidence PASS')
