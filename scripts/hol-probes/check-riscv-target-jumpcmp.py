#!/usr/bin/env python3
"""Pinned full original JumpCmp case statement and original specialization evidence.
Syntactic regression only; Lean checks the proof and source review establishes shape.
"""
from pathlib import Path
import hashlib
import re
ROOT = Path(__file__).resolve().parents[2]
CHECKS = {'Flapjack/RiscV/CorrectnessEncoding/JumpCmp.lean': '2b17d59b01cd4e88838d5f5605159b3a02dd5414a03af70cb4a219acd75b5aee', 'Flapjack/RiscV/CorrectnessEncoding/JumpCmp/Arithmetic.lean': 'd4a85dfc0b1c86d028c6c12e0c80f24c0edd0c6cb5678c1351b6761d17394492', 'Flapjack/RiscV/CorrectnessEncoding/JumpCmp/Comparison.lean': 'da0f2201ff5464a06efccdc31374b98265072a9e860d63e045c77e5e068fdc30', 'Flapjack/RiscV/CorrectnessEncoding/JumpCmp/Encoding.lean': '0451223ee4a6e79a1d456147894a68995be670ae58a8bead751a73d26876ee79', 'Flapjack/RiscV/CorrectnessEncoding/JumpCmp/FarImm.lean': 'a6f93909a15a49da180a02a2c35be84deb3a7120b782e4b65716430e82454a99', 'Flapjack/RiscV/CorrectnessEncoding/JumpCmp/FarNative.lean': 'b45459f3665c2fb68002f1132ba78ec110de3402e77ed57d4a414f81c105d2c0', 'Flapjack/RiscV/CorrectnessEncoding/JumpCmp/FarReg.lean': '4d49b0fc5a01710205569562f7bc1fbfbb4990b6af94b5db62754aaa125da67c', 'Flapjack/RiscV/CorrectnessEncoding/JumpCmp/FarRegTest.lean': '1a8843d1d2357dcbc5303a8711ce780835a620a2f96cd98317322220c7816855', 'Flapjack/RiscV/CorrectnessEncoding/JumpCmp/Native.lean': '96c1ba6baa1b7195b126346f1fd8a39c2c0ff43dafbe733d9d84492601de96cd', 'Flapjack/RiscV/CorrectnessEncoding/JumpCmp/Near.lean': 'bb197b7634e5538ac916f8661a67f1b4cd5eea122aa8e0aa518dfffd13392885', 'Flapjack/RiscV/CorrectnessEncoding/JumpCmp/NearImm.lean': 'd585e27388d6f92a67059e2ae60d1fd500473005e464969eb91dfe5ff3dd881a', 'Flapjack/RiscV/CorrectnessEncoding/JumpCmp/NearReg.lean': '7925070f9483c120b78b053569fc41cb1eb259f3a117dd03a94841e636cad35f', 'Flapjack/RiscV/CorrectnessEncoding/JumpCmp/NearRegTest.lean': '2b751d856ed26f07b42c9a3c0883ce56e1ba165e5e7b7dc55e8ed4ab80b9e176', 'Flapjack/RiscV/CorrectnessEncoding/JumpCmp/Prefix.lean': '0299d026cea55145ae775bc1d7a304fb30e5ecda598e91e55c1f4087bccded04', 'Flapjack/RiscV/CorrectnessEncoding/JumpCmp/Source.lean': '634ec7efe9aa51ec053963e574a84525d1758e75987a9c281c13b2d8d52ef168', 'cakeml/compiler/encoders/asm/asmPropsScript.sml': '3b295bd11d778523bad8673ff1be15e83ab12f63f2e3aee2b7796f1319465a39', 'scripts/hol-probes/riscv_target_jumpcmp_probeScript.sml': '3a500b606c7195557749897a0dd8844df286a75ea1686b64f45d46d748b8ff85', 'scripts/hol-probes/riscv_target_jumpcmp_probe.out': 'c61bc641bdba93cac7f1bf039aeff29e93463cdf13c7f6bc630c0ec3449cd35b'}
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
