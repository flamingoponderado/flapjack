#!/usr/bin/env python3
"""Source/evidence regression pins for untagged native Ror composition support.
Lean checks proofs; these pins do not prove cross-language equivalence.
"""
from pathlib import Path
import hashlib
ROOT = Path(__file__).resolve().parents[2]
CHECKS = {'Flapjack/RiscV/CorrectnessEncoding/RorStep.lean': '85bf94490a7d8be27f5db0585485d06abf2307cb4401a0c90018e8a262235ed7', 'scripts/hol-probes/riscv_ror_step_probeScript.sml': 'c295fea900ef3b08be9d86a6ede3c090f85954398ba967ce6ac54a1829a8eac9', 'scripts/hol-probes/riscv_ror_step_probe.out': '048e4aeb2baa534fc1d31e18028bf7c4b64f19c5247f5aa775a5f34a7ff42055'}
LABELS = ['ror_run_srli_clause', 'ror_run_srli_types', 'ror_run_srli_hypotheses', 'ror_run_sll_clause', 'ror_run_sll_types', 'ror_run_sll_hypotheses', 'ror_run_srl_clause', 'ror_run_srl_types', 'ror_run_srl_hypotheses', 'ror_run_sub_clause', 'ror_run_sub_types', 'ror_run_sub_hypotheses', 'ror_next_srli_zero', 'ror_next_srli_all_ones', 'ror_next_sll_zero', 'ror_next_sll_all_ones', 'ror_next_srl_zero', 'ror_next_srl_all_ones', 'ror_next_sub_zero', 'ror_next_sub_all_ones']
def check(root=ROOT):
    for path, expected in CHECKS.items():
        if hashlib.sha256((root/path).read_bytes()).hexdigest() != expected:
            raise ValueError("native Ror composition/evidence drift: " + path)
    commands = (root/'scripts/hol-probes/regenerate.sh').read_text().replace(chr(92)+chr(10), ' ').splitlines()
    entries = [line for line in commands if line.startswith('run_probe riscv_ror_step_probeScript.sml ')]
    if len(entries) != 1 or any(label not in entries[0].split() for label in LABELS):
        raise ValueError('native Ror probe requires one complete registration')
    return True
if __name__ == '__main__':
    check()
    print('Native Ror support and original scoped evidence PASS')
