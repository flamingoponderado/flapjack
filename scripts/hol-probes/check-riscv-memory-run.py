#!/usr/bin/env python3
"""Pin source-reviewed full native memory composition and original regression evidence."""
from pathlib import Path
import hashlib
ROOT = Path(__file__).resolve().parents[2]
CHECKS = {'Flapjack/RiscV/CorrectnessEncoding/MemoryRun.lean': 'e939a9ca949fd11723c3546ec74ae3b879d5c0417aaafeaf65427a8f92221709', 'scripts/hol-probes/riscv_memory_run_probeScript.sml': 'a98d174e68911d1a7bb2e493cbbefd8ece9cbadaeda7a195e7dc56701ccacd35', 'scripts/hol-probes/riscv_memory_run_probe.out': '4ef700c9866935d3a242227356a1e1b615263d71ed8f2fb99aed2b1b5034da73'}
def check(root=ROOT):
    for name, digest in CHECKS.items():
        if hashlib.sha256((root / name).read_bytes()).hexdigest() != digest:
            raise ValueError('native memory original statement/evidence drift: ' + name)
    commands = (root / 'scripts/hol-probes/regenerate.sh').read_text().replace(chr(92)+chr(10), ' ').splitlines()
    rows = [s for s in commands if s.startswith('run_probe riscv_memory_run_probeScript.sml ')]
    if len(rows) != 1:
        raise ValueError('memory requires one complete original registration')
    for label in ('ld_run_zero', 'ld_run_alias_sign', 'ld_run_basezero_unaligned', 'lwu_run_zero', 'lwu_run_alias_sign', 'lwu_run_basezero_unaligned', 'lhu_run_zero', 'lhu_run_alias_sign', 'lhu_run_basezero_unaligned', 'lbu_run_zero', 'lbu_run_alias_sign', 'lbu_run_basezero_unaligned', 'sd_run_basezero_sign', 'sd_run_alias', 'sw_run_basezero_sign', 'sw_run_alias', 'sh_run_basezero_sign', 'sh_run_alias', 'sb_run_basezero_sign', 'sb_run_alias', 'ld_run_source_clause', 'ld_run_source_hypotheses', 'ld_run_carrier_types', 'lwu_run_source_clause', 'lwu_run_source_hypotheses', 'lwu_run_carrier_types', 'lhu_run_source_clause', 'lhu_run_source_hypotheses', 'lhu_run_carrier_types', 'lbu_run_source_clause', 'lbu_run_source_hypotheses', 'lbu_run_carrier_types', 'sd_run_source_clause', 'sd_run_source_hypotheses', 'sd_run_carrier_types', 'sw_run_source_clause', 'sw_run_source_hypotheses', 'sw_run_carrier_types', 'sh_run_source_clause', 'sh_run_source_hypotheses', 'sh_run_carrier_types', 'sb_run_source_clause', 'sb_run_source_hypotheses', 'sb_run_carrier_types'):
        if label not in rows[0]:
            raise ValueError('missing memory original row: ' + label)
    return True
if __name__ == '__main__':
    check()
    print('Native memory actual Run original evidence PASS')
