#!/usr/bin/env python3
"""Pin source-reviewed full native memory composition and original regression evidence."""
from pathlib import Path
import hashlib
ROOT = Path(__file__).resolve().parents[2]
CHECKS = {'Flapjack/RiscV/CorrectnessEncoding/DecodeMemory.lean': '9ec8a0c79f1a2dcf00702625f3a4c466eec7d3224f386ecdf7d4218f97635600', 'scripts/hol-probes/riscv_memory_decode_probeScript.sml': '7b7cf5b708ee8ea736c21627c3882bdd3ce89eeccd02d307751c6cf01aa34b1f', 'scripts/hol-probes/riscv_memory_decode_probe.out': '77bca760f0eeef26de9e0c0fb8df32e2d3eb944e44b672b8ba428b9c62bdc0fd'}
def check(root=ROOT):
    for name, digest in CHECKS.items():
        if hashlib.sha256((root / name).read_bytes()).hexdigest() != digest:
            raise ValueError('native memory original statement/evidence drift: ' + name)
    commands = (root / 'scripts/hol-probes/regenerate.sh').read_text().replace(chr(92)+chr(10), ' ').splitlines()
    rows = [s for s in commands if s.startswith('run_probe riscv_memory_decode_probeScript.sml ')]
    if len(rows) != 1:
        raise ValueError('memory requires one complete original registration')
    for label in ('ld_decode_zero', 'ld_decode_all_ones', 'ld_decode_mixed_sign', 'ld_encode_source_clause', 'ld_encode_source_hypotheses', 'ld_carrier_types', 'lwu_decode_zero', 'lwu_decode_all_ones', 'lwu_decode_mixed_sign', 'lwu_encode_source_clause', 'lwu_encode_source_hypotheses', 'lwu_carrier_types', 'lhu_decode_zero', 'lhu_decode_all_ones', 'lhu_decode_mixed_sign', 'lhu_encode_source_clause', 'lhu_encode_source_hypotheses', 'lhu_carrier_types', 'lbu_decode_zero', 'lbu_decode_all_ones', 'lbu_decode_mixed_sign', 'lbu_encode_source_clause', 'lbu_encode_source_hypotheses', 'lbu_carrier_types', 'sd_decode_zero', 'sd_decode_all_ones', 'sd_decode_mixed_sign', 'sd_encode_source_clause', 'sd_encode_source_hypotheses', 'sd_carrier_types', 'sw_decode_zero', 'sw_decode_all_ones', 'sw_decode_mixed_sign', 'sw_encode_source_clause', 'sw_encode_source_hypotheses', 'sw_carrier_types', 'sh_decode_zero', 'sh_decode_all_ones', 'sh_decode_mixed_sign', 'sh_encode_source_clause', 'sh_encode_source_hypotheses', 'sh_carrier_types', 'sb_decode_zero', 'sb_decode_all_ones', 'sb_decode_mixed_sign', 'sb_encode_source_clause', 'sb_encode_source_hypotheses', 'sb_carrier_types'):
        if label not in rows[0]:
            raise ValueError('missing memory original row: ' + label)
    return True
if __name__ == '__main__':
    check()
    print('Native memory unrestricted decode original evidence PASS')
