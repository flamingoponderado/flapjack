#!/usr/bin/env python3
"""Pin source-reviewed full native memory composition and original regression evidence."""
from pathlib import Path
import hashlib
ROOT = Path(__file__).resolve().parents[2]
CHECKS = {'Flapjack/RiscV/CorrectnessEncoding/MemoryStep.lean': '1063900ac6e246105c9970d18e163aa2824b52365e35a1510b83c9d56ced4833', 'Flapjack/RiscV/CorrectnessEncoding/Skip.lean': '44117f00633d330a389c61b27b356e5c06bee258bfef6ee09ac52a71c11ebea8', 'scripts/hol-probes/riscv_memory_step_probeScript.sml': '289419cbaf16b7808625ba9cb7b6a46f4096a61019f146031ac48c5b0ae3d66d', 'scripts/hol-probes/riscv_memory_step_probe.out': '65fca4e9d54253d05f03b7502b3c3c9efc59545ca996ebb54f10251f89b64289'}
def check(root=ROOT):
    for name, digest in CHECKS.items():
        if hashlib.sha256((root / name).read_bytes()).hexdigest() != digest:
            raise ValueError('native memory original statement/evidence drift: ' + name)
    commands = (root / 'scripts/hol-probes/regenerate.sh').read_text().replace(chr(92)+chr(10), ' ').splitlines()
    rows = [s for s in commands if s.startswith('run_probe riscv_memory_step_probeScript.sml ')]
    if len(rows) != 1:
        raise ValueError('memory requires one complete original registration')
    for label in ('ld_next_sign', 'ld_next_zero', 'lwu_next_sign', 'lwu_next_zero', 'lhu_next_sign', 'lhu_next_zero', 'lbu_next_sign', 'lbu_next_zero', 'sd_next_sign', 'sd_next_zero', 'sw_next_sign', 'sw_next_zero', 'sh_next_sign', 'sh_next_zero', 'sb_next_sign', 'sb_next_zero', 'next_source_clause', 'next_source_hypotheses', 'next_carrier_types', 'pc_source_clause', 'pc_source_hypotheses', 'pc_carrier_types'):
        if label not in rows[0]:
            raise ValueError('missing memory original row: ' + label)
    return True
if __name__ == '__main__':
    check()
    print('Native memory Next/control/validity original evidence PASS')
