#!/usr/bin/env python3
"""Pin source-reviewed full native memory composition and original regression evidence."""
from pathlib import Path
import hashlib
ROOT = Path(__file__).resolve().parents[2]
CHECKS = {'Flapjack/RiscV/CorrectnessEncoding/MemorySource.lean': '7d76e18c33455ec4b96ccbb47425de79d9d2cf47207fa75b8f24dd97575a0896', 'scripts/hol-probes/riscv_memory_source_probeScript.sml': '03a76edaccb84523c57fec0b345aaf737f76e759736e7ca82cbb03cc5bdbcec1', 'scripts/hol-probes/riscv_memory_source_probe.out': 'fd94566adec658c8e0acbc9624fa16732a1b360e536c686344436067feec99de'}
def check(root=ROOT):
    for name, digest in CHECKS.items():
        if hashlib.sha256((root / name).read_bytes()).hexdigest() != digest:
            raise ValueError('native memory original statement/evidence drift: ' + name)
    commands = (root / 'scripts/hol-probes/regenerate.sh').read_text().replace(chr(92)+chr(10), ' ').splitlines()
    rows = [s for s in commands if s.startswith('run_probe riscv_memory_source_probeScript.sml ')]
    if len(rows) != 1:
        raise ValueError('memory requires one complete original registration')
    for label in ('le0_wrap', 'le1_wrap', 'le1_missing', 'le2_wrap', 'le2_missing', 'le4_wrap', 'le4_missing', 'le8_wrap', 'le8_missing', 'le12_wrap', 'le12_missing', 'be0_wrap', 'be1_wrap', 'be1_missing', 'be2_wrap', 'be2_missing', 'be4_wrap', 'be4_missing', 'be8_wrap', 'be8_missing', 'be12_wrap', 'be12_missing', 'previous_failure_zero', 'read_clause', 'read_hypotheses', 'read_types', 'write_clause', 'write_hypotheses', 'write_types', 'load_clause', 'load_hypotheses', 'load_types', 'store_clause', 'store_hypotheses', 'store_types'):
        if label not in rows[0]:
            raise ValueError('missing memory original row: ' + label)
    return True
if __name__ == '__main__':
    check()
    print('Native memory source traversal domain original evidence PASS')
