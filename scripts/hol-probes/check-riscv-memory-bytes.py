#!/usr/bin/env python3
"""Pin source-reviewed full native memory composition and original regression evidence."""
from pathlib import Path
import hashlib
ROOT = Path(__file__).resolve().parents[2]
CHECKS = {'Flapjack/RiscV/CorrectnessEncoding/MemoryBytes.lean': '4ef7cdfafbb3f71d0eeb3c5b37a5fdff9944cf8a773d7b8e61fd5569dbcf81c6', 'Flapjack/RiscV/L3/Step/ByteMemory.lean': 'b0ef02011e4bc53f39733af233327b9b835233eae104b627eb9870789171796c', 'scripts/hol-probes/riscv_memory_bytes_probeScript.sml': 'a51ec7d6555c659004ec820ac041bc24e575fbbc5cf444d8038dbaec6b64e12a', 'scripts/hol-probes/riscv_memory_bytes_probe.out': 'c3759b1a64fdcfad261b92c2c0473e4800f49264f37ca6a121bf830e882c9a16'}
def check(root=ROOT):
    for name, digest in CHECKS.items():
        if hashlib.sha256((root / name).read_bytes()).hexdigest() != digest:
            raise ValueError('native memory original statement/evidence drift: ' + name)
    commands = (root / 'scripts/hol-probes/regenerate.sh').read_text().replace(chr(92)+chr(10), ' ').splitlines()
    rows = [s for s in commands if s.startswith('run_probe riscv_memory_bytes_probeScript.sml ')]
    if len(rows) != 1:
        raise ValueError('memory requires one complete original registration')
    for label in ('read_offset0', 'read_offset1', 'read_offset2', 'read_offset3', 'read_offset4', 'read_offset5', 'read_offset6', 'read_offset7', 'read_wrap_last', 'read_wrap_cross', 'write1_zero', 'write1_edge', 'write1_wrap', 'write1_cross', 'write2_zero', 'write2_edge', 'write2_wrap', 'write2_cross', 'write4_zero', 'write4_edge', 'write4_wrap', 'write4_cross', 'write8_zero', 'write8_edge', 'write8_wrap', 'write8_cross', 'read_source_clause', 'read_source_hypotheses', 'read_carrier_types', 'write_source_clause', 'write_source_hypotheses', 'write_carrier_types', 'word_read_source_clause', 'word_read_source_hypotheses', 'word_read_carrier_types', 'word_write_source_clause', 'word_write_source_hypotheses', 'word_write_carrier_types'):
        if label not in rows[0]:
            raise ValueError('missing memory original row: ' + label)
    return True
if __name__ == '__main__':
    check()
    print('Native memory byte correspondence original evidence PASS')
