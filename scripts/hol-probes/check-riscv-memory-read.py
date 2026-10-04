#!/usr/bin/env python3
"""Pin source/native read-value correspondence and matched fresh original observations."""
from pathlib import Path
import hashlib
ROOT=Path(__file__).resolve().parents[2]
CHECKS={'Flapjack/RiscV/CorrectnessEncoding/MemoryRead.lean': '9ae079b52bb213f69c7f40f0a4384f42ec4380e6241865ead79f2a5be5b3dbca', 'scripts/hol-probes/riscv_memory_read_value_probeScript.sml': 'c306f4dd5bdcdc674c8d1b6316ed9785823fc01eece1a02c9fc498e289aeaa0a', 'scripts/hol-probes/riscv_memory_read_value_probe.out': 'a3759a4c6e20d37c10747610e44faec713e3ca6d47d6d65ef9fdcc3eb9f19908'}
LABELS=tuple(f'read{n}_{edge}' for n in (1,2,4,8) for edge in ('zero','wrap'))+tuple(f'{side}_{field}' for side in ('source','native') for field in ('clause','hypotheses','types'))
def check(root=ROOT):
 for name,digest in CHECKS.items():
  if hashlib.sha256((root/name).read_bytes()).hexdigest()!=digest:
   raise ValueError('source/native memory read value drift: '+name)
 rows=[line for line in (root/'scripts/hol-probes/regenerate.sh').read_text().replace(chr(92)+chr(10),' ').splitlines() if line.startswith('run_probe riscv_memory_read_value_probeScript.sml ')]
 if len(rows)!=1:raise ValueError('require one complete original read value registration')
 for label in LABELS:
  if label not in rows[0].split():raise ValueError('missing original read value sentinel: '+label)
 return True
if __name__=='__main__':
 check();print('Source/native read value original evidence PASS')
