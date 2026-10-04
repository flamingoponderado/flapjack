#!/usr/bin/env python3
"""Pin literal source/native store post-memory composition and fresh original evidence."""
from pathlib import Path
import hashlib
ROOT=Path(__file__).resolve().parents[2]
CHECKS={'Flapjack/RiscV/CorrectnessEncoding/MemoryStore.lean': '07d701ffd5de6de60669198be232bfc6b4f59b75ffaf6521ea9ae5bdc4891beb', 'scripts/hol-probes/riscv_memory_store_value_probeScript.sml': '90663ca243ab349bb04652a5f96e044470d3bf43827951810e44a8fb7b087648', 'scripts/hol-probes/riscv_memory_store_value_probe.out': '79f56b2db455bb701533b20a770f91f85f536105a12daf7fc241b20e74fcf99a'}
LABELS=tuple(f'store{n}_{edge}' for n in (1,2,4,8) for edge in ('zero','wrap'))+('source_failure_writes','source_narrow_value')+tuple(f'{side}_{field}' for side in ('source','native') for field in ('clause','hypotheses','types'))
def check(root=ROOT):
 for name,digest in CHECKS.items():
  if hashlib.sha256((root/name).read_bytes()).hexdigest()!=digest:
   raise ValueError('source/native store post-memory statement/evidence drift: '+name)
 rows=[line for line in (root/'scripts/hol-probes/regenerate.sh').read_text().replace(chr(92)+chr(10),' ').splitlines() if line.startswith('run_probe riscv_memory_store_value_probeScript.sml ')]
 if len(rows)!=1:raise ValueError('require one complete original store value registration')
 for label in LABELS:
  if label not in rows[0].split():raise ValueError('missing original store sentinel: '+label)
 return True
if __name__=='__main__':
 check();print('Source/native store post-memory original evidence PASS')
