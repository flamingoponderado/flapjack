#!/usr/bin/env python3
"""Pin exact source/native memory inputs and freshly replayed original evidence."""
from pathlib import Path
import hashlib
ROOT=Path(__file__).resolve().parents[2]
CHECKS={'Flapjack/RiscV/CorrectnessEncoding/MemoryInputs.lean': '07f6abc95c1d5e61af16914f2cd6f264e15c2c1109424887a332e27f8ed71797', 'scripts/hol-probes/riscv_memory_inputs_probeScript.sml': 'e07d72987d532741624a82afd3a999fd87a5f7a8c98049d19022cab48e9522b3', 'scripts/hol-probes/riscv_memory_inputs_probe.out': '13191be1c38c03cc0bc2cd0fe0177193bf01f7a76d3f2fc2772b13c979003632'}
LABELS=('load_endpoints', 'load_registers', 'load_offsets', 'load8_endpoints', 'load8_registers', 'load8_offsets', 'load16_endpoints', 'load16_registers', 'load16_offsets', 'load32_endpoints', 'load32_registers', 'load32_offsets', 'store_endpoints', 'store_registers', 'store_offsets', 'store8_endpoints', 'store8_registers', 'store8_offsets', 'store16_endpoints', 'store16_registers', 'store16_offsets', 'store32_endpoints', 'store32_registers', 'store32_offsets', 'alias_wrap', 'source_clause', 'source_hypotheses', 'source_types', 'native_clause', 'native_hypotheses', 'native_types')
def check(root=ROOT):
 for name,digest in CHECKS.items():
  if hashlib.sha256((root/name).read_bytes()).hexdigest()!=digest:
   raise ValueError('source/native memory input statement/evidence drift: '+name)
 rows=[line for line in (root/'scripts/hol-probes/regenerate.sh').read_text().replace(chr(92)+chr(10),' ').splitlines() if line.startswith('run_probe riscv_memory_inputs_probeScript.sml ')]
 if len(rows)!=1:raise ValueError('require one complete original memory input registration')
 for label in LABELS:
  if label not in rows[0].split():raise ValueError('missing original memory input sentinel: '+label)
 return True
if __name__=='__main__':
 check();print('Source/native memory input original evidence PASS')
