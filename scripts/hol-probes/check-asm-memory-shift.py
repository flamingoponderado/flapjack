#!/usr/bin/env python3
"""Pin reviewed literal Nat-eight source memory shifts and matched original observations."""
from pathlib import Path
import hashlib
ROOT=Path(__file__).resolve().parents[2]
CHECKS={'Flapjack/Compiler/Backend/LabToTarget/InstMem.lean': '4611ade2f02acbb94de8ecfb94d7e0265b0ffc7a60a8dd21da014c5ee01733f8', 'Flapjack/Compiler/Encoders/AsmSem/Memory.lean': '48981ab3a554e3ad485627c798a7ab54f5085847c642b8f0a2de309ecf81f1e5', 'Flapjack/Compiler/Encoders/AsmProps/Memory.lean': '0b890f9a0d3f7708ed7cfbd8797e41286cb03c956d325314657ff673d7053985', 'Flapjack/Compiler/Encoders/AsmSem/MemoryByteShift.lean': '612052b61edbe8c534b40153eaa625b63dba46b0c1b9957ff4e5f6d908ca183e', 'scripts/hol-probes/asm_memory_shift_probeScript.sml': 'a1dab80e422e0709729ffbfafa5b3da9ac727fcec4b330d0e3fef0581391fef5', 'scripts/hol-probes/asm_memory_shift_probe.out': '4127bc37122a7ca758123fa08ca515b75dff3b9cbd6b4fcced2fe7800703b78c'}
LABELS=tuple(f'{case}_width_{width}' for width in (1,2,3,64) for case in ('read','write'))
def check(root=ROOT):
 for name,digest in CHECKS.items():
  if hashlib.sha256((root/name).read_bytes()).hexdigest()!=digest:
   raise ValueError('source memory Nat-eight statement/evidence drift: '+name)
 rows=[line for line in (root/'scripts/hol-probes/regenerate.sh').read_text().replace(chr(92)+chr(10),' ').splitlines() if line.startswith('run_probe asm_memory_shift_probeScript.sml ')]
 if len(rows)!=1:raise ValueError('require exactly one original byte-shift registration')
 for label in LABELS:
  if label not in rows[0].split():raise ValueError('missing original byte-shift sentinel: '+label)
 return True
if __name__=='__main__':
 check();print('Literal Nat-eight source memory shift original evidence PASS')
