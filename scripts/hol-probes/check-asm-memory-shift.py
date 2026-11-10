#!/usr/bin/env python3
"""Pin reviewed literal Nat-eight source memory shifts and matched original observations."""
from pathlib import Path
import hashlib
ROOT=Path(__file__).resolve().parents[2]
CHECKS={'Flapjack/Compiler/Backend/LabToTarget/InstMem.lean': '3aa95286c2411d7a59a8e1f4bb67020fccaf50865fc2dbf2bce09b4736c90e13', 'Flapjack/Compiler/Encoders/AsmSem/Memory.lean': 'd843f6b1c4a9551c31f28407dadba5c2f71c70aec7b997f324cbfd0f917d5400', 'Flapjack/Compiler/Encoders/AsmProps/Memory.lean': '30277a3843dca072feceb6a873a428ee3b7fbc2d2826384addeec3771e604ab4', 'Flapjack/Compiler/Encoders/AsmSem/MemoryByteShift.lean': '35857af10780868b9dc39f29d939674fcdb346123519176a3de38c4d8a5692cc', 'scripts/hol-probes/asm_memory_shift_probeScript.sml': 'a1dab80e422e0709729ffbfafa5b3da9ac727fcec4b330d0e3fef0581391fef5', 'scripts/hol-probes/asm_memory_shift_probe.out': '4127bc37122a7ca758123fa08ca515b75dff3b9cbd6b4fcced2fe7800703b78c'}
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
