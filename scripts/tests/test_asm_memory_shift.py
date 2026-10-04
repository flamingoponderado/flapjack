import importlib.util
from pathlib import Path
import tempfile
import unittest
ROOT=Path(__file__).resolve().parents[2]
spec=importlib.util.spec_from_file_location('memory_guard', ROOT/'scripts/hol-probes/check-asm-memory-shift.py')
guard=importlib.util.module_from_spec(spec);spec.loader.exec_module(guard)
class MemoryShiftGuard(unittest.TestCase):
 def fixture(self,d):
  root=Path(d)
  for name in list(guard.CHECKS)+['scripts/hol-probes/regenerate.sh']:
   p=root/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_text((ROOT/name).read_text())
  return root
 def test_original(self):self.assertTrue(guard.check())
 def mutate(self,path,old,new):
  with tempfile.TemporaryDirectory() as d:
   root=self.fixture(d);p=root/path;s=p.read_text();self.assertIn(old,s);p.write_text(s.replace(old,new))
   with self.assertRaises(ValueError):guard.check(root)
 def test_read_count_truncation(self):self.mutate('Flapjack/Compiler/Encoders/AsmSem/Memory.lean','<<< (8 : Nat)','<<< 8')
 def test_write_count_truncation(self):self.mutate('Flapjack/Compiler/Encoders/AsmSem/Memory.lean','>>> (8 : Nat)','>>> 8')
 def test_narrow_width(self):self.mutate('Flapjack/Compiler/Encoders/AsmSem/Memory.lean','[NeZero resultWidth]','[NeZero resultWidth] (wide_only : 8 ≤ resultWidth)')
 def test_false_oracle(self):self.mutate('scripts/hol-probes/asm_memory_shift_probe.out','read_width_1=T','read_width_1=F')
 def test_false_regression(self):self.mutate('Flapjack/Compiler/Encoders/AsmSem/MemoryByteShift.lean','resultWidth := 1) 0 2 sample).1 = 0','resultWidth := 1) 0 2 sample).1 = 1')
 def test_lost_sentinel(self):self.mutate('scripts/hol-probes/regenerate.sh','read_width_3 write_width_3','read_width_3')
