import importlib.util
from pathlib import Path
import tempfile
import unittest
ROOT=Path(__file__).resolve().parents[2]
spec=importlib.util.spec_from_file_location('memory_guard', ROOT/'scripts/hol-probes/check-riscv-memory-bytes.py')
guard=importlib.util.module_from_spec(spec);spec.loader.exec_module(guard)
class MemoryBytesGuard(unittest.TestCase):
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
 def test_narrow_register(self):self.mutate('Flapjack/RiscV/CorrectnessEncoding/MemoryBytes.lean','(rd rs : BitVec 5)','(rd rs : BitVec 4)')
 def test_target_assumption(self):self.mutate('Flapjack/RiscV/CorrectnessEncoding/MemoryBytes.lean','(ok : Flapjack.Compiler.Encoders.RiscV.Target.riscvOk s = true) :','(ok : Flapjack.Compiler.Encoders.RiscV.Target.riscvOk s = true) (target_run : True) :')
 def test_missing_store_case(self):self.mutate('Flapjack/RiscV/CorrectnessEncoding/MemoryBytes.lean','theorem memory_raw_write_region_frame','theorem omitted_region_frame')
 def test_false_oracle(self):self.mutate('scripts/hol-probes/riscv_memory_bytes_probe.out','write8_cross=T','write8_cross=F')
 def test_added_source_hypothesis(self):self.mutate('scripts/hol-probes/riscv_memory_bytes_probe.out','write_source_hypotheses=0','write_source_hypotheses=1')
 def test_lost_sentinel(self):self.mutate('scripts/hol-probes/regenerate.sh','read_wrap_last read_wrap_cross','read_wrap_last')
