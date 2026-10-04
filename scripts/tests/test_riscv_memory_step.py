import importlib.util
from pathlib import Path
import tempfile
import unittest
ROOT=Path(__file__).resolve().parents[2]
spec=importlib.util.spec_from_file_location('memory_guard', ROOT/'scripts/hol-probes/check-riscv-memory-step.py')
guard=importlib.util.module_from_spec(spec);spec.loader.exec_module(guard)
class MemoryStepGuard(unittest.TestCase):
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
 def test_narrow_register(self):self.mutate('Flapjack/RiscV/CorrectnessEncoding/MemoryStep.lean','(r1 r2 : BitVec 5)','(r1 r2 : BitVec 4)')
 def test_target_assumption(self):self.mutate('Flapjack/RiscV/CorrectnessEncoding/MemoryStep.lean','(ok : riscvOk ms = true)' ,'(ok : riscvOk ms = true) (target_run : True)' )
 def test_missing_store_case(self):self.mutate('Flapjack/RiscV/CorrectnessEncoding/MemoryStep.lean','theorem next_memory_step','theorem omitted_next_case')
 def test_false_oracle(self):self.mutate('scripts/hol-probes/riscv_memory_step_probe.out','sb_next_zero=T','sb_next_zero=F')
 def test_added_source_hypothesis(self):self.mutate('scripts/hol-probes/riscv_memory_step_probe.out','next_source_hypotheses=0','next_source_hypotheses=1')
 def test_lost_sentinel(self):self.mutate('scripts/hol-probes/regenerate.sh','sb_next_sign sb_next_zero','sb_next_sign')
