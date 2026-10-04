import importlib.util
from pathlib import Path
import tempfile
import unittest
ROOT=Path(__file__).resolve().parents[2]
spec=importlib.util.spec_from_file_location('memory_guard', ROOT/'scripts/hol-probes/check-riscv-memory-store.py')
guard=importlib.util.module_from_spec(spec);spec.loader.exec_module(guard)
class MemoryStoreGuard(unittest.TestCase):
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
 def test_narrow_value_width(self):self.mutate('Flapjack/RiscV/CorrectnessEncoding/MemoryStore.lean','{width valueWidth : Nat}','{width : Nat}')
 def test_native_run_assumption(self):self.mutate('Flapjack/RiscV/CorrectnessEncoding/MemoryStore.lean','(relation : targetStateRel','(target_run : True) (relation : targetStateRel')
 def test_missing_store_size(self):self.mutate('Flapjack/RiscV/CorrectnessEncoding/MemoryStore.lean','(k : Fin 4)','(k : Fin 3)')
 def test_false_oracle(self):self.mutate('scripts/hol-probes/riscv_memory_store_value_probe.out','store8_wrap=T','store8_wrap=F')
 def test_added_original_hypothesis(self):self.mutate('scripts/hol-probes/riscv_memory_store_value_probe.out','native_hypotheses=0','native_hypotheses=1')
 def test_lost_failure_sentinel(self):self.mutate('scripts/hol-probes/regenerate.sh','source_failure_writes source_narrow_value','source_narrow_value')
