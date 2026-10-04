import importlib.util
from pathlib import Path
import tempfile
import unittest
ROOT=Path(__file__).resolve().parents[2]
spec=importlib.util.spec_from_file_location('memory_guard', ROOT/'scripts/hol-probes/check-riscv-memory-inputs.py')
guard=importlib.util.module_from_spec(spec);spec.loader.exec_module(guard)
class MemoryInputsGuard(unittest.TestCase):
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
 def test_native_run_premise(self):self.mutate('Flapjack/RiscV/CorrectnessEncoding/MemoryInputs.lean','(relation : targetStateRel','(target_run : True) (relation : targetStateRel')
 def test_narrow_signed_bound(self):self.mutate('Flapjack/RiscV/CorrectnessEncoding/MemoryInputs.lean','-2048 ≤ w.toInt','-2047 ≤ w.toInt')
 def test_store_binder_order(self):self.mutate('Flapjack/RiscV/CorrectnessEncoding/MemoryInputs.lean','rawWriteData (addrHOL (.addr base w) s, readReg r s, 8)','rawWriteData (readReg r s, addrHOL (.addr base w) s, 8)')
 def test_false_oracle(self):self.mutate('scripts/hol-probes/riscv_memory_inputs_probe.out','alias_wrap=T','alias_wrap=F')
 def test_added_original_hypothesis(self):self.mutate('scripts/hol-probes/riscv_memory_inputs_probe.out','native_hypotheses=0','native_hypotheses=1')
 def test_lost_load_sentinel(self):self.mutate('scripts/hol-probes/regenerate.sh','load_endpoints load_registers','load_registers')
