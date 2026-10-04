"""Fail-closed regression coverage for native Ror support signatures/evidence."""
import importlib.util
from pathlib import Path
import tempfile
import unittest
ROOT=Path(__file__).resolve().parents[2]
spec=importlib.util.spec_from_file_location('ror_execution_guard',ROOT/'scripts/hol-probes/check-riscv-ror-execution.py')
guard=importlib.util.module_from_spec(spec)
spec.loader.exec_module(guard)
class RorGuard(unittest.TestCase):
    def test_original(self):
        self.assertTrue(guard.check())
    def mutate(self,path,old,new):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory)
            for name in list(guard.CHECKS)+['scripts/hol-probes/regenerate.sh']:
                dest=root/name
                dest.parent.mkdir(parents=True,exist_ok=True)
                dest.write_text((ROOT/name).read_text())
            p=root/path
            self.assertIn(old,p.read_text())
            p.write_text(p.read_text().replace(old,new))
            with self.assertRaises(ValueError):
                guard.check(root)
    def test_extra_target_run(self):
        self.mutate('Flapjack/RiscV/CorrectnessEncoding/RorExecution.lean','(ok : riscvOk ms = true)','(target_run : True) (ok : riscvOk ms = true)')
    def test_restricted_environment(self):
        self.mutate('Flapjack/RiscV/CorrectnessEncoding/RorExecution.lean','(interference : interferenceOk env (riscvProj d))','(scratch_fixed : True) (interference : interferenceOk env (riscvProj d))')
    def test_wrong_assertion_counter(self):
        self.mutate('Flapjack/RiscV/CorrectnessEncoding/RorExecution.lean','env (index + is.length - k)','env (index + is.length + k)')
    def test_missing_memory_domain(self):
        self.mutate('Flapjack/RiscV/CorrectnessEncoding/RorExecution.lean','∀ a, ¬ d a →','∀ a, d a →')
    def test_replaced_actual_next(self):
        self.mutate('Flapjack/RiscV/CorrectnessEncoding/ConstExecution.lean','(riscvTarget.next ms)','ms')
