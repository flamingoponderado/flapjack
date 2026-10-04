"""Fail-closed regression coverage for native Ror support signatures/evidence."""
import importlib.util
from pathlib import Path
import tempfile
import unittest
ROOT=Path(__file__).resolve().parents[2]
spec=importlib.util.spec_from_file_location('ror_guard',ROOT/'scripts/hol-probes/check-riscv-ror-step.py')
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
        self.mutate('Flapjack/RiscV/CorrectnessEncoding/RorStep.lean','(rd rs : BitVec 5)','(target_run : True) (rd rs : BitVec 5)')
    def test_narrow_count(self):
        self.mutate('Flapjack/RiscV/CorrectnessEncoding/RorStep.lean','(shamt : BitVec 6)','(shamt : BitVec 5)')
    def test_false_oracle(self):
        self.mutate('scripts/hol-probes/riscv_ror_step_probe.out','ror_next_sub_zero=T','ror_next_sub_zero=F')
    def test_lost_sentinel(self):
        self.mutate('scripts/hol-probes/regenerate.sh','ror_next_srl_all_ones','')
    def test_duplicate_registration(self):
        self.mutate('scripts/hol-probes/regenerate.sh','run_probe riscv_ror_step_probeScript.sml','run_probe riscv_ror_step_probeScript.sml fake\nrun_probe riscv_ror_step_probeScript.sml')
