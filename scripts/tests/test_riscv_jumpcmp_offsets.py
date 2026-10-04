"""Mutations protect original offset bounds, word widths and prefix correction."""
import importlib.util
from pathlib import Path
import tempfile
import unittest
ROOT=Path(__file__).resolve().parents[2]
spec=importlib.util.spec_from_file_location('offset_guard',ROOT/'scripts/hol-probes/check-riscv-jumpcmp-offsets.py')
guard=importlib.util.module_from_spec(spec)
spec.loader.exec_module(guard)
class OffsetGuard(unittest.TestCase):
    def mutate(self,name,before,after):
        with tempfile.TemporaryDirectory() as d:
            root=Path(d)
            for n in [*guard.CHECKS,'Flapjack.lean','scripts/hol-probes/regenerate.sh']:
                p=root/n
                p.parent.mkdir(parents=True,exist_ok=True)
                p.write_bytes((ROOT/n).read_bytes())
            p=root/name
            text=p.read_text()
            self.assertIn(before,text)
            p.write_text(text.replace(before,after,1))
            with self.assertRaises(ValueError): guard.check(root)
    def test_accepted(self): self.assertTrue(guard.check())
    def test_signed_shift(self):
        self.mutate('Flapjack/RiscV/CorrectnessEncoding/JumpCmp/Arithmetic.lean','a.sshiftRight 1','a >>> (1 : Nat)')
    def test_halfword_correction(self):
        self.mutate('Flapjack/RiscV/CorrectnessEncoding/JumpCmp/Arithmetic.lean','- 2#12','- 0#12')
    def test_long_prefix_correction(self):
        self.mutate('Flapjack/RiscV/CorrectnessEncoding/JumpCmp/Arithmetic.lean','- 4#20','- 2#20')
    def test_original_near_lower(self):
        self.mutate('Flapjack/RiscV/CorrectnessEncoding/JumpCmp/Arithmetic.lean','-4092 ≤ a.toInt','-4096 ≤ a.toInt')
    def test_original_global_upper(self):
        self.mutate('Flapjack/RiscV/CorrectnessEncoding/JumpCmp/Arithmetic.lean','a.toInt ≤ 1048579','a.toInt ≤ 1048575')
    def test_source_alignment(self):
        self.mutate('Flapjack/RiscV/CorrectnessEncoding/JumpCmp/Arithmetic.lean','a.toNat % 4 = 0','a.toNat % 2 = 0')
    def test_payload_width(self):
        self.mutate('Flapjack/RiscV/CorrectnessEncoding/JumpCmp/Arithmetic.lean','setWidth 12','setWidth 13')
    def test_sign_extension(self):
        self.mutate('Flapjack/RiscV/CorrectnessEncoding/JumpCmp/Arithmetic.lean','.signExtend 64','.setWidth 64')
    def test_no_extra_offset_assumption(self):
        self.mutate('Flapjack/RiscV/CorrectnessEncoding/JumpCmp/Arithmetic.lean','(aligned : a.toNat % 4 = 0)','(aligned : a.toNat % 4 = 0) (desired : a = 0)')
    def test_full_pc_prefix(self):
        self.mutate('Flapjack/RiscV/CorrectnessEncoding/JumpCmp/Arithmetic.lean','pc + 8#64 +','pc + 4#64 +')
    def test_actual_hypotheses(self):
        self.mutate('scripts/hol-probes/riscv_jumpcmp_offsets_probe.out','far8_hypotheses=0','far8_hypotheses=1')
    def test_endpoint_observation(self):
        self.mutate('scripts/hol-probes/riscv_jumpcmp_offsets_probe.out','near4_boundary0=T','near4_boundary0=F')
    def test_typed_source_registered(self):
        self.mutate('scripts/hol-probes/regenerate.sh','reg_test_source','')
    def test_original_global_boundary(self):
        self.mutate('scripts/hol-probes/riscv_jumpcmp_offsets_probe.out','(0x100003w :word64)','(0xFFFFFw :word64)')
