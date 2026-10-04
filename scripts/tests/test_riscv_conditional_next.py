"""Mutations protect full state, predicate and unrestricted inputs."""
import importlib.util
from pathlib import Path
import tempfile
import unittest
ROOT=Path(__file__).resolve().parents[2]
spec=importlib.util.spec_from_file_location('cond_guard',ROOT/'scripts/hol-probes/check-riscv-conditional-next.py')
guard=importlib.util.module_from_spec(spec)
spec.loader.exec_module(guard)
class ConditionalNextGuard(unittest.TestCase):
    def mutate(self,name,before,after):
        with tempfile.TemporaryDirectory() as d:
            root=Path(d)
            for n in [*guard.CHECKS,'Flapjack.lean','scripts/hol-probes/regenerate.sh','scripts/hol-probes/riscv_conditional_next_probe.out']:
                p=root/n
                p.parent.mkdir(parents=True,exist_ok=True)
                p.write_bytes((ROOT/n).read_bytes())
            p=root/name
            text=p.read_text()
            self.assertIn(before,text)
            p.write_text(text.replace(before,after,1))
            with self.assertRaises(ValueError): guard.check(root)
    def test_accepted(self): self.assertTrue(guard.check())
    def test_intrinsic_registers(self):
        self.mutate('Flapjack/RiscV/CorrectnessEncoding/JumpCmp/Native.lean','(rs1 rs2 : BitVec 5)','(rs1 rs2 : BitVec 6)')
    def test_halfword_payload(self):
        self.mutate('Flapjack/RiscV/CorrectnessEncoding/JumpCmp/Native.lean','(imm : BitVec 12)','(imm : BitVec 13)')
    def test_full_post(self):
        self.mutate('Flapjack/RiscV/CorrectnessEncoding/JumpCmp/Native.lean','Jump.branchPost ms','ms')
    def test_signed_shift(self):
        self.mutate('Flapjack/RiscV/CorrectnessEncoding/JumpCmp/Native.lean','(imm.signExtend 64 <<< (1 : Nat))','imm.setWidth 64')
    def test_no_added_alignment(self):
        self.mutate('Flapjack/RiscV/CorrectnessEncoding/JumpCmp/Native.lean','(ok : riscvOk ms = true)','(ok : riscvOk ms = true) (aligned : imm.toNat % 2 = 0)')
    def test_signed_comparison(self):
        self.mutate('Flapjack/RiscV/CorrectnessEncoding/JumpCmp/Native.lean','.slt (GPR rs2 ms)','.ult (GPR rs2 ms)')
    def test_reverse_bge(self):
        self.mutate('Flapjack/RiscV/CorrectnessEncoding/JumpCmp/Native.lean','(GPR rs2 ms).sle (GPR rs1 ms)','(GPR rs1 ms).sle (GPR rs2 ms)')
    def test_actual_bytes(self):
        self.mutate('Flapjack/RiscV/CorrectnessEncoding/JumpCmp/Native.lean','ms.MEM8 (ms.c_PC ms.procID+3)','ms.MEM8 (ms.c_PC ms.procID+2)')
    def test_complete_registration(self):
        self.mutate('scripts/hol-probes/regenerate.sh','bgeu_next_signed_boundary','')
    def test_original_next(self):
        self.mutate('scripts/hol-probes/riscv_conditional_next_probe.out','blt_next_signed_boundary=T','blt_next_signed_boundary=F')
