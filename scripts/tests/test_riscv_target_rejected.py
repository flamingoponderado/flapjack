"""Mutations protect the LongDiv case scope, FP absence and source rejection premises."""
import importlib.util
from pathlib import Path
import tempfile
import unittest
ROOT=Path(__file__).resolve().parents[2]
spec=importlib.util.spec_from_file_location('rejected_guard',ROOT/'scripts/hol-probes/check-riscv-target-rejected.py')
guard=importlib.util.module_from_spec(spec)
spec.loader.exec_module(guard)
class RejectedGuard(unittest.TestCase):
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
    def test_no_assumed_rejection(self):
        self.mutate('Flapjack/RiscV/CorrectnessEncoding/Rejected.lean','(r1 r2 r3 r4 r5 : Nat)','(r1 r2 r3 r4 r5 : Nat) (rejected : False)')
    def test_fp_case_absent(self):
        self.mutate('Flapjack/RiscV/CorrectnessEncoding/Rejected.lean','end Flapjack.RiscV.TargetProof','theorem riscv_encoder_correct_fp (f : HolFp) : True := trivial\nend Flapjack.RiscV.TargetProof')
    def test_not_tagged_exact(self):
        self.mutate('Flapjack/RiscV/CorrectnessEncoding/Rejected.lean','theorem riscv_encoder_correct_longdiv','@[hol "cakeml/compiler/encoders/riscv/proofs/riscv_targetProofScript.sml" "riscv_encoder_correct"]\ntheorem riscv_encoder_correct_longdiv')
    def test_five_longdiv_regs(self):
        self.mutate('Flapjack/RiscV/CorrectnessEncoding/Rejected.lean','(r1 r2 r3 r4 r5 : Nat)','(r1 r2 r3 r4 : Nat)')
    def test_every_environment(self):
        self.mutate('Flapjack/RiscV/CorrectnessEncoding/Rejected.lean','∀ env : Nat → riscv_state → riscv_state','∃ env : Nat → riscv_state → riscv_state')
    def test_code_bytes(self):
        self.mutate('Flapjack/RiscV/CorrectnessEncoding/Rejected.lean',"riscvTarget.getByte ms' pc = riscvTarget.getByte ms pc",'True')
    def test_outside_domain(self):
        self.mutate('Flapjack/RiscV/CorrectnessEncoding/Rejected.lean','¬ s1.memDomain x','s1.memDomain x')
    def test_actual_guard_conjunct(self):
        self.mutate('Flapjack/RiscV/CorrectnessEncoding/Rejected.lean','h.1.2.2.2.2.2.2','h.1.2.2.2.2.2.1')
    def test_source_isa(self):
        self.mutate('cakeml/compiler/encoders/asm/asmScript.sml','(c.ISA = x86_64) /\\ (r1 = 0)','(c.ISA = RISC_V) /\\ (r1 = 0)')
    def test_source_fp_count(self):
        self.mutate('cakeml/compiler/encoders/riscv/riscv_targetScript.sml','fp_reg_count := 0','fp_reg_count := 32')
    def test_actual_hypotheses(self):
        self.mutate('scripts/hol-probes/riscv_target_rejected_probe.out','riscv_encoder_correct_fp_hypotheses=0','riscv_encoder_correct_fp_hypotheses=1')
    def test_typed_evidence_registered(self):
        self.mutate('scripts/hol-probes/regenerate.sh','riscv_encoder_correct_longdiv_types','')
    def test_full_fp_statement(self):
        self.mutate('scripts/hol-probes/riscv_target_rejected_probe.out','(f :fp)','(f :num)')
