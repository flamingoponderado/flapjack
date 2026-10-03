import importlib.util
from pathlib import Path
import unittest
ROOT=Path(__file__).resolve().parents[2]
SPEC=importlib.util.spec_from_file_location("bytes_guard",ROOT/"scripts/hol-probes/check-riscv-target-bytes.py")
M=importlib.util.module_from_spec(SPEC);SPEC.loader.exec_module(M)
class BytesTests(unittest.TestCase):
    def test_full_proofs_and_negative_guards(self):
        args=[(ROOT/p).read_text() for p in (
          "scripts/hol-probes/riscv_target_bytes_probe.out",
          "cakeml/compiler/encoders/riscv/proofs/riscv_targetProofScript.sml",
          "scripts/hol-probes/riscv_target_bytes_probeScript.sml",
          "Flapjack/RiscV/CorrectnessEncoding/BytesInMemory.lean",
          "scripts/hol-probes/regenerate.sh")]
        M.check(*args)
        for i,old,new in [(0,"w : :α","w : :word64"),(0,"+ 3w","+ 4w"),
          (0,"hypotheses=0","hypotheses=1"),(0,"proved=T","proved=F"),
          (2,"!w s state","!s state"),(2,"set_sepTheory.fun2set_eq","TRUTH"),
          (3,"{α : Type} (_w : α)","(_w : BitVec 64)"),
          (3,"state.c_PC state.procID + 3","state.c_PC state.procID + 4"),
          (3,"s.memDomain (state.c_PC state.procID) := by","True := by"),
          (3,"(env : Nat → riscv_state → riscv_state)","(env : riscv_state → riscv_state)"),
          (3,"xs.length a 0","xs.length a 2"),
          (2,"Induct_on `xs`","ALL_TAC"),
          (4,"bytes_in_memory_IMP_all_pcs_MEM8_types bytes_in_memory_IMP_all_pcs_MEM8_hypotheses","bytes_in_memory_IMP_all_pcs_MEM8_hypotheses"),
          (4,"bytes_in_memory_thm_types bytes_in_memory_thm_hypotheses","bytes_in_memory_thm_hypotheses")]:
            changed=args.copy();changed[i]=changed[i].replace(old,new)
            with self.subTest(old=old),self.assertRaises(ValueError):M.check(*changed)
