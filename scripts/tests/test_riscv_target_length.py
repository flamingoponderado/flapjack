import importlib.util
from pathlib import Path
import unittest
ROOT=Path(__file__).resolve().parents[2]
SPEC=importlib.util.spec_from_file_location("length_guard",ROOT/"scripts/hol-probes/check-riscv-target-length.py")
M=importlib.util.module_from_spec(SPEC);SPEC.loader.exec_module(M)
class LengthTests(unittest.TestCase):
    def test_full_original_and_negative_guards(self):
        args=[(ROOT/p).read_text() for p in (
          "scripts/hol-probes/riscv_target_length_probe.out",
          "cakeml/compiler/encoders/riscv/proofs/riscv_targetProofScript.sml",
          "scripts/hol-probes/riscv_target_length_probeScript.sml",
          "Flapjack/RiscV/CorrectnessEncoding/Length.lean",
          "scripts/hol-probes/regenerate.sh")]
        M.check(*args)
        for i,old,new in [(0,"MOD 4","MOD 2"),(0,"i : :64 asm","i : :instruction"),
          (0,"hypotheses=0","hypotheses=1"),(0,"proved=T","proved=F"),
          (2,"asmLib.asm_cases_tac `i`","ALL_TAC"),
          (2,"riscv_encode_not_nil]","TRUTH]"),
          (3,"(i : HolAsm 64)","(i : HolAsm 64) (h : asmOkExact i riscvConfig = true)"),
          (3,"riscvEnc i ≠ []","True"),
          (4,"riscv_encoding_types riscv_encoding_hypotheses","riscv_encoding_hypotheses")]:
            changed=args.copy();changed[i]=changed[i].replace(old,new)
            with self.subTest(old=old),self.assertRaises(ValueError):M.check(*changed)
