import importlib.util
from pathlib import Path
import unittest
ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location("state_guard", ROOT / "scripts/hol-probes/check-riscv-target-state.py")
M = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(M)
class StateTests(unittest.TestCase):
    def test_full_original_and_negative_guards(self):
        args = [(ROOT / p).read_text() for p in (
            "scripts/hol-probes/riscv_target_state_probe.out",
            "cakeml/compiler/encoders/riscv/riscv_targetScript.sml",
            "Flapjack/Compiler/Encoders/RiscV/Target/State.lean",
            "scripts/hol-probes/regenerate.sh")]
        M.check(*args)
        for i, old, new in [(0,"ARB.get_fp_reg","ARB"), (0,"word5 # word2","word64 # word2"),
             (0,"hypotheses=0","hypotheses=1"), (0,"proved=T","proved=F"),
             (1,"THE (NextRISCV s)","s"), (1,"aligned 2","aligned 1"),
             (2,"holThe (RiscV.L3.Step.NextRISCV s)","s"),
             (2,"(s.exception == exception.NoException) &&","true &&"),
             (2,"SetSep.fun2Set (s.MEM8, d)","SetSep.fun2Set (s.MEM8, fun _ => True)"),
             (2,"(holArb (HolAsmTarget 64 riscv_state RiscVProjection)).getFpReg",
              "holArb (riscv_state → Nat → BitVec 64)"),
             (2,"BitVec.ofNat 5 n","BitVec.ofNat 5 (n+1)"),
             (3,"riscv_target_fp_field riscv_target_fp_type","riscv_target_fp_type")]:
            changed = args.copy(); changed[i] = changed[i].replace(old,new)
            with self.subTest(old=old), self.assertRaises(ValueError): M.check(*changed)
