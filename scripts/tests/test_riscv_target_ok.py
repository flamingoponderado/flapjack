import importlib.util
from pathlib import Path
import unittest
ROOT=Path(__file__).resolve().parents[2]
SPEC=importlib.util.spec_from_file_location("target_ok_guard",ROOT/"scripts/hol-probes/check-riscv-target-ok.py")
M=importlib.util.module_from_spec(SPEC);SPEC.loader.exec_module(M)
class TargetOkTests(unittest.TestCase):
    def test_full_and_negative_guards(self):
        args=M.inputs();M.check(*args)
        for i,old,new in [(0,"hypotheses=0","hypotheses=1"),(0,"proved=T","proved=F"),
          (0,"word5 # word2","word64 # word2"),(1,"all_tac","ALL_TAC"),
          (2,"blastLib.FULL_BBLAST_TAC","ALL_TAC"),
          (3,"theorem riscv_target_ok :","theorem riscv_target_ok (h : encOk riscvConfig) :"),
          (3,"targetOk riscvTarget :=","True :="),
          (4,"riscv_target_ok_types riscv_target_ok_hypotheses","riscv_target_ok_hypotheses")]:
            changed=args.copy();changed[i]=changed[i].replace(old,new)
            with self.subTest(old=old),self.assertRaises(ValueError):M.check(*changed)
        changed=args.copy();changed[4]+="\n"+args[4].split("\nrun_probe riscv_target_ok_probeScript.sml",1)[1].join(["run_probe riscv_target_ok_probeScript.sml",""])
        with self.assertRaises(ValueError):M.check(*changed)
