import importlib.util
from pathlib import Path
import unittest
ROOT=Path(__file__).resolve().parents[2]
SPEC=importlib.util.spec_from_file_location("immediate_guard",ROOT/"scripts/hol-probes/check-riscv-target-immediate.py")
M=importlib.util.module_from_spec(SPEC);SPEC.loader.exec_module(M)
class ImmediateTests(unittest.TestCase):
    def test_full_and_negative_guards(self):
        args=M.inputs();M.check(*args)
        for i,old,new in [(0,"hypotheses=0","hypotheses=1"),(0,"proved=T","proved=F"),
          (0,"c : :word64","c : :word32"),(0,"@@ 0w : :word32","@@ 0w : :word64"),
          (1,"c <= 0x7FFFF7FFw","c <= 0x7FFFFFFFw"),
          (2,"blastLib.BBLAST_PROVE","TRUTH"),(2,"val () = wordsLib.guess_lengths();",""),
          (3,".setWidth 64 = 0","= 0"),(3,"c.sle 0x7FF = true","True"),
          (3,"(c : BitVec 64)","(c : BitVec 64) (run : True)"),
          (3,"(0 : BitVec 12)","(0 : BitVec 20)"),
          (4,"lem4_types lem4_hypotheses","lem4_hypotheses")]:
            changed=args.copy();changed[i]=changed[i].replace(old,new)
            with self.subTest(old=old),self.assertRaises(ValueError):M.check(*changed)
        changed=args.copy();changed[4]+= "\nrun_probe riscv_target_immediate_probeScript.sml riscv_target_immediate_probe.out\n"
        with self.assertRaises(ValueError):M.check(*changed)
