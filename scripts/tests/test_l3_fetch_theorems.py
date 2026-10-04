"""Original full fetch statements retain every premise and complete state result."""
import importlib.util
from pathlib import Path
import unittest
ROOT=Path(__file__).resolve().parents[2]
SPEC=importlib.util.spec_from_file_location("fetch_theorems",ROOT / "scripts/hol-probes/check-l3-fetch-theorems.py")
MODULE=importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)
class FetchTheorems(unittest.TestCase):
    def test_original_capture(self):MODULE.check((ROOT / "scripts/hol-probes/l3_fetch_theorems_probe.out").read_text())
    def test_lean_full_signature_drift(self):
        text=(ROOT / MODULE.LEAN_PATH).read_text()
        changes=[
            ("xs : List Bool", "xs : BitVec 32"),
            ("xE xF : Bool", "xE : Bool"),
            ("yE yF : Bool", "yE : Bool"),
            ("mstatus.VM = 0#5", "mstatus.VM = 1#5"),
            ("s.c_PC s.procID + 3#64", "s.c_PC s.procID + 2#64"),
            ("[x0,x1,x2,x3,x4,x5,x6,x7,x8", "[x1,x0,x2,x3,x4,x5,x6,x7,x8"),
            ("[y0,y1,y2,y3,y4,y5,y6,y7,y8", "[y1,y0,y2,y3,y4,y5,y6,y7,y8"),
            ("¬(xE = true ∧ xF = true)", "True"),
            ("xE = true ∧ xF = true) :", "True) :"),
            (".Half (holV2w 16 xs)", ".Half (holV2w 8 xs)"),
            (".Word (holV2w 32 xs)", ".Word (holV2w 16 xs)"),
            ("holUpdate s.procID 2#64 s.c_Skip", "holUpdate s.procID 4#64 s.c_Skip"),
            ("holUpdate s.procID 4#64 s.c_Skip", "s.c_Skip"),
            ("theorem fetch16 (s :", "theorem fetch16 (assumed : True) (s :")]
        for old,new in changes:
            with self.subTest(old=old):
                self.assertIn(old,text)
                prefix,body=text.split("theorem fetch16",1)
                with self.assertRaises(ValueError):MODULE.check_lean(prefix+("theorem fetch16"+body).replace(old,new,1))
    def test_lean_comments_formatting_and_proofs_are_outside_statement(self):
        text=(ROOT / MODULE.LEAN_PATH).read_text()
        changed=text.replace("(xs : List Bool)", "(xs /- comment /- nested -/ -/ : List Bool)")
        changed=changed.replace("[x0,x1,", "[x0, x1, ")
        changed=changed.replace("  rcases h with", "  skip\n  rcases h with")
        MODULE.check_lean(changed)
    def test_commented_baseline_and_duplicate_do_not_mask_drift(self):
        text=(ROOT / MODULE.LEAN_PATH).read_text()
        signature=MODULE.LEAN_EXPECTED["fetch16"]
        for changed in ["/- "+signature+" -/\n"+text.replace(".Half (holV2w 16 xs)",".Half (holV2w 8 xs)"),
                        text+"\n"+signature+" := by sorry"]:
            with self.assertRaises(ValueError):MODULE.check_lean(changed)
    def test_reject_narrowing_dropped_premises_and_partial_results(self):
        text="\n".join(MODULE.EXPECTED)
        changes=[("s::riscv_state","s::word64"),("xs::bool list","xs::word32"),
          ("yF::bool;",""),("word16","word8"),("word32","word16"),
          ("mstatus.VM = 0w","mstatus.VM = 1w"),("s.c_PC s.procID + 3w","s.c_PC s.procID + 2w"),
          ("¬(xE ∧ xF) ⇒","T ⇒"),("xs = [x0;","T ∧ [x0;"),
          ("s with c_Skip := s.c_Skip⦇s.procID ↦ 2w⦈","s"),
          ("s with c_Skip := s.c_Skip⦇s.procID ↦ 4w⦈","s"),
          ("Fetch s = (Word","Fetch s = (Half"),
          ("hypotheses=0","hypotheses=1"),("proof=T","proof=F")]
        for before,after in changes:
            with self.subTest(before=before):
                self.assertIn(before,text)
                with self.assertRaises(ValueError):MODULE.check(text.replace(before,after))
if __name__=="__main__":unittest.main()
