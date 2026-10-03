"""Native step bit rewrites preserve complete original carrier/conjunct domains."""
import importlib.util
from pathlib import Path
import unittest
ROOT=Path(__file__).resolve().parents[2]
SPEC=importlib.util.spec_from_file_location("bit_rewrites",ROOT / "scripts/hol-probes/check-l3-step-bit-rewrites.py")
MODULE=importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)
class BitRewrites(unittest.TestCase):
    def test_original_capture(self):
        MODULE.check((ROOT / "scripts/hol-probes/l3_step_bit_rewrites_probe.out").read_text())
    def test_reject_carrier_clause_and_premise_mutations(self):
        text="\n".join(MODULE.EXPECTED)
        for before,after in [("word64","word32"),("word8","word7"),("word5","word4"),
            ("x7::bool;",""),("∀w v.","∀w v. w = 0w ⇒"),
            ("+ v)","+ 0w)"),("x + w ≪ 1","(x + w) ≪ 1"),
            ("[b3; b2; b1; b0; T]","[b3; b2; b1; b0; F]"),
            ("hypotheses=0","hypotheses=1"),("proof=T","proof=F")]:
            with self.subTest(before=before):
                self.assertIn(before,text)
                with self.assertRaises(ValueError):MODULE.check(text.replace(before,after))
if __name__=="__main__":unittest.main()
