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
