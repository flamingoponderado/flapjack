"""Original rule premises, complete record results and full input carriers stay pinned."""
import importlib.util
from pathlib import Path
import unittest
ROOT=Path(__file__).resolve().parents[2]
spec=importlib.util.spec_from_file_location("next_rule_capture",ROOT / "scripts/hol-probes/check-l3-next-evaluation.py")
m=importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)

class NativeNextRules(unittest.TestCase):
    def test_complete_generic_original_rules(self):
        text="\n".join(m.EXPECTED)+"\n"
        m.check(text)
        for name in ("nextEval", "nextBranch", "nextCond"):
            self.assertIn(name+"_binders=",text)
            self.assertIn(name+"_hypotheses=0",text)
            self.assertIn(name+"_proof=T",text)
        self.assertEqual(text.count("w::rawInstType"),3)
        self.assertEqual(text.count("Run i fetched = nxt"),3)
        self.assertEqual(text.count("nxt.c_NextFetch⦇nxt.procID ↦ NONE⦈"),2)

    def test_narrowed_carriers_circular_premises_and_weakened_results_rejected(self):
        text="\n".join(m.EXPECTED)+"\n"
        mutations=[text.replace("w::rawInstType","w::word32"),
                   text.replace("a::word64","a::word32"),
                   text.replace("Run i fetched = nxt ∧","NextRISCV s = target ∧"),
                   text.replace("Run i fetched = nxt ∧", ""),
                   text.replace("nxt.c_NextFetch⦇nxt.procID ↦ NONE⦈","nxt.c_NextFetch"),
                   text.replace("if b then a else", "if b then 0w else"),
                   text.replace("_hypotheses=0","_hypotheses=1"),
                   text.replace("_proof=T","_proof=F")]
        for mutated in mutations:
            self.assertNotEqual(mutated,text)
            with self.assertRaises(ValueError):m.check(mutated)
