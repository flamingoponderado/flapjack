"""Prospective source checks for independently quantified substitution maps."""

import json
import runpy
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
CHECK = runpy.run_path(str(ROOT / "scripts/check-hol-refs.py"))["infer_subst_submap_observer_errors"]
PATH = "Flapjack/Compiler/Inference/InferProps/Substitution.lean"
PRODUCER_PATH = "Flapjack/Compiler/Inference/Infer/Substitution.lean"
REF = ("cakeml/compiler/inference/inferPropsScript.sml", "infer_subst_submap")
BINDERS = ("type_s1", "type_s2", "list_s1", "list_s2")
SOURCE = (ROOT / PATH).read_text()
PRODUCER = (ROOT / PRODUCER_PATH).read_text()
DOMAIN = (ROOT / "Flapjack/FiniteMap/DomainExact.lean").read_text()
SUBMAP = (ROOT / "Flapjack/FiniteMap/SubmapExact.lean").read_text()
ROWS = json.loads((ROOT / "docs/HOL-THEOREM-MAP.json").read_text())


class InferSubstSubmapSourceTest(unittest.TestCase):
    def check(self, source=SOURCE, path=PATH, ref=REF, binders=BINDERS, producer=PRODUCER,
              domain=DOMAIN, submap=SUBMAP, rows=ROWS):
        return CHECK(source, path, ref, binders, producer, domain, submap, rows)

    def test_actual_statement_and_producer(self):
        self.assertEqual(self.check(), [])

    def test_site_and_independent_binder_metadata(self):
        for args in ({"path": "Other.lean"}, {"ref": (REF[0], "other")},
                     {"binders": ("type_s1", "type_s2", "type_s1", "type_s2")},
                     {"binders": ("type_s2", "type_s1", "list_s1", "list_s2")}):
            with self.subTest(args=args):
                self.assertTrue(self.check(**args))

    def test_weakened_or_changed_conjuncts_fail(self):
        for source in (
            SOURCE.replace("s1.submap s2 ∧\n      {v | tVars", "s2.submap s1 ∧\n      {v | tVars"),
            SOURCE.replace("inferSubst s1 t = inferSubst s2 t)", "inferSubst s1 t = inferSubst s1 t)"),
            SOURCE.replace("s ∈ ts.map tVars", "s ∈ ([] : List (Set Nat))"),
            SOURCE.replace("v ∈ s2.domain \\ s1.domain → m ≤ v", "v ∈ s2.domain \\ s1.domain → v ≤ m", 1),
            SOURCE.replace("ts.map (inferSubst s1) = ts.map (inferSubst s2)",
                           "ts.map (inferSubst s1) = ts.map (inferSubst s1)"),
            SOURCE.replace("(m : Nat),\n      s1.submap", "(m : Nat) (extra : True),\n      s1.submap"),
            SOURCE.replace("open Flapjack.Compiler.Inference.Unify\n", "open Flapjack.Compiler.Inference.Unify\n  Other\n"),
            SOURCE + "\ndef inferSubst := 0\n",
            SOURCE.replace("mutual\n", "abbrev InferT := Bool\nmutual\n", 1),
            SOURCE.replace("mutual\n", "abbrev Nat := Bool\nmutual\n", 1),
            SOURCE.replace("mutual\n", "local abbrev InferT := Bool\nmutual\n", 1),
            SOURCE.replace("mutual\n", "export Other (InferT)\nmutual\n", 1),
            SOURCE.replace("mutual\n", "macro_rules | `(x) => `(True)\nmutual\n", 1),
            SOURCE.replace("(map : HolFiniteMapExact Nat Nat) (key : Nat)",
                           "(map : HolFiniteMapExact Nat Nat) (key : Nat) (extra : True)"),
        ):
            with self.subTest(source=source[-100:]):
                self.assertTrue(self.check(source=source))

    def test_producer_tag_and_review_row_are_required(self):
        self.assertTrue(self.check(producer=PRODUCER.replace("infer_subst_def", "other_def")))
        self.assertTrue(self.check(producer=PRODUCER.replace("| none => .uvar n", "| none => .varDb n")))
        self.assertTrue(self.check(producer=PRODUCER.replace("cases subst", "sorry")))
        self.assertTrue(self.check(domain=DOMAIN.replace("map.lookup key ≠ none", "True")))
        self.assertTrue(self.check(submap=SUBMAP.replace("g.lookup key = some value", "True", 1)))
        rows = [row for row in ROWS if not (row.get("lean_path") == PRODUCER_PATH and
                                            row.get("lean_name") == "inferSubst")]
        self.assertTrue(self.check(rows=rows))
        row = next(row for row in ROWS if row.get("lean_path") == PRODUCER_PATH and
                   row.get("lean_name") == "inferSubst")
        self.assertTrue(self.check(rows=ROWS + [row]))
        self.assertTrue(self.check(rows=[{**item, "statement_status": "reviewed_exact"}
                                         if item == row else item for item in ROWS]))


if __name__ == "__main__":
    unittest.main()
