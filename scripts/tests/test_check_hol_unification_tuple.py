"""Fail-closed source audit for the prospective unification tuple qualifier."""

import runpy
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
CHECK = runpy.run_path(str(ROOT / "scripts/check-hol-refs.py"))["unification_tuple_relation_errors"]
SOURCE = (ROOT / "Flapjack/HOL/Unification/UnifDef/WellFounded.lean").read_text()
OWNER = (ROOT / "Flapjack/HOL/Unification/UnifDef.lean").read_text()
HOL = ("HOL/examples/algorithms/unification/triangular/first-order/unifDefScript.sml", "WF_uR")


class UnificationTupleQualifierTest(unittest.TestCase):
    def check(self, source=SOURCE, owner=OWNER, positions=("component_1",), hol=HOL):
        return CHECK(source, owner, positions, hol)

    def test_actual_relation_and_tuple_codecs(self):
        self.assertEqual(self.check(), [])

    def test_wrong_source_or_positions(self):
        self.assertTrue(self.check(positions=("component_2",)))
        self.assertTrue(self.check(positions=("component_1", "component_1")))
        self.assertTrue(self.check(positions=()))
        self.assertTrue(self.check(positions=("component_1", "component_2")))
        self.assertTrue(self.check(hol=(HOL[0], "uR_def")))
        self.assertTrue(self.check(hol=("wrongScript.sml", HOL[1])))

    def test_wrong_relation_and_extra_premise(self):
        self.assertTrue(self.check(SOURCE.replace("WellFounded (@uR α)", "WellFounded (fun _ _ => True)")))
        self.assertTrue(self.check(SOURCE.replace(
            "{α : Type} : WellFounded (@uR α)", "{α : Type} (h : True) : WellFounded (@uR α)")))
        self.assertTrue(self.check(SOURCE + "\ndef uR := True\n"))

    def test_rejects_relation_macro_and_qualified_shadow(self):
        macro = ('local macro:max "@" "uR" : term => `(emptyReviewRelation)\n')
        source = SOURCE.replace("namespace Flapjack.HOL.Unification\n",
                                "namespace Flapjack.HOL.Unification\n" + macro)
        self.assertIn("unification tuple qualifier forbids local syntax or name rebinding in target",
                      self.check(source))
        self.assertIn("unification tuple qualifier rejects shadowed relation or carriers",
                      self.check(SOURCE + "\nprivate def Other.uR := True\n"))

    def test_rejects_raw_strings_and_fake_import_in_string(self):
        self.assertIn("unification tuple audit rejects raw string literals",
                      self.check(SOURCE + '\ndef fake := r#"\nnamespace Fake\n"#\n'))
        source = SOURCE.replace("public import Flapjack.HOL.Unification.UnifDef",
                                'def fake := "public import Flapjack.HOL.Unification.UnifDef"')
        self.assertIn("unification tuple qualifier requires the exact relation owner import",
                      self.check(source))

    def test_raw_map_wrong_slots_and_invertible_permutation(self):
        self.assertTrue(self.check(SOURCE.replace("HolFiniteMapExact Nat (Term α)", "(Nat → Option (Term α))")))
        self.assertTrue(self.check(SOURCE.replace("(FiniteMapBroad.toBroad p.1, p.2.1, p.2.2)",
                                                  "(FiniteMapBroad.toBroad p.1, p.2.2, p.2.1)")))
        self.assertTrue(self.check(SOURCE.replace("(FiniteMapBroad.ofBroad p.1, p.2.1, p.2.2)",
                                                  "(FiniteMapBroad.ofBroad p.1, p.2.2, p.2.1)")))
        swapped = SOURCE.replace("(FiniteMapBroad.toBroad p.1, p.2.1, p.2.2)",
                                 "(FiniteMapBroad.toBroad p.1, p.2.2, p.2.1)")
        swapped = swapped.replace("(FiniteMapBroad.ofBroad p.1, p.2.1, p.2.2)",
                                  "(FiniteMapBroad.ofBroad p.1, p.2.2, p.2.1)")
        self.assertTrue(self.check(swapped))

    def test_missing_vacuous_or_conditional_witness(self):
        self.assertTrue(self.check(SOURCE.replace("holFmapAsFiniteSupportTupleWitness_uRWellFounded_reverse",
                                                  "wrongWitness")))
        self.assertTrue(self.check(SOURCE.replace("uRTupleOfBroad (uRTupleToBroad p) = p", "p = p")))
        self.assertTrue(self.check(SOURCE.replace("(p : HolFiniteMapExact Nat (Term α) × Term α × Term α) :\n    uRTupleOfBroad",
                                                  "(p : HolFiniteMapExact Nat (Term α) × Term α × Term α) (h : True) :\n    uRTupleOfBroad")))

    def test_owner_and_import_are_pinned(self):
        self.assertTrue(self.check(SOURCE.replace("public import Flapjack.HOL.Unification.UnifDef",
                                                  "public import Flapjack.HOL.Unification.Walk")))
        self.assertTrue(self.check(owner=OWNER.replace("right.1.submap left.1", "left.1.submap right.1")))
        self.assertTrue(self.check(owner=OWNER.replace('"uR_def"', '"uP_def"')))
        wrong = OWNER.replace("uR (sx, c1, c2) (s, t1, t2) ↔\n    wfs sx",
                              "True ∧ wfs sx")
        self.assertIn("unification tuple qualifier requires the complete uREq statement",
                      self.check(owner=wrong))
        tag = ('@[hol "HOL/examples/algorithms/unification/triangular/first-order/'
               'unifDefScript.sml" "uR_def"\n  (fmap_as_finite_support_parameters := [sx, s])]')
        self.assertIn(tag, OWNER)
        fake = OWNER.replace(tag, "") + (
            '\ndef fake : String := "@[hol '
            '\\"HOL/examples/algorithms/unification/triangular/first-order/unifDefScript.sml\\" '
            '\\"uR_def\\" (fmap_as_finite_support_parameters := [sx, s])] theorem uREq "\n'
        )
        self.assertIn("unification tuple qualifier requires the reviewed uREq attribute",
                      self.check(owner=fake))

    def test_extra_binders_and_ambient_commands(self):
        self.assertTrue(self.check(SOURCE.replace("{α : Type} : WellFounded (@uR α)",
                                                  "{α : Type} [Inhabited α] : WellFounded (@uR α)")))
        self.assertTrue(self.check(SOURCE.replace("namespace Flapjack.HOL.Unification\n",
                                                  "namespace Flapjack.HOL.Unification\nvariable (h : True)\n")))
        self.assertTrue(self.check(SOURCE.replace("namespace Flapjack.HOL.Unification",
                                                  "namespace Different.Namespace")))
        self.assertTrue(self.check(SOURCE + "\nnamespace Extra\nend Extra\n"))

    def test_owner_ambient_macro_namespace_and_shadows(self):
        ambient = OWNER.replace(
            "/-- Canonical codec roundtrip for the right substitution in the relation. -/",
            "variable (extraPremise : False)\ninclude extraPremise\n"
            "/-- Canonical codec roundtrip for the right substitution in the relation. -/", 1)
        start = ambient.index("theorem uREq ")
        end = ambient.index(":= Iff.rfl", start) + len(":= Iff.rfl")
        ambient = ambient[:end] + "\nomit extraPremise\n" + ambient[end:]
        self.assertIn("unification tuple qualifier forbids ambient variables in owner",
                      self.check(owner=ambient))
        self.assertIn("unification tuple qualifier forbids local syntax or name rebinding in owner",
                      self.check(owner=OWNER + '\nlocal macro:max "@" "uR" : term => `(False)\n'))
        self.assertIn("unification tuple qualifier requires the exact namespace in owner",
                      self.check(owner=OWNER.replace("namespace Flapjack.HOL.Unification", "namespace Other")))
        self.assertIn("unification tuple qualifier rejects shadowed owner carriers or primitives",
                      self.check(owner=OWNER + "\nprivate def Other.Term := Nat\n"))
        self.assertIn("unification tuple qualifier rejects an alternative qualified uR",
                      self.check(owner=OWNER + "\nprivate def Other.uR := True\n"))


if __name__ == "__main__":
    unittest.main()
