"""Fail-closed tests for the prospective generalization map source gate."""

import runpy
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
CHECKER = runpy.run_path(str(ROOT / "scripts/check-hol-refs.py"))
CHECK = CHECKER["generalise_parameter_tuple_result_errors"]
LEAN_PATH = "Flapjack/Compiler/Inference/Infer/Generalise.lean"
HOL_REF = ("cakeml/compiler/inference/inferScript.sml", "generalise_def")
SOURCE = (ROOT / LEAN_PATH).read_text()


class GeneraliseParameterTupleSourceTest(unittest.TestCase):
    def test_command_style_hol_attributes_fail_closed(self):
        scan = CHECKER["unsupported_hol_attribute_commands"]
        self.assertEqual(scan('attribute [hol "p" "n"] a b'), [1])
        self.assertEqual(scan('attribute [simp,\n hol "p" "n"] a'), [1])
        self.assertEqual(scan('attribute [other [x], «hol» "p" "n"] a'), [1])
        self.assertEqual(scan('def s := "attribute [hol x] a"'), [])
        self.assertEqual(scan('-- attribute [hol "p" "n"] a\n@[hol "p" "n"]\ndef a := 0'), [])
        self.assertEqual(scan('attribute [simp] a'), [])

    def test_prospective_post_mutual_command_is_pinned(self):
        command = ('attribute [hol "cakeml/compiler/inference/inferScript.sml" "generalise_def"\n'
                   '  (fmap_as_finite_support_parameter_tuple_result := '
                   '(map_parameter := subst) (result_component := component_2))]\n'
                   '  generaliseMap generaliseListMap\n\n')
        anchor = 'termination_by ts => sizeOf ts\nend\n\nmutual\n'
        self.assertEqual(SOURCE.count(anchor), 1)
        fixture = SOURCE.replace(anchor, anchor.replace('mutual\n', command + 'mutual\n'), 1)
        check = CHECKER["prospective_generalise_command_errors"]
        self.assertEqual(check(fixture, LEAN_PATH), [])
        for bad in (
            fixture.replace('generaliseMap generaliseListMap', 'generaliseMap other'),
            fixture.replace('component_2', 'component_1'),
            fixture.replace('generaliseMap generaliseListMap', 'generaliseMap generaliseListMap extra'),
            fixture.replace(command, command + command),
            fixture.replace('def generaliseMap', '@[hol "cakeml/compiler/inference/inferScript.sml" "generalise_def"]\ndef generaliseMap', 1),
            fixture.replace(command, 'mutual\ndef dummy : List Nat → Nat := fun _ => 0\n'
                            'termination_by ts => sizeOf ts\nend\n\n' + command, 1),
        ):
            with self.subTest(source=bad[-200:]):
                self.assertTrue(check(bad, LEAN_PATH))
        self.assertTrue(check(fixture, 'Other.lean'))
        self.assertTrue(CHECKER["unsupported_hol_attribute_commands"](fixture))

    def check(self, source=SOURCE, name="generaliseMap", path=LEAN_PATH,
              hol=HOL_REF, parameter="subst", component="component_2"):
        return CHECK(source, path, name, hol, parameter, component)

    def test_actual_operations(self):
        self.assertEqual(self.check(), [])
        self.assertEqual(self.check(name="generaliseListMap"), [])

    def test_scanner_retains_valid_and_malformed_qualifiers(self):
        qualifier = ("(fmap_as_finite_support_parameter_tuple_result := "
                     "(map_parameter := subst) (result_component := component_2))")
        tag = f'@[hol "{HOL_REF[0]}" "{HOL_REF[1]}" {qualifier}]'
        scan = lambda text: list(CHECKER["hol_attribute_sites"](
            [text], include_generalise_map=True))[0][-1]
        self.assertEqual(scan(tag), ("subst", "component_2"))
        self.assertEqual(scan(tag.replace("component_2", "component_1")),
                         ("subst", "component_1"))
        self.assertEqual(scan(tag.replace(qualifier, qualifier + " " + qualifier)), ("", ""))
        self.assertEqual(scan(tag.replace("(map_parameter := subst)", "(map_parameter := )")), ("", ""))
        self.assertEqual(scan(tag.replace(qualifier, "")), ())

    def test_valid_and_malformed_uses_remain_disabled(self):
        pending = CHECKER["prospective_generalise_map_errors"]
        for name in ("generaliseMap", "generaliseListMap"):
            self.assertEqual(pending(SOURCE, LEAN_PATH, name, HOL_REF,
                                     ("subst", "component_2")),
                             ["generalization map qualifier is not enabled"])
        self.assertIn("generalization map qualifier is not enabled",
                      pending(SOURCE, LEAN_PATH, "generaliseMap", HOL_REF, ("", "")))

    def test_unqualified_reference_is_rejected(self):
        reference = CHECKER["generalise_reference_errors"]
        for name in ("generaliseMap", "generaliseListMap"):
            self.assertEqual(reference(SOURCE, LEAN_PATH, name, HOL_REF, ()),
                             ["generalise_def requires its combined map qualifier"])
        self.assertEqual(reference(SOURCE, LEAN_PATH, "other", (HOL_REF[0], "other"), ()), [])

    def test_only_the_reviewed_sites_and_positions_are_eligible(self):
        self.assertTrue(self.check(path="Other.lean"))
        self.assertTrue(self.check(hol=(HOL_REF[0], "generalise_list_length")))
        self.assertTrue(self.check(name="other"))
        self.assertTrue(self.check(parameter="other"))
        self.assertTrue(self.check(component="component_1"))

    def test_rejects_raw_wrong_or_additional_maps(self):
        header = "def generaliseMap (minimum next : Nat) (subst : HolFiniteMapExact Nat Nat) :"
        self.assertIn(header, SOURCE)
        self.assertTrue(self.check(SOURCE.replace(header, header.replace(
            "HolFiniteMapExact Nat Nat", "Nat → Option Nat"), 1)))
        self.assertTrue(self.check(SOURCE.replace(header, header.replace(
            "HolFiniteMapExact Nat Nat", "HolFiniteMapExact Nat Bool"), 1)))
        self.assertTrue(self.check(SOURCE.replace(header, header.replace(
            " :", " (extra : HolFiniteMapExact Nat Nat) :", 1), 1)))
        result = "InferT → Nat × HolFiniteMapExact Nat Nat × InferT"
        self.assertTrue(self.check(SOURCE.replace(result,
            "InferT → Nat × InferT × HolFiniteMapExact Nat Nat", 1)))

    def test_rejects_hidden_binders_and_duplicate_declarations(self):
        self.assertTrue(self.check(SOURCE.replace("mutual\n", "variable (h : False)\nmutual\n", 1)))
        self.assertTrue(self.check(SOURCE.replace("mutual\n", "local notation \"bogus\" => 0\nmutual\n", 1)))
        self.assertTrue(self.check(SOURCE.replace("mutual\n", "local infix:50 \"bogus\" => Nat.add\nmutual\n", 1)))
        self.assertTrue(self.check(SOURCE.replace("mutual\n", "scoped syntax \"bogus\" : term\nmutual\n", 1)))
        self.assertTrue(self.check(SOURCE.replace("mutual\n", "open Shadow\nmutual\n", 1)))
        self.assertTrue(self.check(SOURCE.replace("mutual\n", "namespace Shadow\nmutual\n", 1)))
        self.assertTrue(self.check(SOURCE + "\ndef generaliseMap := 0\n"))
        self.assertTrue(self.check(SOURCE +
            "\naxiom holFmapAsFiniteSupportParameterTupleResultWitness_generaliseMap : True\n"))

    def test_checks_both_complete_mutual_bodies(self):
        mutations = [
            ("if minimum ≤ n then", "if minimum < n then"),
            ("subst.updateEq (n, next)", "subst.updateEq (next, n)"),
            ("(1, subst.updateEq", "(0, subst.updateEq"),
            ("generaliseListMap minimum (count + next) subst ts",
             "generaliseListMap minimum next subst ts"),
            ("(count + count', subst, t :: ts)", "(count', subst, t :: ts)"),
            ("  | .varDb n => (0, subst, .varDb n)\n", ""),
            ("termination_by t => sizeOf t", ""),
        ]
        for old, new in mutations:
            with self.subTest(old=old):
                self.assertIn(old, SOURCE)
                changed = SOURCE.replace(old, new, 1)
                self.assertTrue(self.check(changed))
                self.assertTrue(self.check(changed, name="generaliseListMap"))

    def test_rejects_missing_vacuous_or_conditional_witness(self):
        name = "holFmapAsFiniteSupportParameterTupleResultWitness_generaliseMap"
        self.assertTrue(self.check(SOURCE.replace("theorem " + name, "theorem missing", 1)))
        self.assertTrue(self.check(SOURCE.replace(
            "(sp2fm (fm2sp subst)).lookup key = subst.lookup key ∧",
            "subst.lookup key = subst.lookup key ∧", 1)))
        self.assertTrue(self.check(SOURCE.replace(
            "(t : InferT) (key : Nat) :\n    (sp2fm",
            "(t : InferT) (key : Nat) (h : False) :\n    (sp2fm", 1)))
        self.assertTrue(self.check(SOURCE.replace(
            "(generaliseMap minimum next subst t).2.1.lookup key",
            "(generaliseMap next minimum subst t).2.1.lookup key", 1)))
        self.assertTrue(self.check(SOURCE.replace(
            "sptLookup key (Infer.generalise minimum next (fm2sp subst) t).2.1",
            "subst.lookup key", 1)))


if __name__ == "__main__":
    unittest.main()
