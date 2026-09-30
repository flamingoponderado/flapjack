"""Inherited-section-premise regressions for finite-map qualifier witnesses."""
import runpy
import unittest
from pathlib import Path

CHECKER = runpy.run_path(str(Path(__file__).resolve().parents[1] / "check-hol-refs.py"))

class AmbientWitnessTest(unittest.TestCase):
    equality = [
        "theorem holFmapAsFiniteSupportEqualityWitness_t",
        "    (left right : HolFiniteMapExact Nat Nat) (k : Nat) :",
        "    left.lookup k = right.lookup k := by exact h left right k",
    ]
    relation = [
        "structure State where",
        "  globals : HolFiniteMapExact Nat Nat",
        "theorem holFmapAsFiniteSupportRelationWitness_State (s : State) :",
        "    State.ofBroad s.toBroad = s := by exact h s",
    ]

    def equality_errors(self, lines):
        return CHECKER["fmap_as_finite_support_equality_errors"](
            lines, "Example.lean",
            "theorem t (left right : HolFiniteMapExact Nat Nat) : left = right := by exact h",
            "t")

    def relation_ok(self, lines):
        return CHECKER["has_fmap_relation_witness"](lines, "State")

    def test_active_section_proof_premise_rejected(self):
        for command in [
            "variable (h : False)", "variables (h : False)",
            "variable (h : ∀ s, State.ofBroad s.toBroad = s)",
            "variable (h : namedPredicate s)", "include h", "omit h",
            "variable (h : False) include h", "variable (h : False) omit h",
        ]:
            with self.subTest(command=command):
                prefix = ["section Assumed", command]
                self.assertTrue(self.equality_errors(prefix + self.equality + ["end Assumed"]))
                self.assertFalse(self.relation_ok(prefix + self.relation + ["end Assumed"]))

    def test_outer_assumption_survives_closed_inner_scope(self):
        prefix = ["section Outer", "variable (h : False)",
                  "namespace Inner", "end Inner"]
        self.assertTrue(self.equality_errors(prefix + self.equality))
        self.assertFalse(self.relation_ok(prefix + self.relation))

    def test_closed_helper_scopes_do_not_poison_witness(self):
        for opening, closing in [("namespace Helpers", "end Helpers"),
                                 ("section Helpers", "end Helpers"),
                                 ("section", "end")]:
            with self.subTest(opening=opening):
                prefix = [opening, "variable (h : False)", "include h", closing]
                self.assertEqual(self.equality_errors(prefix + self.equality), [])
                self.assertTrue(self.relation_ok(prefix + self.relation))

    def test_commands_after_witness_do_not_change_its_binders(self):
        suffix = ["section Later", "variable (h : False)", "include h", "end Later"]
        self.assertEqual(self.equality_errors(self.equality + suffix), [])
        self.assertTrue(self.relation_ok(self.relation + suffix))

    def test_comments_strings_and_quoted_identifiers_are_not_commands(self):
        prefix = ['/- namespace Helpers variable (h : False) include h -/',
                  'def text := "section variable include omit end"',
                  'def «variable» := 0', '-- variable (h : False)']
        self.assertEqual(self.equality_errors(prefix + self.equality), [])
        self.assertTrue(self.relation_ok(prefix + self.relation))

    def test_mutual_end_does_not_close_outer_assumption_scope(self):
        prefix = ["section Outer", "variable (h : False)", "mutual", "end"]
        self.assertTrue(self.equality_errors(prefix + self.equality))
        self.assertFalse(self.relation_ok(prefix + self.relation))

    def test_plural_equality_witness_rejects_inherited_premise(self):
        second = [line.replace("Witness_t", "Witness_t_2").replace(
            "left.lookup k = right.lookup k", "right.lookup k = left.lookup k")
            for line in self.equality]
        first = [line.replace("Witness_t", "Witness_t_1") for line in self.equality]
        lines = ["section", "variable (h : False)"] + first + second + ["end"]
        errors = CHECKER["fmap_as_finite_support_equalities_errors"](
            lines, "Example.lean",
            "theorem t (left right : HolFiniteMapExact Nat Nat) : left = right ∧ right = left := by exact h",
            "t")
        self.assertEqual(len(errors), 2)
        self.assertTrue(all("inherited proof premises" in error for error in errors))

    def test_current_shmem_closed_helper_scope_is_accepted(self):
        root = Path(__file__).resolve().parents[2]
        lines = (root / "Flapjack/Pancake/CrepToLoop/Proofs/NCompileCorrect/ShMem.lean").read_text().splitlines()
        for carrier in ["CrepToLoopContextExact", "CrepSemHOLState", "LoopSemStateFiniteExact"]:
            with self.subTest(carrier=carrier):
                self.assertTrue(CHECKER["has_fmap_relation_witness"](lines, carrier))

    def test_variables_parameter_and_let_names_are_not_ambient_commands(self):
        prefix = ["def f (variables : List Nat) := variables",
                  "def g := let variables := [1]; variables",
                  "def multiline (", "    variables : List Nat) := variables"]
        self.assertEqual(self.equality_errors(prefix + self.equality), [])
        self.assertTrue(self.relation_ok(prefix + self.relation))

    def test_command_quotation_does_not_close_active_scope(self):
        prefix = ["section Outer", "variable (h : False)",
                  "def syntaxExample := `(command| end Outer)"]
        self.assertTrue(self.equality_errors(prefix + self.equality))
        self.assertFalse(self.relation_ok(prefix + self.relation))
