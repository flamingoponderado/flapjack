"""Fail-closed coverage of the approved total-function inhabitant qualifier."""
import runpy
import unittest
from pathlib import Path

SCRIPTS = Path(__file__).resolve().parents[1]
REFS = runpy.run_path(str(SCRIPTS / "check-hol-refs.py"))
MAP = runpy.run_path(str(SCRIPTS / "check_hol_theorem_map.py"))
EXPORT = runpy.run_path(str(SCRIPTS / "check_hol_ref_export.py"))


class TotalFunctionInhabitantsCheckerTest(unittest.TestCase):
    valid = (
        "noncomputable def alookupLemma {α : Type} {β : Type} [Nonempty α] [Nonempty β] "
        "(l : List (α × β)) (x : α) : β := "
        "holThe ((l.find? (fun p => p.1 = x)).map Prod.snd)"
    )

    def errors(self, signature=None, source=None, names=("α", "β")):
        return REFS["total_function_inhabitants_errors"](
            signature if signature is not None else self.valid,
            source if source is not None else self.valid,
            names,
        )

    def test_accepts_listed_type_binders_with_a_rendering(self):
        self.assertEqual(self.errors(), [])
        inhabited = self.valid.replace("[Nonempty β]", "[Inhabited β]")
        self.assertEqual(self.errors(signature=inhabited, source=inhabited), [])

    def test_rejects_unlisted_instance(self):
        self.assertTrue(self.errors(names=("α",)))
        self.assertTrue(self.errors(names=()))

    def test_rejects_listed_name_without_an_instance(self):
        source = self.valid.replace("[Nonempty β]", "")
        self.assertTrue(self.errors(signature=source, source=source))
        doubled = self.valid.replace("[Nonempty β]", "[Nonempty β] [Inhabited β]")
        self.assertTrue(self.errors(signature=doubled, source=doubled))

    def test_rejects_a_name_that_is_not_a_type_binder(self):
        source = self.valid.replace("{β : Type}", "(β : Nat)")
        self.assertTrue(self.errors(signature=source, source=source))

    def test_rejects_a_declaration_without_a_reviewed_rendering(self):
        source = self.valid.replace(
            "holThe ((l.find? (fun p => p.1 = x)).map Prod.snd)", "x")
        self.assertTrue(self.errors(source=source))

    def test_rejects_duplicate_or_empty_names(self):
        single = (
            "noncomputable def holHead {α : Type} [Nonempty α] (l : List α) : α := holHd l"
        )
        self.assertTrue(self.errors(signature=single, source=single, names=("α", "α")))
        self.assertTrue(self.errors(names=("α", "")))

    def test_duplicate_binder_is_the_only_error(self):
        single = (
            "noncomputable def holHead {α : Type} [Nonempty α] (l : List α) : α := holHd l"
        )
        errors = self.errors(signature=single, source=single, names=("α", "α"))
        self.assertEqual(len(errors), 1, errors)
        self.assertIn("more than once", errors[0])

    def test_attribute_scanner_reports_the_listed_binders(self):
        def listed(text):
            site = list(REFS["hol_attribute_sites"](
                ['@[hol "cakeml/compiler/backend/proofs/wordPropsScript.sml" '
                 '"ALOOKUP_lemma" ' + text + ']'],
                include_total_function_inhabitants=True))[0]
            return site[-1]

        self.assertEqual(listed("(total_function_inhabitants := [α, β])"), ("α", "β"))
        self.assertTrue(self.errors(names=listed("(total_function_inhabitants := [])")))
        self.assertTrue(self.errors(names=listed(
            "(total_function_inhabitants := [α]) (total_function_inhabitants := [β])")))


class TotalFunctionInhabitantsManifestTest(unittest.TestCase):
    hol_path = "cakeml/compiler/backend/proofs/wordPropsScript.sml"
    hol_name = "ALOOKUP_lemma"
    lean_path = "Flapjack/Example.lean"
    lean_name = "alookupLemma"

    def record(self, status="reviewed_total_function_inhabitants",
               inhabitants=("α", "β"), reviewer=None):
        record = {
            "hol_path": self.hol_path,
            "hol_name": self.hol_name,
            "lean_path": self.lean_path,
            "lean_name": self.lean_name,
            "statement_status": status,
            "reviewer": reviewer or (
                "source comparison of the total_function_inhabitants rendering holThe"),
        }
        if inhabitants:
            record["total_function_inhabitants"] = list(inhabitants)
        return record

    def tagged(self, inhabitants=("α", "β")):
        return {(self.lean_path, self.lean_name): (
            self.hol_path, self.hol_name,
            (), (), (), (), False, (), False, False, (), (), None, (), (), False,
            False, (), (), (), (), (), inhabitants,
        )}

    def validate(self, record, inhabitants=("α", "β")):
        return MAP["validate_inventory"](
            [record], set(), self.tagged(inhabitants), set())

    def test_accepts_the_qualifier_alone(self):
        self.assertEqual(self.validate(self.record()), [])

    def test_rejects_reviewed_exact(self):
        self.assertTrue(self.validate(self.record(status="reviewed_exact")))

    def test_rejects_a_manifest_attribute_mismatch(self):
        self.assertTrue(self.validate(self.record(inhabitants=("α",)), ("α", "β")))

    def test_rejects_the_status_without_the_qualifier(self):
        self.assertTrue(self.validate(self.record(), ()))

    def test_rejects_a_note_that_does_not_name_the_qualifier(self):
        self.assertTrue(self.validate(self.record(reviewer="source comparison of the rendering")))

    def test_status_and_export_registration(self):
        self.assertIn("reviewed_total_function_inhabitants", MAP["VALID_STATUSES"])
        self.assertIn("total_function_inhabitants", EXPORT["ALLOWED_QUALIFIERS"])
        self.assertIn(
            "total_function_inhabitants",
            EXPORT["manifest_qualifiers"](self.record()),
        )


if __name__ == "__main__":
    unittest.main()
