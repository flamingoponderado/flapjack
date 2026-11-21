"""Fail-closed coverage of the approved total-function inhabitant qualifier."""
import contextlib
import hashlib
import io
import json
import runpy
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

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

    def test_choice_and_set_to_list_are_reviewed_renderings(self):
        rest = ("noncomputable def holRest {α : Type} [Nonempty α] (s : Set α) : Set α := "
                "s \\ {holChoice s}")
        self.assertEqual(self.errors(rest, rest, ("α",)), [])
        mem = ("theorem mem {α : Type} [Nonempty α] : ∀ s : Set α, s.Finite → "
               "∀ x, x ∈ holSetToList s ↔ x ∈ s := mem_holSetToList")
        self.assertEqual(self.errors(mem, mem, ("α",)), [])
        unlisted = ("theorem r {α : Type} [Nonempty α] (s : Set α) : holRest s ⊆ s := sub")
        self.assertTrue(self.errors(unlisted, unlisted, ("α",)))

    def test_unqualified_instances_are_rejected(self):
        check = REFS["unqualified_inhabitants_errors"]
        self.assertTrue(check("theorem t {α : Type} [Nonempty α] : True := by trivial", False))
        self.assertTrue(check("theorem t {α : Type} [Inhabited α] : True := by trivial", False))
        self.assertFalse(check("theorem t {α : Type} [Nonempty α] : True := by trivial", True))
        self.assertFalse(check("theorem t {α : Type} : True := by trivial", False))

    def test_map_existential_qualifier_does_not_cover_inhabitance(self):
        main = REFS["main"]
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "cakeml/pancake").mkdir(parents=True)
            (root / "cakeml/pancake/fixtureScript.sml").write_text("Theorem th: T Proof simp[] QED\n")
            lean = root / "Fixture.lean"
            lean.write_text('@[hol "cakeml/pancake/fixtureScript.sml" "th" '
                            '(fmap_as_finite_support_existentials := [out])]\n'
                            'theorem t {α : Type} [Nonempty α] : True := by trivial\n')
            out = io.StringIO()
            with patch.dict(main.__globals__, {"ROOT": root, "lean_files": lambda: [lean],
                    "reachable_modules": lambda: {"Fixture"}, "reals_rendering_names": lambda _: set()}), \
                    contextlib.redirect_stderr(out), contextlib.redirect_stdout(out):
                self.assertEqual(main([]), 1)
            self.assertIn("Nonempty/Inhabited instance requires", out.getvalue())

    def test_legacy_baseline_pins_instance_and_complete_signature(self):
        check = REFS["matches_inhabitance_baseline"]
        signature = "theorem t {α : Type} [Nonempty α] : True :="
        entry = {"instances": ["α"], "signature_sha256": hashlib.sha256(signature.encode()).hexdigest()}
        self.assertTrue(check(signature, entry))
        self.assertFalse(check(signature.replace("True", "False"), entry))
        self.assertFalse(check(signature.replace("[Nonempty α]", "[Nonempty α] [Nonempty β]"), entry))
        self.assertFalse(check(signature, {**entry, "instances": ["β"]}))

    def test_baseline_rejects_changed_and_stale_entries(self):
        main = REFS["main"]
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "cakeml/pancake").mkdir(parents=True)
            (root / "cakeml/pancake/fixtureScript.sml").write_text("Theorem th: T Proof simp[] QED\n")
            (root / "scripts").mkdir()
            lean = root / "Fixture.lean"
            tag = '@[hol "cakeml/pancake/fixtureScript.sml" "th"]\n'
            signature = "theorem t {α : Type} [Nonempty α] : True :="
            lean.write_text(tag + signature + " by trivial\n")
            header = REFS["tagged_declaration_text"](lean.read_text().splitlines(), 1)
            entry = {"path": "Fixture.lean", "declaration": "t",
                     "hol_path": "cakeml/pancake/fixtureScript.sml", "hol_name": "th",
                     "instances": ["α"], "signature_sha256": hashlib.sha256(header.encode()).hexdigest()}
            (root / "scripts/hol-unqualified-inhabitants-baseline.json").write_text(json.dumps({"entries": [entry]}))

            def run():
                out = io.StringIO()
                with patch.dict(main.__globals__, {"ROOT": root, "lean_files": lambda: [lean],
                        "reachable_modules": lambda: {"Fixture"}, "reals_rendering_names": lambda _: set()}), \
                        contextlib.redirect_stderr(out), contextlib.redirect_stdout(out):
                    rc = main([])
                return rc, out.getvalue()

            rc, out = run()
            self.assertEqual(rc, 0, out)
            lean.write_text(tag + signature.replace("True", "False") + " by trivial\n")
            rc, out = run()
            self.assertEqual(rc, 1)
            self.assertIn("stale or changed unqualified inhabitance baseline", out)
            self.assertIn("Nonempty/Inhabited instance requires", out)
            lean.write_text(tag + "theorem t : True := by trivial\n")
            rc, out = run()
            self.assertEqual(rc, 1)
            self.assertIn("stale or changed unqualified inhabitance baseline", out)

    def test_proof_only_rendering_baseline_is_pinned_and_stale_checked(self):
        main = REFS["main"]
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "cakeml/pancake").mkdir(parents=True)
            (root / "cakeml/pancake/fixtureScript.sml").write_text("Theorem th: T Proof simp[] QED\n")
            (root / "scripts").mkdir()
            lean = root / "Fixture.lean"
            tag = '@[hol "cakeml/pancake/fixtureScript.sml" "th" (total_function_inhabitants := [α])]\n'
            signature = "theorem t {α : Type} [Nonempty α] : True :="
            lean.write_text(tag + signature + " by have x := holThe; trivial\n")
            header = REFS["tagged_declaration_text"](lean.read_text().splitlines(), 1)
            entry = {"path": "Fixture.lean", "declaration": "t",
                     "hol_path": "cakeml/pancake/fixtureScript.sml", "hol_name": "th",
                     "instances": ["α"], "signature_sha256": hashlib.sha256(header.encode()).hexdigest()}
            (root / "scripts/hol-unqualified-inhabitants-baseline.json").write_text(
                json.dumps({"proof_only_renderings_pending_classification": [entry]}))

            def run():
                out = io.StringIO()
                with patch.dict(main.__globals__, {"ROOT": root, "lean_files": lambda: [lean],
                        "reachable_modules": lambda: {"Fixture"}, "reals_rendering_names": lambda _: set()}), \
                        contextlib.redirect_stderr(out), contextlib.redirect_stdout(out):
                    rc = main([])
                return rc, out.getvalue()

            rc, out = run()
            self.assertEqual(rc, 0, out)
            lean.write_text(tag + signature.replace("True", "False") + " by have x := holThe; trivial\n")
            rc, out = run()
            self.assertEqual(rc, 1)
            self.assertIn("stale or changed proof-only rendering baseline", out)

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

    def test_transitive_rendering_is_restricted_to_the_reviewed_sites(self):
        route = REFS["join_env_locals_transitive_rendering"]
        path = "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml"
        lean = "Flapjack/Compiler/Backend/DataToWord/Proofs/Gc/JoinEnvLocals.lean"
        cases = [("join_env_locals_def", "joinEnvLocals", "joinEnv"),
                 ("join_env_locals_insert_odd", "joinEnvLocals_insertOdd", "joinEnvLocals"),
                 ("join_env_locals_insert_dest_odd", "joinEnvLocals_insertDestOdd", "joinEnvLocals")]
        for hol_name, lean_name, expected in cases:
            self.assertEqual(route(path, hol_name, lean, lean_name, ("α",)), expected)
            self.assertIsNone(route(path, hol_name, lean, lean_name, ("β",)))
            self.assertIsNone(route(path, hol_name, lean, "other", ("α",)))
            self.assertIsNone(route(path, hol_name, "Flapjack/Other.lean", lean_name, ("α",)))
            self.assertIsNone(route("cakeml/other.sml", hol_name, lean, lean_name, ("α",)))

    def test_direct_join_env_exception_is_exact(self):
        route = REFS["join_env_locals_transitive_rendering"]
        source = "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml"
        root = "Flapjack/Compiler/Backend/DataToWord/Proofs/Gc/"
        for hol, file, name, binder in [
            ("join_env_NIL", "StackRel.lean", "joinEnv_nil", "α"),
            ("join_env_EQ_ZIP", "JoinZip.lean", "joinEnv_eq_zip", "β"),
            ("LENGTH_MAP_SND_join_env_IMP", "JoinZip.lean", "length_filter_snd_joinEnv_imp", "β")]:
            self.assertEqual(route(source, hol, root + file, name, (binder,)), "joinEnv")
            self.assertIsNone(route(source, hol, root + file, name, ("wrong",)))
            self.assertIsNone(route(source, hol, root + file, name + "Other", (binder,)))

    def test_theorem_proof_mentions_do_not_justify_a_qualifier(self):
        check = REFS["total_function_inhabitants_errors"]
        signature = "theorem t {α : Type} [Nonempty α] : True :="
        self.assertTrue(check(signature, signature + " by have x := holThe; trivial", ("α",)))
        direct = signature.replace("True", "joinEnv s [] = []")
        self.assertFalse(check(direct, direct + " by trivial", ("α",), "joinEnv"))

    def test_transitive_rendering_still_requires_the_named_call(self):
        signature = "def joined {α β : Type} [Nonempty α] (x : α) : α := x"
        check = REFS["total_function_inhabitants_errors"]
        self.assertTrue(check(signature, signature, ("α",), "joinEnv"))
        self.assertFalse(check(signature, signature + " joinEnv", ("α",), "joinEnv"))
        self.assertTrue(check(signature, signature + " -- joinEnv", ("α",), "joinEnv"))


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
            False, (), (), (), (), (), (), (), (), (), inhabitants,
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
