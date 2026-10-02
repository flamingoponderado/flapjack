"""Regression tests for HOL theorem-map coverage and metadata validation."""

import copy
import runpy
import json
import unittest
from pathlib import Path


MAP = runpy.run_path(
    str(Path(__file__).resolve().parents[1] / "check_hol_theorem_map.py")
)


def _memoize_repository_scan(scan):
    """Scan the checked-out repository once; every caller gets its own copy.

    The tests only read these scans, and the repository does not change while
    they run, so repeating a whole-tree scan per test adds no checking.
    Calls with explicit arguments (for example a temporary root) still scan.
    """
    cache = []

    def cached(*args, **kwargs):
        if args or kwargs:
            return scan(*args, **kwargs)
        if not cache:
            cache.append(scan())
        return copy.deepcopy(cache[0])

    return cached


for _scan in ("build_inventory", "tagged_declarations", "data_declarations",
              "proof_theorem_declarations"):
    MAP[_scan] = _memoize_repository_scan(MAP[_scan])
MANIFEST = runpy.run_path(
    str(Path(__file__).resolve().parents[1] / "hol_theorem_map.py")
)


class ProofDeclarationScanTest(unittest.TestCase):
    def test_comments_and_check_commands_are_not_theorems(self):
        source = """
/-
theorem fakeInBlock : True := by trivial
/- theorem fakeNested : True := by trivial -/
-/
-- theorem fakeLine : True := by trivial
#check notAProofDeclaration
protected theorem actualProof : True := by trivial
"""
        stripped = MAP["strip_comments"](source)
        names = {
            match.group(1)
            for line in stripped.splitlines()
            if (match := MAP["THEOREM_RE"].match(line))
        }
        self.assertEqual(names, {"actualProof"})


class CoordinatorPendingReviewNoteTest(unittest.TestCase):
    def test_rejects_intervening_and_reversed_pending_notes(self):
        notes = [
            "Coordinator source acceptance pending.",
            "Fleet merge acceptance remains tracked separately on the existing beads.",
            "merge acceptance separate",
            "acceptance separate",
            "pending coordinator acceptance",
            "integration acceptance pending",
            "external PR review pending",
            "Coordinator source review is required.",
            "integration review required",
            "coordinator is pending",
            "source review pending coordinator.",
            "acceptance pending coordinator.",
        ]
        for note in notes:
            with self.subTest(note=note):
                self.assertIsNotNone(MAP["reviewed_note_pending_error"](
                    ("Flapjack/Example.lean", "newPort"), "reviewed_exact", note,
                ))

    def test_does_not_confuse_pending_ci_with_pending_source_acceptance(self):
        self.assertIsNone(MAP["reviewed_note_pending_error"](
            ("Flapjack/Example.lean", "newPort"), "reviewed_exact",
            "Coordinator source acceptance complete. CI pending.",
        ))

    def test_rejects_new_reviewed_rows_with_pending_coordinator_note(self):
        error = MAP["reviewed_note_pending_error"](
            ("Flapjack/Example.lean", "newPort"),
            "reviewed_exact",
            "source comparison complete; coordinator review pending",
        )
        self.assertIsNotNone(error)
        self.assertIn("reviewed statement status cannot retain", error)

    def test_allows_only_the_explicit_legacy_bead_allowlist(self):
        key = next(iter(MAP["PENDING_REVIEW_NOTE_ALLOWLIST"]))
        self.assertIsNone(
            MAP["reviewed_note_pending_error"](
                key, "reviewed_exact", "source comparison; Coordinator review required"
            )
        )

    def test_pending_statement_review_is_not_a_reviewed_status(self):
        self.assertIsNone(
            MAP["reviewed_note_pending_error"](
                ("Flapjack/Example.lean", "unreviewed"),
                "pending_statement_review",
                "coordinator review pending",
            )
        )


class HeterogeneousFmapQualifierInventoryTest(unittest.TestCase):
    def test_combined_heterogeneous_words_status_is_accepted_only_with_both_tags(self):
        record = {
            "hol_path": "cakeml/pancake/semantics/panSemScript.sml",
            "hol_name": "lookup_code_def",
            "lean_path": "Flapjack/Example.lean",
            "lean_name": "lookupCodeCanonicalHOL",
            "statement_status": "reviewed_fmap_as_finite_support_heterogeneous_function_words_as_type_indexed_bitvec",
            "reviewer": "source comparison of heterogeneous finite-map argument_1/result_2 and word carriers",
            "fmap_as_finite_support_heterogeneous_function": ["argument_1", "result_2"],
            "words_as_type_indexed_bitvec": True,
        }
        key = (record["lean_path"], record["lean_name"])
        def tagged(words=True, positions=("argument_1", "result_2")):
            return {key: (record["hol_path"], record["hol_name"], (), (), (), (),
                          False, (), False, words, (), (), None, (), positions)}
        self.assertEqual(MAP["validate_inventory"]([record], set(), tagged(), set()), [])
        for tags in (tagged(words=False), tagged(positions=())):
            self.assertTrue(MAP["validate_inventory"]([record], set(), tags, set()))

    def test_new_status_and_manifest_field_are_registered(self):
        self.assertIn(
            "reviewed_fmap_as_finite_support_heterogeneous_function",
            MAP["VALID_STATUSES"],
        )
        self.assertIn(
            "reviewed_fmap_as_finite_support_heterogeneous_function_words_as_type_indexed_bitvec",
            MAP["VALID_STATUSES"],
        )
        self.assertIn(
            "fmap_as_finite_support_heterogeneous_function",
            MANIFEST["OPTIONAL_FIELDS"],
        )


class ReviewedSourceComparisonTest(unittest.TestCase):
    def test_pan_globals_compile_prog_carrier_mismatch_is_documented(self):
        key = ("Flapjack/Pancake/PanGlobals.lean", "compileProgCake")
        inventory = {
            (record["lean_path"], record["lean_name"]): record
            for record in MAP["build_inventory"]()
        }
        record = inventory[key]
        self.assertEqual(
            (record["hol_path"], record["hol_name"]),
            ("cakeml/pancake/pan_globalsScript.sml", "compile_def"),
        )
        self.assertEqual(record["statement_status"], "documented_mismatch")
        self.assertIn("ProgHOL width", record["reviewer"])
        self.assertIn("No byte-range premise", record["reviewer"])
        self.assertTrue(MAP["lean_definition_exists"](MAP["ROOT"], *key))
        self.assertNotIn(key, MAP["tagged_declarations"]())

    def test_pan_globals_transformation_carrier_mismatches_are_documented(self):
        cases = {
            ("Flapjack/Pancake/PanGlobals.lean", "globalRenameProg"): (
                "cakeml/pancake/pan_globalsScript.sml",
                "fperm_def",
            ),
            ("Flapjack/Pancake/PanGlobals.lean", "globalRenameDecls"): (
                "cakeml/pancake/pan_globalsScript.sml",
                "fperm_decs_def",
            ),
            ("Flapjack/Pancake/PanGlobals.lean", "globalResortDecls"): (
                "cakeml/pancake/pan_globalsScript.sml",
                "resort_decls_def",
            ),
            ("Flapjack/Pancake/PanGlobals.lean", "globalNewMainName"): (
                "cakeml/pancake/pan_globalsScript.sml",
                "new_main_name_def",
            ),
            ("Flapjack/Pancake/PanGlobals.lean", "globalDeclShapes"): (
                "cakeml/pancake/pan_globalsScript.sml",
                "dec_shapes_def",
            ),
        }
        inventory = {
            (record["lean_path"], record["lean_name"]): record
            for record in MAP["build_inventory"]()
        }
        tagged = MAP["tagged_declarations"]()
        for key, (hol_path, hol_name) in cases.items():
            with self.subTest(lean_name=key[1]):
                record = inventory[key]
                self.assertEqual(
                    (record["hol_path"], record["hol_name"]),
                    (hol_path, hol_name),
                )
                self.assertEqual(record["statement_status"], "documented_mismatch")
                self.assertIn("flapjack-6nn.3.1", record["reviewer"])
                self.assertTrue(MAP["lean_definition_exists"](MAP["ROOT"], *key))
                self.assertNotIn(key, tagged)

    def test_pan_globals_exception_carrier_mismatches_are_documented(self):
        manifest = json.loads(MAP["DEFAULT_MANIFEST"].read_text())
        manifest_by_key = {
            (record["lean_path"], record["lean_name"]): record
            for record in manifest
        }
        cases = {
            ("Flapjack/Pancake/Proofs/PanGlobals.lean", "exceptions_append"): (
                "cakeml/pancake/proofs/pan_globalsProofScript.sml",
                "exceptions_append",
                "flapjack-dlc.48",
            ),
            (
                "Flapjack/Pancake/Proofs/PanGlobals.lean",
                "exceptions_FILTER_is_function",
            ): (
                "cakeml/pancake/proofs/pan_globalsProofScript.sml",
                "exceptions_FILTER_is_function",
                "flapjack-dlc.47",
            ),
        }
        tagged = MAP["tagged_declarations"]()
        for key, (hol_path, hol_name, bead) in cases.items():
            with self.subTest(lean_name=key[1]):
                record = manifest_by_key[key]
                self.assertEqual(
                    (record["hol_path"], record["hol_name"]),
                    (hol_path, hol_name),
                )
                self.assertEqual(record["statement_status"], "documented_mismatch")
                self.assertIn("Exp α.Const", record["reviewer"])
                self.assertIn(bead, record["reviewer"])
                self.assertNotIn(key, tagged)
        tagged = MAP["tagged_declarations"]()
        manifest = json.loads(MAP["DEFAULT_MANIFEST"].read_text())
        manifest_by_key = {
            (record["lean_path"], record["lean_name"]): record
            for record in manifest
        }
        exact_cases = {
            ("Flapjack/Pancake/PanGlobals.lean", "fpermName"): (
                "cakeml/pancake/pan_globalsScript.sml",
                "fperm_name_def",
            ),
            ("Flapjack/Pancake/Proofs/PanGlobals.lean", "fpermName_cancel"): (
                "cakeml/pancake/proofs/pan_globalsProofScript.sml",
                "fperm_name_cancel",
            ),
            ("Flapjack/Pancake/Proofs/PanGlobals.lean", "fpermName_cong"): (
                "cakeml/pancake/proofs/pan_globalsProofScript.sml",
                "fperm_name_cong",
            ),
        }
        for key, (hol_path, hol_name) in exact_cases.items():
            with self.subTest(lean_name=key[1]):
                record = manifest_by_key[key]
                self.assertEqual(
                    (record["hol_path"], record["hol_name"]),
                    (hol_path, hol_name),
                )
                self.assertEqual(record["statement_status"], "reviewed_exact")
                self.assertIn("polymorphic", record["reviewer"])
                self.assertIn(key, tagged)
        mismatch_cases = {
            ("Flapjack/Pancake/PanGlobals.lean", "globalRenameFunctionName"): (
                "cakeml/pancake/pan_globalsScript.sml",
                "fperm_name_def",
            ),
            ("Flapjack/Pancake/Proofs/PanGlobals.lean", "fperm_name_cancel"): (
                "cakeml/pancake/proofs/pan_globalsProofScript.sml",
                "fperm_name_cancel",
            ),
            ("Flapjack/Pancake/Proofs/PanGlobals.lean", "fperm_name_cong"): (
                "cakeml/pancake/proofs/pan_globalsProofScript.sml",
                "fperm_name_cong",
            ),
        }
        for key, (hol_path, hol_name) in mismatch_cases.items():
            with self.subTest(lean_name=key[1]):
                record = manifest_by_key[key]
                self.assertEqual(
                    (record["hol_path"], record["hol_name"]),
                    (hol_path, hol_name),
                )
                self.assertEqual(record["statement_status"], "documented_mismatch")
                self.assertIn("specialization", record["reviewer"])
                self.assertNotIn(key, tagged)

    def test_pan_globals_fresh_name_exact_ports_and_production_forms(self):
        tagged = MAP["tagged_declarations"]()
        manifest = json.loads(MAP["DEFAULT_MANIFEST"].read_text())
        manifest_by_key = {
            (record["lean_path"], record["lean_name"]): record
            for record in manifest
        }
        exact_cases = {
            ("Flapjack/Pancake/Proofs/PanGlobals.lean", "freshNameHOL_not_mem_hol"): (
                "fresh_name_correct",
                ["name", "names"],
            ),
            (
                "Flapjack/Pancake/Proofs/PanGlobals.lean",
                "freshNameHOL_not_mem_of_subset_hol",
            ): (
                "fresh_name_correct'",
                ["name", "names", "names'"],
            ),
        }
        for key, (hol_name, names_fields) in exact_cases.items():
            with self.subTest(lean_name=key[1]):
                record = manifest_by_key[key]
                self.assertEqual(
                    (record["hol_path"], record["hol_name"]),
                    ("cakeml/pancake/proofs/pan_globalsProofScript.sml", hol_name),
                )
                self.assertEqual(
                    record["statement_status"], "reviewed_names_as_string"
                )
                self.assertEqual(record["names_as_string"], names_fields)
                self.assertEqual(record["names_as_string_boundary"], ["name"])
                self.assertIn("byte-observable", record["reviewer"])
                for identifier in names_fields:
                    classification = (
                        "byte-observable" if identifier == "name"
                        else "equality/map-key-only"
                    )
                    self.assertIn(
                        f"{identifier}: {classification}", record["reviewer"]
                    )
                self.assertIn(key, tagged)
        mismatch_cases = {
            ("Flapjack/Pancake/Proofs/PanGlobals.lean", "fresh_name_correct"): (
                "fresh_name_correct",
            ),
            ("Flapjack/Pancake/Proofs/PanGlobals.lean", "fresh_name_correct'"): (
                "fresh_name_correct'",
            ),
        }
        for key, (hol_name,) in mismatch_cases.items():
            with self.subTest(lean_name=key[1]):
                record = manifest_by_key[key]
                self.assertEqual(
                    (record["hol_path"], record["hol_name"]),
                    ("cakeml/pancake/proofs/pan_globalsProofScript.sml", hol_name),
                )
                self.assertEqual(record["statement_status"], "documented_mismatch")
                self.assertIn("globalFreshName", record["reviewer"])
                self.assertNotIn(key, tagged)

    def test_crep_evaluate_ind_exact_tag(self):
        tagged = MAP["tagged_declarations"]()
        manifest = json.loads(MAP["DEFAULT_MANIFEST"].read_text())
        manifest_by_key = {
            (record["lean_path"], record["lean_name"]): record
            for record in manifest
        }
        key = (
            "Flapjack/Pancake/Semantics/CrepSem/EvaluateInd.lean",
            "evalCrepSemHOLProgExact_induct",
        )
        record = manifest_by_key[key]
        self.assertEqual(
            (record["hol_path"], record["hol_name"]),
            ("cakeml/pancake/semantics/crepSemScript.sml", "evaluate_ind"),
        )
        self.assertEqual(
            record["statement_status"],
            "reviewed_fmap_as_finite_support_words_as_type_indexed_bitvec",
        )
        self.assertEqual(record["fmap_as_finite_support"], ["locals", "globals", "code"])
        self.assertTrue(record["words_as_type_indexed_bitvec"])
        self.assertIn("flapjack-2de.1.1", record["reviewer"])
        self.assertIn(key, tagged)
        self.assertNotIn(key, MAP["DOCUMENTED_MISMATCHES"])

    def test_crep_sem_state_exact_helpers_have_combined_carrier_qualifiers(self):
        tagged = MAP["tagged_declarations"]()
        manifest = json.loads(MAP["DEFAULT_MANIFEST"].read_text())
        manifest_by_key = {
            (record["lean_path"], record["lean_name"]): record
            for record in manifest
        }
        exact_cases = {
            "decClockCrepSemHOL": "dec_clock_def",
            "fixClockCrepSemHOL": "fix_clock_def",
            "fixClockCrepSemHOL_IMP_LESS_EQ": "fix_clock_IMP_LESS_EQ",
            "memLoadCrepSemHOL": "mem_load_def",
        }
        for lean_name, hol_name in exact_cases.items():
            key = ("Flapjack/Pancake/Semantics/CrepSem/HOLState.lean", lean_name)
            with self.subTest(lean_name=lean_name):
                record = manifest_by_key[key]
                self.assertEqual(
                    (record["hol_path"], record["hol_name"]),
                    ("cakeml/pancake/semantics/crepSemScript.sml", hol_name),
                )
                self.assertEqual(
                    record["statement_status"],
                    "reviewed_fmap_as_finite_support_words_as_type_indexed_bitvec")
                self.assertEqual(
                    record["fmap_as_finite_support"], ["locals", "globals", "code"])
                self.assertIs(record["words_as_type_indexed_bitvec"], True)
                self.assertIn(key, tagged)

    def test_crep_sem_holstate_update_helpers_have_combined_carrier_qualifiers(self):
        tagged = MAP["tagged_declarations"]()
        manifest = json.loads(MAP["DEFAULT_MANIFEST"].read_text())
        manifest_by_key = {
            (record["lean_path"], record["lean_name"]): record
            for record in manifest
        }
        exact_cases = {
            "setVar": "set_var_def",
            "setGlobals": "set_globals_def",
            "updLocals": "upd_locals_def",
            "emptyLocals": "empty_locals_def",
        }
        for lean_name, hol_name in exact_cases.items():
            key = ("Flapjack/Pancake/Semantics/CrepSem/HOLState.lean", lean_name)
            with self.subTest(lean_name=lean_name):
                record = manifest_by_key[key]
                self.assertEqual(
                    (record["hol_path"], record["hol_name"]),
                    ("cakeml/pancake/semantics/crepSemScript.sml", hol_name),
                )
                self.assertEqual(
                    record["statement_status"],
                    "reviewed_fmap_as_finite_support_words_as_type_indexed_bitvec")
                self.assertEqual(
                    record["fmap_as_finite_support"], ["locals", "globals", "code"])
                self.assertIs(record["words_as_type_indexed_bitvec"], True)
                self.assertIn(key, tagged)
        # The polymorphic finite-map result is now reviewed and tagged. The
        # executable BEq-based resVarW remains a separate documented mismatch.
        res_var_key = (
            "Flapjack/Pancake/Semantics/CrepSem/HOLState.lean", "resVarEq")
        res_var_record = manifest_by_key[res_var_key]
        self.assertEqual(
            (res_var_record["hol_path"], res_var_record["hol_name"]),
            ("cakeml/pancake/semantics/crepSemScript.sml", "res_var_def"),
        )
        self.assertEqual(
            res_var_record["statement_status"],
            "reviewed_fmap_as_finite_support_result",
        )
        self.assertTrue(res_var_record["fmap_as_finite_support_result"])
        self.assertIn(res_var_key, tagged)

    def test_standalone_map_parameter_qualifiers_preserve_named_binders(self):
        tagged = MAP["tagged_declarations"]()
        manifest = json.loads(MAP["DEFAULT_MANIFEST"].read_text())
        by_key = {(r["lean_path"], r["lean_name"]): r for r in manifest}
        exact_key = ("Flapjack/Pancake/PanToCrep/ExpHdlExact.lean", "expHdlExact")
        props_key = (
            "Flapjack/Pancake/Semantics/PanProps/EvalInvariant.lean",
            "feveryResVarFlookupHOL",
        )
        exact = by_key[exact_key]
        self.assertEqual(
            exact["statement_status"],
            "reviewed_fmap_as_finite_support_parameters_words_as_type_indexed_bitvec",
        )
        self.assertEqual(exact["fmap_as_finite_support_parameters"], ["fm"])
        self.assertIs(exact["words_as_type_indexed_bitvec"], True)
        self.assertEqual(tagged[exact_key][10], ("fm",))
        props = by_key[props_key]
        self.assertEqual(
            props["statement_status"], "reviewed_fmap_as_finite_support_parameters"
        )
        self.assertEqual(props["fmap_as_finite_support_parameters"], ["fm", "fm2"])
        self.assertEqual(tagged[props_key][10], ("fm", "fm2"))

    def test_crep_assigned_vars_nested_seq_carrier_mismatch_is_documented(self):
        key = (
            "Flapjack/Pancake/Semantics/CrepProps.lean",
            "crepAssignedVars_nestedSeq_assign_zipWithW",
        )
        inventory = {
            (record["lean_path"], record["lean_name"]): record
            for record in MAP["build_inventory"]()
        }
        record = inventory[key]
        self.assertEqual(
            (record["hol_path"], record["hol_name"]),
            (
                "cakeml/pancake/semantics/crepPropsScript.sml",
                "nested_seq_assigned_vars_eq",
            ),
        )
        self.assertEqual(record["statement_status"], "documented_mismatch")
        self.assertIn("Call/ExtCall names are String", record["reviewer"])
        self.assertNotIn(key, MAP["tagged_declarations"]())

    def test_crep_res_var_definition_mismatch_is_in_review_inventory(self):
        key = ("Flapjack/Pancake/Semantics/CrepSem.lean", "resVarW")
        inventory = {
            (record["lean_path"], record["lean_name"]): record
            for record in MAP["build_inventory"]()
        }
        record = inventory[key]
        self.assertEqual(
            (record["hol_path"], record["hol_name"]),
            ("cakeml/pancake/semantics/crepSemScript.sml", "res_var_def"),
        )
        self.assertEqual(record["statement_status"], "documented_mismatch")
        self.assertIn("infinite support", record["reviewer"])
        self.assertIn(key, MAP["data_declarations"]())
        self.assertNotIn(key, MAP["tagged_declarations"]())

    def test_pan_struct_convert_value_carrier_mismatch_is_documented(self):
        key = (
            "Flapjack/Pancake/Proofs/PanStructs/CompileCorrect.lean",
            "panStructConvertValue",
        )
        inventory = {
            (record["lean_path"], record["lean_name"]): record
            for record in MAP["build_inventory"]()
        }
        record = inventory[key]
        self.assertEqual(
            (record["hol_path"], record["hol_name"]),
            ("cakeml/pancake/proofs/pan_structsProofScript.sml", "convert_v_def"),
        )
        self.assertEqual(record["statement_status"], "documented_mismatch")
        self.assertIn("word_lab wrapper", record["reviewer"])
        self.assertIn("flapjack-pxn.18.3.5.8.19", record["reviewer"])
        self.assertTrue(MAP["lean_definition_exists"](MAP["ROOT"], *key))
        self.assertNotIn(key, MAP["tagged_declarations"]())

    def test_pan_simp_functions_eq_filter_map_arb_mismatch_is_documented(self):
        key = ("Flapjack/Pancake/PanSimp.lean", "functions_eq_filterMap")
        inventory = {
            (record["lean_path"], record["lean_name"]): record
            for record in MAP["build_inventory"]()
        }
        record = inventory[key]
        self.assertEqual(
            (record["hol_path"], record["hol_name"]),
            ("cakeml/pancake/semantics/panPropsScript.sml", "functions_eq_FILTER"),
        )
        self.assertEqual(record["statement_status"], "documented_mismatch")
        self.assertIn("ARB", record["reviewer"])
        self.assertIn("flapjack-4ac.4.109", record["reviewer"])
        self.assertTrue(MAP["lean_definition_exists"](MAP["ROOT"], *key))
        self.assertNotIn(key, MAP["tagged_declarations"]())

    def test_pan_observational_semantics_hook_mismatch_is_documented(self):
        key = ("Flapjack/PanObservationalSemantics.lean", "panSemantics")
        inventory = {
            (record["lean_path"], record["lean_name"]): record
            for record in MAP["build_inventory"]()
        }
        record = inventory[key]
        self.assertEqual(
            (record["hol_path"], record["hol_name"]),
            ("cakeml/pancake/semantics/panSemScript.sml", "semantics_def"),
        )
        self.assertEqual(record["statement_status"], "documented_mismatch")
        self.assertIn("PanSemanticsHooks", record["reviewer"])
        self.assertIn("flapjack-pxn.18.4.4", record["reviewer"])
        self.assertTrue(MAP["lean_definition_exists"](MAP["ROOT"], *key))
        self.assertNotIn(key, MAP["tagged_declarations"]())

    def test_pansem_evaluate_clock_carrier_mismatch_is_documented(self):
        key = (
            "Flapjack/Pancake/Semantics/PanSem/EvaluateClock.lean",
            "evalPanSemRecursiveCallFiniteContext_clock_le",
        )
        inventory = {
            (record["lean_path"], record["lean_name"]): record
            for record in MAP["build_inventory"]()
        }
        record = inventory[key]
        self.assertEqual(
            (record["hol_path"], record["hol_name"]),
            ("cakeml/pancake/semantics/panSemScript.sml", "evaluate_clock"),
        )
        self.assertEqual(record["statement_status"], "documented_mismatch")
        self.assertIn("FiniteEvalContext", record["reviewer"])
        self.assertIn("flapjack-qj5", record["reviewer"])
        self.assertTrue(MAP["lean_definition_exists"](MAP["ROOT"], *key))
        self.assertNotIn(key, MAP["tagged_declarations"]())

    def test_pan_props_res_var_flookup_mismatches_are_documented(self):
        inventory = {
            (record["lean_path"], record["lean_name"]): record
            for record in MAP["build_inventory"]()
        }
        cases = {
            "resVarHOLExact_flookup_some_eq_lookup": "flookup_res_var_some_eq_lookup",
            "resVarHOLExact_flookup_of_ne": "flookup_res_var_diff_eq_org",
            "resVarHOLExact_flookup": "FLOOKUP_pan_res_var_thm",
        }
        for lean_name, hol_name in cases.items():
            key = ("Flapjack/Pancake/Semantics/PanProps.lean", lean_name)
            record = inventory[key]
            self.assertEqual(
                (record["hol_path"], record["hol_name"]),
                ("cakeml/pancake/semantics/panPropsScript.sml", hol_name),
            )
            self.assertEqual(record["statement_status"], "documented_mismatch")
            self.assertIn("finite-map", record["reviewer"])
            self.assertIn("flapjack-pxn.18.3.7.1.3.1.1.2.4", record["reviewer"])
            self.assertTrue(MAP["lean_definition_exists"](MAP["ROOT"], *key))
            self.assertNotIn(key, MAP["tagged_declarations"]())

    def test_pan_lang_with_shape_mismatches_are_documented(self):
        inventory = {
            (record["lean_path"], record["lean_name"]): record
            for record in MAP["build_inventory"]()
        }
        cases = {
            "length_withShape_eq_shape": "length_with_shape_eq_shape",
            "all_distinct_withShape": "all_distinct_with_shape",
            "mem_of_withShape_mem": "el_mem_with_shape",
            "mem_withShape_length": "mem_with_shape_length",
            "withShape_getElem_eq_take_drop": "with_shape_el_take_drop_eq",
        }
        for lean_name, hol_name in cases.items():
            key = ("Flapjack/Pancake/PanLang.lean", lean_name)
            record = inventory[key]
            self.assertEqual(
                (record["hol_path"], record["hol_name"]),
                ("cakeml/pancake/semantics/panPropsScript.sml", hol_name),
            )
            self.assertEqual(record["statement_status"], "documented_mismatch")
            self.assertIn("Shape", record["reviewer"])
            self.assertIn("flapjack-pxn.18.3.5.8", record["reviewer"])
            self.assertTrue(MAP["lean_definition_exists"](MAP["ROOT"], *key))
            self.assertNotIn(key, MAP["tagged_declarations"]())

    def test_pan_props_flatten_and_disjoint_mismatches_are_documented(self):
        inventory = {
            (record["lean_path"], record["lean_name"]): record
            for record in MAP["build_inventory"]()
        }
        cases = {
            ("Flapjack/Pancake/PanLang.lean", "listDisjoint_withShape_getElem"):
                "all_distinct_with_shape_distinct",
            ("Flapjack/Pancake/PanLang.lean", "listDisjoint_withShape_getElem_lt"):
                "all_distinct_disjoint_with_shape",
            ("Flapjack/Pancake/PanLang.lean", "listDisjoint_of_mem_zip_withShape"):
                "all_distinct_mem_zip_disjoint_with_shape",
            ("Flapjack/Pancake/PanLang.lean", "withShape_getElem_getElem"):
                "el_el_with_shape",
            ("Flapjack/PanValueFlatten.lean",
             "shapeSize_comb_eq_flatten_length_of_getElem"):
                "list_rel_length_shape_of_flatten_better",
            ("Flapjack/PanValueFlatten.lean",
             "shapeSize_comb_map_panValueShape_eq_flatten_length"):
                "list_rel_length_shape_of_flatten",
            ("Flapjack/Pancake/Semantics/PanProps.lean",
             "listRelFlattenWithShapeLength"):
                "list_rel_flatten_with_shape_length",
            ("Flapjack/Pancake/Semantics/PanProps.lean",
             "listRelFlattenWithShapeFlookup"):
                "list_rel_flatten_with_shape_flookup",
        }
        for key, hol_name in cases.items():
            record = inventory[key]
            self.assertEqual(
                (record["hol_path"], record["hol_name"]),
                ("cakeml/pancake/semantics/panPropsScript.sml", hol_name),
            )
            self.assertEqual(record["statement_status"], "documented_mismatch")
            self.assertIn("flapjack-pxn.18.3.5.8", record["reviewer"])
            self.assertTrue(MAP["lean_definition_exists"](MAP["ROOT"], *key))
            self.assertNotIn(key, MAP["tagged_declarations"]())

    def test_pansem_state_defs_function_backed_mismatches_are_documented(self):
        inventory = {
            (record["lean_path"], record["lean_name"]): record
            for record in MAP["build_inventory"]()
        }
        cases = {
            ("Flapjack/Pancake/Semantics/PanSem/ClockExact.lean",
             "fixClockHOLExact_IMP_LESS_EQ"): "fix_clock_IMP_LESS_EQ",
            ("Flapjack/Pancake/Semantics/PanSem/StateSimpExact.lean",
             "kvar_simps"): "kvar_simps",
            ("Flapjack/Pancake/Semantics/PanSem/StateSimpExact.lean",
             "is_valid_value_simps"): "is_valid_value_simps",
            ("Flapjack/Pancake/Semantics/PanSem/StateSimpExact.lean",
             "is_valid_value_simps2"): "is_valid_value_simps2",
            ("Flapjack/Pancake/Semantics/PanSem/StateDefsExact.lean",
             "kvar_defs"): "kvar_defs",
            ("Flapjack/Pancake/Semantics/PanSem/IsValidValueExact.lean",
             "isValidValueHOLExact"): "is_valid_value_def",
            ("Flapjack/Pancake/Semantics/PanSem/LocalUpdatesExact.lean",
             "updLocalsHOLExact"): "upd_locals_def",
            ("Flapjack/Pancake/Semantics/PanSem/LocalUpdatesExact.lean",
             "resVarHOLExact"): "res_var_def",
            ("Flapjack/Pancake/Semantics/PanSem/DecCallExact.lean",
             "lookupCodeHOLExact"): "lookup_code_def",
        }
        for key, hol_name in cases.items():
            record = inventory[key]
            self.assertEqual(
                (record["hol_path"], record["hol_name"]),
                ("cakeml/pancake/semantics/panSemScript.sml", hol_name),
            )
            self.assertEqual(record["statement_status"], "documented_mismatch")
            self.assertIn("flapjack-pxn.18.3.7.1.3.1.1.2.5", record["reviewer"])
            self.assertTrue(MAP["lean_definition_exists"](MAP["ROOT"], *key))
            self.assertNotIn(key, MAP["tagged_declarations"]())

    def test_pansem_mem_alt_ports_and_shmem_mismatches_are_classified(self):
        inventory = {
            (record["lean_path"], record["lean_name"]): record
            for record in MAP["build_inventory"]()
        }
        cases = {
            ("Flapjack/Pancake/Semantics/PanSem/MemLoad32Alt.lean",
             "panMemLoad32HOL_eq_alt"):
                ("mem_load_32_alt", "flapjack-pxn.18.3.6.9.27", "reviewed_exact"),
            ("Flapjack/Pancake/Semantics/PanSem/MemStore32Alt.lean",
             "panMemStore32HOL_eq_alt"):
                ("mem_store_32_alt", "flapjack-pxn.18.3.6.9.29", "reviewed_exact"),
            ("Flapjack/Pancake/Semantics/PanSem/ShMemExact.lean",
             "shMemLoadHOLExact"):
                ("sh_mem_load_def", "flapjack-pxn.18.3.7.1.3.1.1.2.5", "documented_mismatch"),
            ("Flapjack/Pancake/Semantics/PanSem/ShMemExact.lean",
             "shMemStoreHOLExact"):
                ("sh_mem_store_def", "flapjack-pxn.18.3.7.1.3.1.1.2.5", "documented_mismatch"),
        }
        for key, (hol_name, dep, status) in cases.items():
            record = inventory[key]
            self.assertEqual(
                (record["hol_path"], record["hol_name"]),
                ("cakeml/pancake/semantics/panSemScript.sml", hol_name),
            )
            self.assertEqual(record["statement_status"], status)
            self.assertTrue(MAP["lean_definition_exists"](MAP["ROOT"], *key))
            if status == "reviewed_exact":
                self.assertIn(key, MAP["tagged_declarations"]())
            else:
                self.assertIn(dep, record["reviewer"])
                self.assertNotIn(key, MAP["tagged_declarations"]())

    def test_global_rename_function_name_polymorphic_hol_mismatch_is_documented(
        self,
    ):
        key = ("Flapjack/Pancake/PanGlobals.lean", "globalRenameFunctionName")
        inventory = {
            (record["lean_path"], record["lean_name"]): record
            for record in MAP["build_inventory"]()
        }
        record = inventory[key]
        self.assertEqual(
            (record["hol_path"], record["hol_name"]),
            ("cakeml/pancake/pan_globalsScript.sml", "fperm_name_def"),
        )
        self.assertEqual(record["statement_status"], "documented_mismatch")
        self.assertNotIn("names_as_string", record)
        self.assertIn("polymorphic", record["reviewer"])
        self.assertIn("flapjack-pxn.18.3.5.8", record["reviewer"])
        self.assertTrue(MAP["lean_definition_exists"](MAP["ROOT"], *key))
        self.assertNotIn(key, MAP["tagged_declarations"]())

    def test_crep_set_globals_state_carrier_mismatch_is_documented(self):
        key = ("Flapjack/Pancake/Semantics/CrepSem.lean", "setCrepHolGlobalsW")
        inventory = {
            (record["lean_path"], record["lean_name"]): record
            for record in MAP["build_inventory"]()
        }
        record = inventory[key]
        self.assertEqual(
            (record["hol_path"], record["hol_name"]),
            ("cakeml/pancake/semantics/crepSemScript.sml", "set_globals_def"),
        )
        self.assertEqual(record["statement_status"], "documented_mismatch")
        self.assertIn("unrestricted Nat-to-Option locals", record["reviewer"])
        self.assertTrue(MAP["lean_definition_exists"](MAP["ROOT"], *key))
        self.assertNotIn(key, MAP["tagged_declarations"]())

    def test_crep_set_var_state_carrier_mismatch_is_documented(self):
        key = ("Flapjack/Pancake/Semantics/CrepSem.lean", "setCrepHolVarW")
        inventory = {
            (record["lean_path"], record["lean_name"]): record
            for record in MAP["build_inventory"]()
        }
        record = inventory[key]
        self.assertEqual(
            (record["hol_path"], record["hol_name"]),
            ("cakeml/pancake/semantics/crepSemScript.sml", "set_var_def"),
        )
        self.assertEqual(record["statement_status"], "documented_mismatch")
        self.assertIn("infinite", record["reviewer"])
        self.assertTrue(MAP["lean_definition_exists"](MAP["ROOT"], *key))
        self.assertNotIn(key, MAP["tagged_declarations"]())

    def test_crep_clock_and_locals_carrier_mismatches_are_documented(self):
        inventory = {
            (record["lean_path"], record["lean_name"]): record
            for record in MAP["build_inventory"]()
        }
        expected = {
            "decCrepHolClockW": "dec_clock_def",
            "emptyCrepHolLocalsW": "empty_locals_def",
            "fixCrepHolClockW": "fix_clock_def",
            "fixCrepHolClock_IMP_LESS_EQW": "fix_clock_IMP_LESS_EQ",
        }
        for lean_name, hol_name in expected.items():
            key = ("Flapjack/Pancake/Semantics/CrepSem.lean", lean_name)
            with self.subTest(key=key):
                record = inventory[key]
                self.assertEqual(
                    (record["hol_path"], record["hol_name"]),
                    ("cakeml/pancake/semantics/crepSemScript.sml", hol_name),
                )
                self.assertEqual(record["statement_status"], "documented_mismatch")
                self.assertIn("infinite", record["reviewer"])
                self.assertTrue(MAP["lean_definition_exists"](MAP["ROOT"], *key))
                self.assertNotIn(key, MAP["tagged_declarations"]())

    def test_crepprops_simp_and_nested_seq_mismatches_are_documented(self):
        inventory = {
            (record["lean_path"], record["lean_name"]): record
            for record in MAP["build_inventory"]()
        }
        expected = {
            "decCrepHolClock_simp": "dec_clock_simp",
            "emptyCrepHolLocals_simp": "empty_locals_simp",
            "crepAssignedFreeVars_nestedSeq_assign_zipWithW": "nested_seq_assigned_free_vars_eq",
        }
        for lean_name, hol_name in expected.items():
            key = ("Flapjack/Pancake/Semantics/CrepProps.lean", lean_name)
            with self.subTest(key=key):
                record = inventory[key]
                self.assertEqual(
                    (record["hol_path"], record["hol_name"]),
                    ("cakeml/pancake/semantics/crepPropsScript.sml", hol_name),
                )
                self.assertEqual(record["statement_status"], "documented_mismatch")
                self.assertIn("withdrawn", record["reviewer"])
                self.assertTrue(MAP["lean_definition_exists"](MAP["ROOT"], *key))
                self.assertNotIn(key, MAP["tagged_declarations"]())

    def test_crepprops_globals_and_assigned_var_mismatches_are_documented(self):
        inventory = {
            (record["lean_path"], record["lean_name"]): record
            for record in MAP["build_inventory"]()
        }
        expected = {
            "flookup_setCrepHolGlobals_localsW": "FLOOKUP_set_globals",
            "crepAssignedFreeVars_nestedSeq_storeGlobalsW":
                "assigned_free_vars_store_globals_empty",
            "crepAssignedVars_nestedSeq_storeGlobalsW":
                "assigned_vars_store_globals_empty",
            "mem_crepAssignedFreeVars_imp_mem_crepAssignedVarsW":
                "assigned_free_vars_IMP_assigned_vars",
        }
        for lean_name, hol_name in expected.items():
            key = ("Flapjack/Pancake/Semantics/CrepProps.lean", lean_name)
            with self.subTest(key=key):
                record = inventory[key]
                self.assertEqual(
                    (record["hol_path"], record["hol_name"]),
                    ("cakeml/pancake/semantics/crepPropsScript.sml", hol_name),
                )
                self.assertEqual(record["statement_status"], "documented_mismatch")
                self.assertIn("String", record["reviewer"])
                self.assertTrue(MAP["lean_definition_exists"](MAP["ROOT"], *key))
                self.assertNotIn(key, MAP["tagged_declarations"]())

    def test_pan_empty_locals_definition_mismatch_is_in_review_inventory(self):
        key = (
            "Flapjack/Pancake/Semantics/PanSem.lean",
            "panEmptyLocals",
        )
        inventory = {
            (record["lean_path"], record["lean_name"]): record
            for record in MAP["build_inventory"]()
        }
        record = inventory[key]
        self.assertEqual(
            (record["hol_path"], record["hol_name"]),
            ("cakeml/pancake/semantics/panSemScript.sml", "empty_locals_def"),
        )
        self.assertEqual(record["statement_status"], "documented_mismatch")
        self.assertIn("finite-map bridge", record["reviewer"])
        self.assertIn(key, MAP["data_declarations"]())
        self.assertNotIn(key, MAP["tagged_declarations"]())

    def test_crep_state_shape_mismatch_is_not_mapped_as_exact(self):
        inventory = {
            (record["lean_path"], record["lean_name"]): record
            for record in MAP["build_inventory"]()
        }
        invalid_exact = (
            ("Flapjack/Pancake/Semantics/CrepProps.lean", "lookup_locals_eq_map_vars"),
            ("Flapjack/Pancake/Semantics/CrepProps.lean", "dec_clock_simp"),
            ("Flapjack/Pancake/Semantics/CrepProps.lean", "empty_locals_simp"),
            ("Flapjack/Pancake/Semantics/CrepSem.lean", "decCrepClock"),
            ("Flapjack/Pancake/Semantics/CrepSem.lean", "clearCrepRuntimeLocals"),
        )
        for key in invalid_exact:
            with self.subTest(key=key):
                self.assertNotIn(key, inventory)

    def test_compile_prog_distinctness_carrier_mismatches_are_documented(self):
        inventory = {
            (record["lean_path"], record["lean_name"]): record
            for record in MAP["build_inventory"]()
        }
        compile_prog = inventory[
            ("Flapjack/Pancake/PanToCrep/CompileProg.lean", "compileProgTopHOL")
        ]
        self.assertEqual(compile_prog["hol_name"], "compile_prog_def")
        self.assertEqual(compile_prog["statement_status"], "documented_mismatch")
        documented_mismatches = (
            "firstCompileProgAllDistinct",
            "firstCompileToCrepAllDistinct",
        )
        for theorem_name in documented_mismatches:
            key = ("Flapjack/Pancake/Proofs/PanToCrep.lean", theorem_name)
            with self.subTest(key=key):
                self.assertIsNone(inventory[key]["hol_name"])
                self.assertEqual(
                    inventory[key]["statement_status"],
                    "no_hol_reference_pending_classification",
                )

        manifest = json.loads(MAP["DEFAULT_MANIFEST"].read_text())
        manifest_by_key = {
            (record["lean_path"], record["lean_name"]): record
            for record in manifest
        }
        for theorem_name in documented_mismatches:
            key = ("Flapjack/Pancake/Proofs/PanToCrep.lean", theorem_name)
            with self.subTest(review_record=key):
                self.assertEqual(
                    manifest_by_key[key]["statement_status"], "documented_mismatch"
                )
                self.assertIn("carrier", manifest_by_key[key]["reviewer"])

    def test_genlist_vmax_distinct_lists_port_is_in_review_inventory(self):
        inventory = {
            (record["lean_path"], record["lean_name"]): record
            for record in MAP["build_inventory"]()
        }
        generic_key = (
            "Flapjack/Pancake/Proofs/PanToCrep/CompileExpVmax.lean",
            "genlistVmaxDistinctListsCompiledExps",
        )
        generic = inventory[generic_key]
        self.assertIsNone(generic["hol_name"])
        self.assertEqual(
            generic["statement_status"],
            "no_hol_reference_pending_classification",
        )

        manifest = json.loads(MAP["DEFAULT_MANIFEST"].read_text())
        manifest_by_key = {
            (record["lean_path"], record["lean_name"]): record
            for record in manifest
        }
        generic_record = manifest_by_key[generic_key]
        self.assertEqual(
            generic_record["hol_name"],
            "genlist_vmax_distinct_lists_compiled_exps",
        )
        self.assertEqual(generic_record["statement_status"], "documented_mismatch")

        exact_key = (
            "Flapjack/Pancake/Proofs/PanToCrep/CompileExpVmax.lean",
            "genlistVmaxDistinctListsCompiledExpsW",
        )
        exact = inventory[exact_key]
        self.assertEqual(
            exact["hol_name"],
            "genlist_vmax_distinct_lists_compiled_exps",
        )
        self.assertEqual(exact["statement_status"], "reviewed_exact")
        self.assertTrue(exact["reviewer"])

    def test_exact_pan_to_crep_utility_ports_are_in_review_inventory(self):
        inventory = {
            (record["lean_path"], record["lean_name"]): record
            for record in MAP["build_inventory"]()
        }
        expected = {
            ("Flapjack/Pancake/Proofs/PanToCrep.lean", "mod_eq_of_lt_eq"),
            ("Flapjack/Pancake/Proofs/PanToCrep.lean", "option_ne_none_iff_exists"),
            ("Flapjack/Pancake/Proofs/PanToCrep.lean", "prod_mk_pair_eq_id"),
        }
        for key in expected:
            with self.subTest(key=key):
                self.assertEqual(inventory[key]["statement_status"], "reviewed_exact")
                self.assertEqual(
                    inventory[key]["reviewer"], "Codex (source comparison)"
                )

    def test_locals_rel_lookup_ctxt_withdrawal_is_recorded(self):
        inventory = {
            (record["lean_path"], record["lean_name"]): record
            for record in MAP["build_inventory"]()
        }
        key = ("Flapjack/Pancake/Proofs/PanToCrep.lean", "localsRelLookupCtxt")
        self.assertIsNone(inventory[key]["hol_name"])
        self.assertEqual(inventory[key]["statement_status"],
                         "no_hol_reference_pending_classification")
        manifest = json.loads(MAP["DEFAULT_MANIFEST"].read_text())
        record = next(record for record in manifest if
                      (record["lean_path"], record["lean_name"]) == key)
        self.assertEqual(record["hol_name"], "locals_rel_lookup_ctxt")
        self.assertEqual(record["statement_status"], "documented_mismatch")

    def test_compile_exp_not_mem_load_glob_withdrawal_is_recorded(self):
        inventory = {
            (record["lean_path"], record["lean_name"]): record
            for record in MAP["build_inventory"]()
        }
        key = ("Flapjack/Pancake/Proofs/PanToCrep.lean", "compileExpNotMemLoadGlob")
        self.assertIsNone(inventory[key]["hol_name"])
        self.assertEqual(inventory[key]["statement_status"],
                         "no_hol_reference_pending_classification")
        manifest = json.loads(MAP["DEFAULT_MANIFEST"].read_text())
        record = next(record for record in manifest if
                      (record["lean_path"], record["lean_name"]) == key)
        self.assertEqual(record["hol_name"], "compile_exp_not_mem_load_glob")
        self.assertEqual(record["statement_status"], "documented_mismatch")

    def test_is_wf_shape_drop_exact_port_and_production_analogue(self):
        inventory = {
            (record["lean_path"], record["lean_name"]): record
            for record in MAP["build_inventory"]()
        }
        exact_key = ("Flapjack/Pancake/Proofs/PanStructs/StructInfosOkExact.lean",
                     "isWfShapeExactHOL_drop")
        production_key = ("Flapjack/Pancake/Proofs/PanStructs.lean", "isWfShape_drop")
        self.assertEqual(inventory[exact_key]["hol_name"], "is_wf_shape_drop")
        self.assertEqual(inventory[exact_key]["statement_status"],
                         "pending_statement_review")
        self.assertEqual(inventory[production_key]["hol_name"], "is_wf_shape_drop")
        self.assertEqual(inventory[production_key]["statement_status"],
                         "documented_mismatch")

        manifest = json.loads(MAP["DEFAULT_MANIFEST"].read_text())
        exact_record = next(record for record in manifest if
                            (record["lean_path"], record["lean_name"]) == exact_key)
        self.assertEqual(exact_record["hol_name"], "is_wf_shape_drop")
        self.assertEqual(exact_record["statement_status"], "reviewed_exact")
        production_record = next(record for record in manifest if
                                 (record["lean_path"], record["lean_name"]) == production_key)
        self.assertIsNone(production_record["hol_name"])
        self.assertEqual(production_record["statement_status"],
                         "no_hol_reference_pending_classification")

    def test_old_exp_shapes_map_analogue_stays_untagged(self):
        inventory = {
            (record["lean_path"], record["lean_name"]): record
            for record in MAP["build_inventory"]()
        }
        key = ("Flapjack/Pancake/Proofs/PanStructs.lean", "structOldExpShapes_eq_map")
        self.assertEqual(inventory[key]["hol_name"], "old_exp_shapes_eq")
        self.assertEqual(inventory[key]["statement_status"], "documented_mismatch")

        manifest = json.loads(MAP["DEFAULT_MANIFEST"].read_text())
        record = next(record for record in manifest if
                      (record["lean_path"], record["lean_name"]) == key)
        self.assertEqual(record["hol_name"], "old_exp_shapes_eq")
        self.assertEqual(record["statement_status"], "documented_mismatch")
        self.assertIn("byte-observable", record["reviewer"])
        self.assertIn("String", record["reviewer"])

    def test_fperm_decs_decls_carrier_mismatch_stays_untagged(self):
        key = ("Flapjack/Pancake/Proofs/PanGlobals.lean", "fperm_decs_decls")
        inventory = {
            (record["lean_path"], record["lean_name"]): record
            for record in MAP["build_inventory"]()
        }
        self.assertEqual(inventory[key]["hol_name"], "fperm_decs_decls")
        self.assertEqual(inventory[key]["statement_status"], "documented_mismatch")
        self.assertNotIn(key, MAP["tagged_declarations"]())

        manifest = json.loads(MAP["DEFAULT_MANIFEST"].read_text())
        record = next(record for record in manifest if
                      (record["lean_path"], record["lean_name"]) == key)
        self.assertEqual(record["hol_name"], "fperm_decs_decls")
        self.assertEqual(record["statement_status"], "documented_mismatch")
        review = MAP["DOCUMENTED_MISMATCHES"][key][2]
        self.assertIn("unused ys binder", review)
        self.assertIn("arbitrary α global values", review)
        self.assertIn("no NameRanged premise", review)
        self.assertIn("arbitrary α global values", record["reviewer"])


    def test_fields_in_order_reorder_analogue_stays_untagged(self):
        inventory = {
            (record["lean_path"], record["lean_name"]): record
            for record in MAP["build_inventory"]()
        }
        key = ("Flapjack/Pancake/Proofs/PanStructs.lean", "fieldsInOrderReorderNoop")
        self.assertEqual(inventory[key]["hol_name"], "fields_in_order_reorder_noop")
        self.assertEqual(inventory[key]["statement_status"], "documented_mismatch")

        manifest = json.loads(MAP["DEFAULT_MANIFEST"].read_text())
        record = next(record for record in manifest if
                      (record["lean_path"], record["lean_name"]) == key)
        self.assertEqual(record["hol_name"], "fields_in_order_reorder_noop")
        self.assertEqual(record["statement_status"], "documented_mismatch")
        self.assertIn("byte-observable", record["reviewer"])
        self.assertIn("No NameRanged premise", record["reviewer"])


class ValidateInventoryTest(unittest.TestCase):
    path = "Flapjack/Pancake/Proofs/Example.lean"

    def record(self, **overrides):
        record = {
            "hol_path": "cakeml/pancake/proofs/exampleProofScript.sml",
            "hol_name": "example_theorem",
            "lean_path": self.path,
            "lean_name": "exampleTheorem",
            "statement_status": "pending_statement_review",
            "reviewer": "Codex (reference inventory)",
        }
        record.update(overrides)
        return record

    def test_complete_mapped_entry_passes(self):
        errors = MAP["validate_inventory"](
            [self.record()],
            {(self.path, "exampleTheorem")},
            {
                (self.path, "exampleTheorem"): (
                    "cakeml/pancake/proofs/exampleProofScript.sml",
                    "example_theorem",
                )
            },
        )
        self.assertEqual(errors, [])

    def test_reviewed_list_as_array_requires_qualified_tag_and_fields(self):
        fields = ("degrees",)
        tagged = {
            (self.path, "exampleTheorem"): (
                "cakeml/pancake/proofs/exampleProofScript.sml",
                "example_theorem",
                fields,
                (),
                (),
            )
        }
        record = self.record(
            statement_status="reviewed_list_as_array", list_as_array=["degrees"]
        )
        self.assertEqual(
            MAP["validate_inventory"](
                [record], {(self.path, "exampleTheorem")}, tagged
            ),
            [],
        )

    def test_qualified_tag_rejects_absent_or_misnamed_witness_field(self):
        tagged = {
            (self.path, "exampleTheorem"): (
                "cakeml/pancake/proofs/exampleProofScript.sml",
                "example_theorem",
                ("degrees",),
                (),
                (),
            )
        }
        exact = self.record(statement_status="reviewed_exact")
        errors = MAP["validate_inventory"](
            [exact], {(self.path, "exampleTheorem")}, tagged
        )
        self.assertTrue(any("use reviewed_list_as_array" in e for e in errors))

        qualified = self.record(
            statement_status="reviewed_list_as_array", list_as_array=["move"]
        )
        errors = MAP["validate_inventory"](
            [qualified], {(self.path, "exampleTheorem")}, tagged
        )
        self.assertTrue(any("fields do not match" in e for e in errors))

    def test_exact_tag_regression_remains_reviewed_exact(self):
        record = self.record(statement_status="reviewed_exact")
        errors = MAP["validate_inventory"](
            [record],
            {(self.path, "exampleTheorem")},
            {
                (self.path, "exampleTheorem"): (
                    "cakeml/pancake/proofs/exampleProofScript.sml",
                    "example_theorem",
                    (),
                    (),
                    (),
                )
            },
        )
        self.assertEqual(errors, [])

    def test_reviewed_names_as_string_requires_matching_tag_and_source_review(self):
        tagged = {
            (self.path, "exampleTheorem"): (
                "cakeml/pancake/proofs/exampleProofScript.sml",
                "example_theorem",
                (),
                ("key",),
                (),
            )
        }
        reviewed = self.record(
            statement_status="reviewed_names_as_string",
            reviewer="Codex (HOL source review: key: equality/map-key-only)",
            names_as_string=["key"],
        )
        self.assertEqual(
            MAP["validate_inventory"](
                [reviewed], {(self.path, "exampleTheorem")}, tagged
            ),
            [],
        )

        exact = self.record(
            statement_status="reviewed_exact", names_as_string=["key"]
        )
        errors = MAP["validate_inventory"](
            [exact], {(self.path, "exampleTheorem")}, tagged
        )
        self.assertTrue(any("use reviewed_names_as_string" in e for e in errors))

        pending = self.record(
            statement_status="pending_statement_review",
            names_as_string=["key"],
        )
        errors = MAP["validate_inventory"](
            [pending], {(self.path, "exampleTheorem")}, tagged
        )
        self.assertTrue(any("needs a reviewed source classification" in e for e in errors))

        generic_review = {**reviewed, "reviewer": "Codex (reference inventory)"}
        errors = MAP["validate_inventory"](
            [generic_review], {(self.path, "exampleTheorem")}, tagged
        )
        self.assertTrue(any("source-review note" in e for e in errors))

        unclassified = {**reviewed, "reviewer": "Codex (HOL source review: key use reviewed)"}
        errors = MAP["validate_inventory"](
            [unclassified], {(self.path, "exampleTheorem")}, tagged
        )
        self.assertTrue(any("must classify key as equality/map-key-only" in e for e in errors))

        wrong_field = {**reviewed, "names_as_string": ["other"]}
        errors = MAP["validate_inventory"](
            [wrong_field], {(self.path, "exampleTheorem")}, tagged
        )
        self.assertTrue(any("names_as_string fields do not match" in e for e in errors))

    def test_boundary_qualifier_must_be_reviewed_subset_and_match_manifest(self):
        tagged = {
            (self.path, "exampleTheorem"): (
                "cakeml/pancake/proofs/exampleProofScript.sml",
                "example_theorem",
                (),
                ("key", "generated"),
                ("generated",),
            )
        }
        record = self.record(
            statement_status="reviewed_names_as_string",
            reviewer=("Codex (HOL source review: key: equality/map-key-only; "
                      "generated: byte-observable)"),
            names_as_string=["key", "generated"],
            names_as_string_boundary=["key"],
        )
        errors = MAP["validate_inventory"](
            [record], {(self.path, "exampleTheorem")}, tagged
        )
        self.assertTrue(any("names_as_string_boundary fields do not match" in e
                            for e in errors))

        reviewed_boundary = {
            **record,
            "names_as_string_boundary": ["generated"],
            "reviewer": ("Codex (HOL source review: key: equality/map-key-only; "
                         "generated: byte-observable)"),
        }
        self.assertEqual(
            MAP["validate_inventory"](
                [reviewed_boundary], {(self.path, "exampleTheorem")}, tagged
            ),
            [],
        )

    def test_missing_proofs_declaration_fails(self):
        errors = MAP["validate_inventory"](
            [], {(self.path, "exampleTheorem")}, {}
        )
        self.assertTrue(any("Proofs theorem missing" in error for error in errors))

    def test_tag_mismatch_fails(self):
        errors = MAP["validate_inventory"](
            [self.record(hol_name="wrong_name")],
            {(self.path, "exampleTheorem")},
            {
                (self.path, "exampleTheorem"): (
                    "cakeml/pancake/proofs/exampleProofScript.sml",
                    "example_theorem",
                )
            },
        )
        self.assertTrue(any("does not match its @[hol] tag" in error for error in errors))

    def test_missing_reviewer_fails(self):
        errors = MAP["validate_inventory"](
            [self.record(reviewer="")],
            {(self.path, "exampleTheorem")},
            {
                (self.path, "exampleTheorem"): (
                    "cakeml/pancake/proofs/exampleProofScript.sml",
                    "example_theorem",
                )
            },
        )
        self.assertTrue(any("reviewer metadata is required" in error for error in errors))

    def test_shape_adjusted_status_is_not_a_reviewed_hol_port(self):
        errors = MAP["validate_inventory"](
            [self.record(statement_status="reviewed_adjusted")],
            {(self.path, "exampleTheorem")},
            {
                (self.path, "exampleTheorem"): (
                    "cakeml/pancake/proofs/exampleProofScript.sml",
                    "example_theorem",
                )
            },
        )
        self.assertTrue(any("invalid statement_status" in error for error in errors))

    def test_unmapped_helper_is_explicitly_recorded(self):
        record = self.record(
            hol_path=None,
            hol_name=None,
            lean_name="localHelper",
            statement_status="no_hol_reference_pending_classification",
        )
        errors = MAP["validate_inventory"](
            [record], {(self.path, "localHelper")}, {}
        )
        self.assertEqual(errors, [])

    def test_documented_mismatch_keeps_source_candidate_untagged(self):
        reference = (
            "cakeml/pancake/proofs/pan_to_crepProofScript.sml",
            "opt_mmap_eval_is_wf_shape_v",
        )
        record = self.record(
            hol_path=reference[0],
            hol_name=reference[1],
            lean_name="evalPanValueExpsWfShapeOfStateRel",
            statement_status="documented_mismatch",
            reviewer="Codex (source comparison)",
        )
        key = (self.path, record["lean_name"])
        self.assertEqual(MAP["validate_inventory"]([record], {key}, {}), [])
        errors = MAP["validate_inventory"]([record], {key}, {key: reference})
        self.assertTrue(any("must not carry an @[hol] tag" in error for error in errors))

    def test_res_var_hol_equality_forms_are_documented_mismatch(self):
        manifest = json.loads(MAP["DEFAULT_MANIFEST"].read_text())
        by_key = {
            (record["lean_path"], record["lean_name"]): record for record in manifest
        }
        hol_forms = {
            ("Flapjack/Pancake/Proofs/CrepInline.lean",
             "foldl_res_var_zip_lookup_var_hol"): "FOLDL_res_var_ZIP_lookup_var",
            ("Flapjack/Pancake/Proofs/CrepInline.lean",
             "foldl_res_var_zip_lookup_hol"): "FOLDL_res_var_ZIP_lookup",
            ("Flapjack/Pancake/Proofs/CrepInline.lean",
             "submap_imp_fupdate_submap_hol"): "SUBMAP_IMP_FUPDATE_SUBMAP",
            ("Flapjack/Pancake/Proofs/CrepInline.lean",
             "submap_imp_domsub_submap_hol"): "SUBMAP_IMP_DOMSUB_SUBMAP",
            ("Flapjack/Pancake/Proofs/CrepInline.lean",
             "submap_imp_domsub_fupdate_hol"): "SUBMAP_IMP_DOMSUB_FUPDATE",
            ("Flapjack/Pancake/Proofs/CrepInline.lean",
             "res_var_commutes_strong_hol"): "res_var_commutes_strong",
            ("Flapjack/Pancake/Proofs/CrepInline.lean",
             "res_var_foldl_commutes_strong_hol"): "res_var_foldl_commutes_strong",
            ("Flapjack/Pancake/Proofs/CrepInline.lean",
             "flookup_res_var_is_mem_zip_eq_hol"): "flookup_res_var_is_mem_zip_eq",
            ("Flapjack/Pancake/Semantics/CrepProps.lean",
             "flookup_res_var_distinct_zip_eq_hol"): "flookup_res_var_distinct_zip_eq",
        }
        for key, hol_name in hol_forms.items():
            with self.subTest(key=key):
                record = by_key[key]
                self.assertEqual(record["hol_name"], hol_name)
                self.assertEqual(record["statement_status"], "documented_mismatch")
                self.assertIn("infinite-support", record["reviewer"])
                self.assertIn("flapjack-pxn.18.3.7.1.3.1.1.3.1",
                              record["reviewer"])
                self.assertNotIn(key, MAP["tagged_declarations"]())

        production = {
            ("Flapjack/Pancake/Proofs/CrepInline.lean",
             "FOLDL_res_var_ZIP_lookup_var"),
            ("Flapjack/Pancake/Proofs/CrepInline.lean",
             "FOLDL_res_var_ZIP_lookup"),
            ("Flapjack/Pancake/Proofs/CrepInline.lean",
             "SUBMAP_IMP_FUPDATE_SUBMAP"),
            ("Flapjack/Pancake/Proofs/CrepInline.lean",
             "SUBMAP_IMP_DOMSUB_SUBMAP"),
            ("Flapjack/Pancake/Proofs/CrepInline.lean",
             "SUBMAP_IMP_DOMSUB_FUPDATE"),
            ("Flapjack/Pancake/Proofs/CrepInline.lean",
             "res_var_commutes_strong"),
            ("Flapjack/Pancake/Proofs/CrepInline.lean",
             "res_var_foldl_commutes_strong"),
            ("Flapjack/Pancake/Proofs/CrepInline.lean",
             "flookup_res_var_is_mem_zip_eq"),
        }
        for key in production:
            with self.subTest(key=key):
                self.assertEqual(by_key[key]["statement_status"],
                                 "documented_mismatch")
                self.assertNotIn(key, MAP["tagged_declarations"]())

    def test_globals_lookup_carrier_mismatch_is_documented(self):
        key = ("Flapjack/Pancake/Proofs/PanToCrep.lean", "globalsLookup")
        self.assertIn(key, MAP["DOCUMENTED_MISMATCHES"])
        hol_path, hol_name, reviewer = MAP["DOCUMENTED_MISMATCHES"][key]
        self.assertEqual(
            (hol_path, hol_name),
            (
                "cakeml/pancake/proofs/pan_to_crepProofScript.sml",
                "globals_lookup_def",
            ),
        )
        self.assertIn("flapjack-pxn.18.3.5.8.8", reviewer)

    def test_pan_to_crep_definition_cluster_mismatches_are_documented(self):
        expected = {
            "excpRel": "excp_rel_def",
            "ctxtFc": "ctxt_fc_def",
            "codeRel": "code_rel_def",
            "stateRel": "state_rel_def",
            "localsRel": "locals_rel_def",
        }
        for lean_name, hol_name in expected.items():
            key = ("Flapjack/Pancake/Proofs/PanToCrep.lean", lean_name)
            self.assertIn(key, MAP["DOCUMENTED_MISMATCHES"])
            hol_path, got_hol_name, reviewer = MAP["DOCUMENTED_MISMATCHES"][key]
            self.assertEqual(hol_path, "cakeml/pancake/proofs/pan_to_crepProofScript.sml")
            self.assertEqual(got_hol_name, hol_name)
            self.assertIn("flapjack-pxn.18.3.5.8", reviewer)

    def test_pan_value_evaluator_stability_mismatches_are_documented(self):
        expected = {
            "evalPanValueExps_update_local_not_mem": "update_locals_not_vars_eval_mmap",
            "evalPanValueExps_update_locals_not_mem": "opt_mmap_eval_distinct_lists_not_affect",
            "evalPanValueExp_update_locals_not_mem": "eval_distinct_lists_not_affect",
        }
        for lean_name, hol_name in expected.items():
            key = ("Flapjack/PanValueEvaluatorStability.lean", lean_name)
            self.assertIn(key, MAP["DOCUMENTED_MISMATCHES"])
            hol_path, got_hol_name, reviewer = MAP["DOCUMENTED_MISMATCHES"][key]
            self.assertEqual(hol_path, "cakeml/pancake/proofs/pan_to_crepProofScript.sml")
            self.assertEqual(got_hol_name, hol_name)
            self.assertIn("flapjack-pxn.18.3.5.8", reviewer)


    def test_pansem_word_lab_carrier_is_reviewed_exact(self):
        key = ("Flapjack/Pancake/Semantics/PanSem.lean", "HolWordLab")
        self.assertNotIn(key, MAP["DOCUMENTED_MISMATCHES"])
        manifest = json.loads(MAP["DEFAULT_MANIFEST"].read_text())
        by_key = {
            (record["lean_path"], record["lean_name"]): record for record in manifest
        }
        record = by_key[key]
        self.assertEqual(record["statement_status"], "reviewed_exact")
        self.assertEqual((record["hol_path"], record["hol_name"]),
                         ("cakeml/pancake/semantics/panSemScript.sml", "word_lab"))
        self.assertIn("flapjack-0lj.5", record["reviewer"])


    def test_panprops_decs_stcnames_only_functions_exact_ports(self):
        manifest = json.loads(MAP["DEFAULT_MANIFEST"].read_text())
        by_key = {
            (record["lean_path"], record["lean_name"]): record for record in manifest
        }
        expected = {
            ("Flapjack/Pancake/Semantics/PanProps.lean",
             "decsStcnamesHOLExact_of_functions_or_decls_or_exnDecls"): (
                "cakeml/pancake/semantics/panPropsScript.sml",
                "decs_stcnames_only_functions"),
            ("Flapjack/Pancake/Semantics/PanProps.lean",
             "decsStcnamesHOLExact_of_functions"): (
                "cakeml/pancake/semantics/panPropsScript.sml",
                "decs_stcnames_only_functions2"),
        }
        for key, (hol_path, hol_name) in expected.items():
            with self.subTest(key=key):
                record = by_key[key]
                self.assertEqual(
                    (record["hol_path"], record["hol_name"]), (hol_path, hol_name))
                self.assertEqual(record["statement_status"], "reviewed_exact")
                self.assertIn(key, MAP["tagged_declarations"]())


    def test_pansem_the_val_word_mismatch_is_documented(self):
        key = ("Flapjack/Pancake/Semantics/PanSemStateEval.lean", "holValueWord")
        self.assertIn(key, MAP["DOCUMENTED_MISMATCHES"])
        hol_path, hol_name, reviewer = MAP["DOCUMENTED_MISMATCHES"][key]
        self.assertEqual(hol_path, "cakeml/pancake/semantics/panSemScript.sml")
        self.assertEqual(hol_name, "theValWord_def")
        self.assertIn("flapjack-0lj.5", reviewer)
        manifest = json.loads(MAP["DEFAULT_MANIFEST"].read_text())
        by_key = {
            (record["lean_path"], record["lean_name"]): record for record in manifest
        }
        record = by_key[key]
        self.assertEqual(record["statement_status"], "documented_mismatch")
        self.assertEqual((record["hol_path"], record["hol_name"]), (hol_path, hol_name))


    def test_pansem_set_var_set_global_finite_ports(self):
        manifest = json.loads(MAP["DEFAULT_MANIFEST"].read_text())
        by_key = {
            (record["lean_path"], record["lean_name"]): record for record in manifest
        }
        expected = {
            "setVarHOLFinite": "set_var_def",
            "setGlobalHOLFinite": "set_global_def",
        }
        for lean_name, hol_name in expected.items():
            key = ("Flapjack/Pancake/Semantics/PanSem/StateExactFiniteMap.lean",
                   lean_name)
            with self.subTest(key=key):
                record = by_key[key]
                self.assertEqual((record["hol_path"], record["hol_name"]),
                                 ("cakeml/pancake/semantics/panSemScript.sml",
                                  hol_name))
                self.assertEqual(
                    record["statement_status"],
                    "reviewed_fmap_as_finite_support_words_as_type_indexed_bitvec")
                self.assertTrue(record["words_as_type_indexed_bitvec"])
                self.assertIn(key, MAP["tagged_declarations"]())


    def test_panlang_functions_append_filter_exact_ports(self):
        manifest = json.loads(MAP["DEFAULT_MANIFEST"].read_text())
        by_key = {
            (record["lean_path"], record["lean_name"]): record for record in manifest
        }
        expected = {
            ("Flapjack/Pancake/PanLang/Decl.lean", "isDeclHOL"): (
                "cakeml/pancake/panLangScript.sml", "is_decl_def"),
            ("Flapjack/Pancake/PanLang/Decl.lean", "isFunctionHOL"): (
                "cakeml/pancake/panLangScript.sml", "is_function_def"),
            ("Flapjack/Pancake/Semantics/PanProps.lean", "functionsHOL_append"): (
                "cakeml/pancake/semantics/panPropsScript.sml", "functions_append"),
            ("Flapjack/Pancake/Semantics/PanProps.lean",
             "functionsHOL_filter_isFunction"): (
                "cakeml/pancake/semantics/panPropsScript.sml", "functions_FILTER"),
            ("Flapjack/Pancake/Semantics/PanProps.lean",
             "functionsHOL_filter_isDecl"): (
                "cakeml/pancake/semantics/panPropsScript.sml", "functions_FILTER'"),
        }
        for key, (hol_path, hol_name) in expected.items():
            with self.subTest(key=key):
                record = by_key[key]
                self.assertEqual(
                    (record["hol_path"], record["hol_name"]), (hol_path, hol_name))
                self.assertEqual(record["statement_status"], "reviewed_exact")
                self.assertIn(key, MAP["tagged_declarations"]())

        # The ARB-carrying functions_eq_FILTER is deliberately not tagged.
        eq_filter = ("Flapjack/Pancake/Semantics/PanProps.lean",
                     "functionsHOL_eq_filter")
        self.assertNotIn(eq_filter, MAP["tagged_declarations"]())
        self.assertNotIn(eq_filter, by_key)

    def test_panprops_is_wf_shape_of_v_exact_port(self):
        manifest = json.loads(MAP["DEFAULT_MANIFEST"].read_text())
        key = ("Flapjack/Pancake/Semantics/PanProps.lean",
               "isWfShapeValueHOLExact_shapeOfHOLExact")
        record = next(
            (r for r in manifest
             if (r["lean_path"], r["lean_name"]) == key), None)
        self.assertIsNotNone(record)
        self.assertEqual(
            (record["hol_path"], record["hol_name"]),
            ("cakeml/pancake/semantics/panPropsScript.sml", "is_wf_shape_of_v"))
        self.assertEqual(record["statement_status"], "reviewed_exact")
        self.assertIn(key, MAP["tagged_declarations"]())

    def test_panprops_pan_primop_is_wf_shape_v_exact_port(self):
        manifest = json.loads(MAP["DEFAULT_MANIFEST"].read_text())
        key = ("Flapjack/Pancake/Semantics/PanProps.lean",
               "panPrimopHOLExact_isWfShapeValueHOLExact")
        record = next(
            (r for r in manifest
             if (r["lean_path"], r["lean_name"]) == key), None)
        self.assertIsNotNone(record)
        self.assertEqual(
            (record["hol_path"], record["hol_name"]),
            ("cakeml/pancake/semantics/panPropsScript.sml",
             "pan_primop_is_wf_shape_v"))
        self.assertEqual(record["statement_status"], "reviewed_exact")
        self.assertIn(key, MAP["tagged_declarations"]())

    def test_panprops_shape_wf_nil_and_drop_exact_ports(self):
        manifest = json.loads(MAP["DEFAULT_MANIFEST"].read_text())
        by_key = {
            (record["lean_path"], record["lean_name"]): record for record in manifest
        }
        expected = {
            ("Flapjack/Pancake/Semantics/PanProps.lean",
             "isWfShapeValueHOLExact_nil_step1"): (
                "cakeml/pancake/semantics/panPropsScript.sml",
                "is_wf_shape_v_nil_step1"),
            ("Flapjack/Pancake/Semantics/PanProps.lean",
             "isWfShapeExactHOL_shapeOfHOLExact_eq_isWfShapeValueHOLExact_nil"): (
                "cakeml/pancake/semantics/panPropsScript.sml",
                "is_wf_shape_v_nil"),
            ("Flapjack/Pancake/Semantics/PanProps.lean",
             "isWfShapeValueHOLExact_drop"): (
                "cakeml/pancake/semantics/panPropsScript.sml",
                "is_wf_shape_v_drop"),
        }
        for key, (hol_path, hol_name) in expected.items():
            with self.subTest(key=key):
                record = by_key[key]
                self.assertEqual(
                    (record["hol_path"], record["hol_name"]), (hol_path, hol_name))
                if key[1] == "isWfShapeValueHOLExact_nil_step1":
                    self.assertEqual(record["statement_status"],
                                     "reviewed_words_as_type_indexed_bitvec")
                    self.assertIs(record["words_as_type_indexed_bitvec"], True)
                else:
                    self.assertEqual(record["statement_status"], "reviewed_exact")
                self.assertIn(key, MAP["tagged_declarations"]())

    def test_panprops_mem_load_is_wf_shape_v_exact_port(self):
        manifest = json.loads(MAP["DEFAULT_MANIFEST"].read_text())
        key = ("Flapjack/Pancake/Semantics/PanProps.lean",
               "memLoadHOLExact_isWfShapeValueHOLExact")
        record = next(
            (r for r in manifest
             if (r["lean_path"], r["lean_name"]) == key), None)
        self.assertIsNotNone(record)
        self.assertEqual(
            (record["hol_path"], record["hol_name"]),
            ("cakeml/pancake/semantics/panPropsScript.sml",
             "mem_load_is_wf_shape_v"))
        self.assertEqual(record["statement_status"], "reviewed_exact")
        self.assertIn(key, MAP["tagged_declarations"]())

    def test_panprops_mem_load_shape_eq_exact_ports(self):
        manifest = json.loads(MAP["DEFAULT_MANIFEST"].read_text())
        by_key = {
            (record["lean_path"], record["lean_name"]): record for record in manifest
        }
        expected = {
            ("Flapjack/Pancake/Semantics/PanProps.lean",
             "memLoadHOLExact_shape_eq"): (
                "cakeml/pancake/semantics/panPropsScript.sml",
                "mem_loads_some_shape_eq"),
            ("Flapjack/Pancake/Semantics/PanProps.lean",
             "memLoadHOLExact_some_shapeOf_eq"): (
                "cakeml/pancake/semantics/panPropsScript.sml",
                "mem_load_some_shape_eq"),
        }
        for key, (hol_path, hol_name) in expected.items():
            with self.subTest(key=key):
                record = by_key[key]
                self.assertEqual(
                    (record["hol_path"], record["hol_name"]), (hol_path, hol_name))
                self.assertEqual(record["statement_status"], "reviewed_exact")
                self.assertIn(key, MAP["tagged_declarations"]())

    def test_panprops_every_exp_and_exps_of_exact_ports(self):
        manifest = json.loads(MAP["DEFAULT_MANIFEST"].read_text())
        by_key = {
            (record["lean_path"], record["lean_name"]): record for record in manifest
        }
        expected = {
            ("Flapjack/Pancake/Semantics/PanProps.lean", "everyExpHOL"): (
                "cakeml/pancake/semantics/panPropsScript.sml", "every_exp_def"),
            ("Flapjack/Pancake/Semantics/PanProps.lean", "expsOfHOL"): (
                "cakeml/pancake/semantics/panPropsScript.sml", "exps_of_def"),
        }
        for key, (hol_path, hol_name) in expected.items():
            with self.subTest(key=key):
                record = by_key[key]
                self.assertEqual(
                    (record["hol_path"], record["hol_name"]), (hol_path, hol_name))
                self.assertEqual(record["statement_status"], "reviewed_exact")
                self.assertIn(key, MAP["tagged_declarations"]())


    def test_panprops_localised_and_mmap_exact_ports(self):
        manifest = json.loads(MAP["DEFAULT_MANIFEST"].read_text())
        by_key = {
            (record["lean_path"], record["lean_name"]): record for record in manifest
        }
        expected = {
            ("Flapjack/Pancake/Semantics/PanProps.lean", "localisedExpHOL"): (
                "cakeml/pancake/semantics/panPropsScript.sml", "localised_exp_real_def"),
            ("Flapjack/Pancake/Semantics/PanProps.lean", "namelessExpHOL"): (
                "cakeml/pancake/semantics/panPropsScript.sml", "nameless_exp_real_def"),
            ("Flapjack/Pancake/Semantics/PanProps.lean", "localisedProgHOL"): (
                "cakeml/pancake/semantics/panPropsScript.sml", "localised_prog_def"),
            ("Flapjack/Pancake/Semantics/PanProps.lean", "optMmapEqSomeHelper"): (
                "cakeml/pancake/semantics/panPropsScript.sml", "opt_mmap_eq_some_helper"),
        }
        for key, (hol_path, hol_name) in expected.items():
            with self.subTest(key=key):
                record = by_key[key]
                self.assertEqual(
                    (record["hol_path"], record["hol_name"]), (hol_path, hol_name))
                self.assertEqual(record["statement_status"], "reviewed_exact")
                self.assertIn(key, MAP["tagged_declarations"]())

        # The production String-carrier predicate keeps the withdrawn tag.
        mismatch = ("Flapjack/PanLocalised.lean", "localisedProg")
        record = by_key[mismatch]
        self.assertEqual(
            (record["hol_path"], record["hol_name"]),
            ("cakeml/pancake/semantics/panPropsScript.sml", "localised_prog_def"))
        self.assertEqual(record["statement_status"], "documented_mismatch")
        self.assertIn("String", record["reviewer"])
        self.assertNotIn(mismatch, MAP["tagged_declarations"]())


class ExistentialFmapStatusTest(unittest.TestCase):
    def _record(self, **overrides):
        record = {
            "hol_path": "cakeml/pancake/proofs/crep_inlineProofScript.sml",
            "hol_name": "code_inl_rel_def",
            "lean_path": "Flapjack/Example.lean",
            "lean_name": "codeInlRelExact",
            "statement_status": "reviewed_fmap_as_finite_support_existentials",
            "reviewer": "source comparison of HOL existential binder inl_bag",
            "fmap_as_finite_support_existentials": ["inl_bag"],
        }
        record.update(overrides)
        return record

    def _tag(self, existentials=("inl_bag",)):
        return {
            ("Flapjack/Example.lean", "codeInlRelExact"): (
                "cakeml/pancake/proofs/crep_inlineProofScript.sml",
                "code_inl_rel_def", (), (), (), (), False, (), False, False,
                (), existentials,
            )
        }

    def _errors(self, record, tagged):
        return MAP["validate_inventory"]([record], set(), tagged, set())

    def test_accepts_existential_map_status(self):
        self.assertEqual(self._errors(self._record(), self._tag()), [])

    def test_rejects_status_without_qualifier(self):
        errors = self._errors(self._record(), self._tag(()))
        self.assertTrue(any("needs a fmap_as_finite_support_existentials" in e for e in errors))

    def test_requires_source_note_naming_binder(self):
        errors = self._errors(
            self._record(reviewer="reviewed without source comparison"), self._tag())
        self.assertTrue(any("source-comparison note naming every existential binder" in e
                            for e in errors))

    def test_rejects_manifest_tag_disagreement(self):
        errors = self._errors(
            self._record(fmap_as_finite_support_existentials=["other"]), self._tag())
        self.assertTrue(any("do not match its @[hol] tag" in e for e in errors))

    def test_accepts_relation_existential_and_word_carrier_composition(self):
        record = self._record(
            statement_status=(
                "reviewed_fmap_as_finite_support_relation_existentials_"
                "words_as_type_indexed_bitvec"
            ),
            reviewer="source comparison of CrepSemHOLState maps, inl_fs, and inl_bag",
            fmap_as_finite_support_relation=[
                "CrepSemHOLState.locals", "CrepSemHOLState.globals",
                "CrepSemHOLState.code", "inl_fs",
            ],
            words_as_type_indexed_bitvec=True,
        )
        tagged = self._tag()
        key = next(iter(tagged))
        old = tagged[key]
        tagged[key] = old[:7] + (
            (("CrepSemHOLState", "locals"), ("CrepSemHOLState", "globals"),
             ("CrepSemHOLState", "code"), ("inl_fs", "")),
            False, True, (), ("inl_bag",),
        )
        self.assertEqual(self._errors(record, tagged), [])


class StandaloneFmapResultStatusTest(unittest.TestCase):
    def _record(self, **overrides):
        record = {
            "hol_path": "cakeml/pancake/pan_to_crepScript.sml",
            "hol_name": "get_eids_from_decls_def",
            "lean_path": "Flapjack/Example.lean",
            "lean_name": "getEidsFromDeclsHOL",
            "statement_status": "reviewed_fmap_as_finite_support_result",
            "reviewer": "source comparison of HOL/Lean carriers",
            "fmap_as_finite_support_result": True,
        }
        record.update(overrides)
        return record

    def _tag(self, fmap_result=True, fmap_fields=()):
        return {
            ("Flapjack/Example.lean", "getEidsFromDeclsHOL"): (
                "cakeml/pancake/pan_to_crepScript.sml",
                "get_eids_from_decls_def",
                (), (), (), fmap_fields, fmap_result,
            )
        }

    def _errors(self, record, tagged):
        return MAP["validate_inventory"]([record], set(), tagged, set())

    def test_accepts_standalone_result_status(self):
        self.assertEqual(self._errors(self._record(), self._tag()), [])

    def test_accepts_result_and_word_carrier_composition(self):
        record = self._record(
            statement_status="reviewed_fmap_as_finite_support_result_words_as_type_indexed_bitvec",
            words_as_type_indexed_bitvec=True,
        )
        tagged = self._tag()
        key = next(iter(tagged))
        tagged[key] += ((), False, True)
        self.assertEqual(self._errors(record, tagged), [])

    def test_result_word_composition_requires_both_qualifiers(self):
        status = "reviewed_fmap_as_finite_support_result_words_as_type_indexed_bitvec"
        for has_result, has_words in [(False, True), (True, False), (False, False)]:
            record = self._record(statement_status=status,
                fmap_as_finite_support_result=has_result,
                words_as_type_indexed_bitvec=has_words)
            tagged = self._tag(fmap_result=has_result)
            key = next(iter(tagged))
            tagged[key] += ((), False, has_words)
            errors = self._errors(record, tagged)
            self.assertTrue(any("needs both" in error for error in errors), errors)

    def test_rejects_reviewed_exact_for_result_qualifier(self):
        errors = self._errors(
            self._record(statement_status="reviewed_exact"), self._tag())
        self.assertTrue(any("reviewed_exact" in error for error in errors))

    def test_rejects_missing_manifest_field(self):
        record = self._record()
        del record["fmap_as_finite_support_result"]
        errors = self._errors(record, self._tag())
        self.assertTrue(any("does not match its @[hol] tag" in error for error in errors))

    def test_rejects_result_status_without_qualifier(self):
        errors = self._errors(self._record(), self._tag(fmap_result=False))
        self.assertTrue(any("needs a fmap_as_finite_support_result" in error for error in errors))

    def test_rejects_field_and_result_qualifiers_together(self):
        errors = self._errors(
            self._record(
                fmap_as_finite_support=["locals"],
            ),
            self._tag(fmap_result=True, fmap_fields=("locals",)),
        )
        self.assertTrue(any("mutually exclusive" in error for error in errors))

    def test_rejects_result_status_without_source_note(self):
        errors = self._errors(
            self._record(reviewer="inventory only"), self._tag())
        self.assertTrue(any("source-comparison note" in error for error in errors))


class MultiOwnerFmapRelationStatusTest(unittest.TestCase):
    def _record(self, **overrides):
        record = {
            "hol_path": "cakeml/pancake/proofs/pan_to_crepProofScript.sml",
            "hol_name": "evaluate_shape_invariant_ret_inst",
            "lean_path": "Flapjack/Example.lean",
            "lean_name": "evaluateShapeInvariant",
            "statement_status": "reviewed_fmap_as_finite_support_relation",
            "reviewer": "source comparison of HOL/Lean carrier structures",
            "fmap_as_finite_support_relation": [
                "PanState.locals", "CrepState.locals"],
        }
        record.update(overrides)
        return record

    def _tag(self, carriers=(("PanState", "locals"), ("CrepState", "locals"))):
        return {
            ("Flapjack/Example.lean", "evaluateShapeInvariant"): (
                "cakeml/pancake/proofs/pan_to_crepProofScript.sml",
                "evaluate_shape_invariant_ret_inst",
                (), (), (), (), False, carriers,
            )
        }

    def test_accepts_multi_owner_relation_status(self):
        errors = MAP["validate_inventory"](
            [self._record()], set(), self._tag(), set())
        self.assertEqual(errors, [])

    def test_rejects_status_without_qualifier(self):
        errors = MAP["validate_inventory"](
            [self._record()], set(), self._tag(()), set())
        self.assertTrue(any(
            "needs a fmap_as_finite_support_relation @[hol] tag" in error
            for error in errors
        ))

    def test_rejects_manifest_tag_disagreement(self):
        errors = MAP["validate_inventory"](
            [self._record(fmap_as_finite_support_relation=["Other.locals"])],
            set(), self._tag(), set())
        self.assertTrue(any("do not match its @[hol] tag" in error for error in errors))


    def test_rejects_relation_combined_with_field_qualifier(self):
        tagged = self._tag()
        key = next(iter(tagged))
        hol, name, *rest = tagged[key]
        carriers = rest[5]
        tagged[key] = (hol, name, (), (), (), ("globals",), False, carriers)
        errors = MAP["validate_inventory"](
            [self._record(fmap_as_finite_support=["globals"])], set(), tagged, set())
        self.assertTrue(any("mutually exclusive" in e for e in errors), errors)

    def test_rejects_relation_combined_with_result_qualifier(self):
        tagged = self._tag()
        key = next(iter(tagged))
        hol, name, *rest = tagged[key]
        carriers = rest[5]
        tagged[key] = (hol, name, (), (), (), (), True, carriers)
        errors = MAP["validate_inventory"]([self._record()], set(), tagged, set())
        self.assertTrue(any("mutually exclusive" in e for e in errors), errors)

    def test_rejects_relation_without_source_note(self):
        errors = MAP["validate_inventory"](
            [self._record(reviewer="no comparison recorded")],
            set(), self._tag(), set())
        self.assertTrue(any("source-comparison note" in e for e in errors), errors)


class CombinedRelationWordsStatusTest(unittest.TestCase):
    COMBINED = (
        "reviewed_fmap_as_finite_support_relation_words_as_type_indexed_bitvec"
    )

    def _record(self, **overrides):
        record = {
            "hol_path": "cakeml/pancake/proofs/pan_to_crepProofScript.sml",
            "hol_name": "compile_exp_val_rel",
            "lean_path": "Flapjack/Example.lean",
            "lean_name": "compileExpValRelHOL",
            "statement_status": self.COMBINED,
            "reviewer": "source comparison of HOL/Lean word and finite-map carriers",
            "fmap_as_finite_support_relation": ["PanState.globals", "CrepState.code"],
            "words_as_type_indexed_bitvec": True,
        }
        record.update(overrides)
        return record

    def _tag(self, carriers=(("PanState", "globals"), ("CrepState", "code")), words=True):
        return {
            ("Flapjack/Example.lean", "compileExpValRelHOL"): (
                "cakeml/pancake/proofs/pan_to_crepProofScript.sml",
                "compile_exp_val_rel",
                (), (), (), (), False, carriers, False, words,
            )
        }

    def _errors(self, record, tagged):
        return MAP["validate_inventory"]([record], set(), tagged, set())

    def test_accepts_combined_relation_words_status(self):
        self.assertEqual(self._errors(self._record(), self._tag()), [])

    def test_rejects_combined_status_without_words(self):
        errors = self._errors(self._record(), self._tag(words=False))
        self.assertTrue(any("needs both" in error for error in errors), errors)

    def test_rejects_combined_status_without_relation(self):
        errors = self._errors(self._record(), self._tag(carriers=()))
        self.assertTrue(any("needs both" in error for error in errors), errors)

    def test_rejects_relation_status_for_combined_qualifiers(self):
        errors = self._errors(
            self._record(statement_status="reviewed_fmap_as_finite_support_relation"),
            self._tag(),
        )
        self.assertTrue(
            any("words_as_type_indexed_bitvec" in error for error in errors), errors
        )

    def test_rejects_words_status_for_combined_qualifiers(self):
        errors = self._errors(
            self._record(statement_status="reviewed_words_as_type_indexed_bitvec"),
            self._tag(),
        )
        self.assertTrue(
            any("fmap_as_finite_support_relation" in error for error in errors), errors
        )

    def test_rejects_combined_status_without_source_note(self):
        errors = self._errors(
            self._record(reviewer="inventory only"), self._tag())
        self.assertTrue(any("source-comparison note" in error for error in errors), errors)


class FmapResultFieldExclusionTest(unittest.TestCase):
    def _record(self, **overrides):
        record = {
            "hol_path": "cakeml/pancake/pan_to_crepScript.sml",
            "hol_name": "make_vmap_def",
            "lean_path": "Flapjack/Example.lean",
            "lean_name": "makeVmapExact",
            "statement_status": "reviewed_fmap_as_finite_support_result",
            "reviewer": "source comparison of HOL/Lean finite-map carrier",
            "fmap_as_finite_support_result": True,
        }
        record.update(overrides)
        return record

    def _tag(self, fmap_fields=(), fmap_result=True):
        return {
            ("Flapjack/Example.lean", "makeVmapExact"): (
                "cakeml/pancake/pan_to_crepScript.sml",
                "make_vmap_def",
                (), (), (), fmap_fields, fmap_result, (),
            )
        }

    def test_rejects_result_combined_with_field_qualifier(self):
        errors = MAP["validate_inventory"](
            [self._record(fmap_as_finite_support=["locals"])],
            set(), self._tag(fmap_fields=("locals",)), set())
        self.assertTrue(any("mutually exclusive" in e for e in errors), errors)

    def test_rejects_result_without_source_note(self):
        errors = MAP["validate_inventory"](
            [self._record(reviewer="checked")], set(), self._tag(), set())
        self.assertTrue(any("source-comparison note" in e for e in errors), errors)


class FmapEqualitiesStatusTest(unittest.TestCase):
    """Theorem-level map equalities need their own reviewed status."""

    STATUS = "reviewed_fmap_as_finite_support_equalities"

    def _record(self, **overrides):
        record = {
            "hol_path": "cakeml/pancake/proofs/pan_to_crepProofScript.sml",
            "hol_name": "slc_tlc_rw",
            "lean_path": "Flapjack/Example.lean",
            "lean_name": "slcTlcRw",
            "statement_status": self.STATUS,
            "reviewer": "source comparison of each HOL map equality",
            "fmap_as_finite_support_equalities": True,
        }
        record.update(overrides)
        return record

    def _tag(self, equalities=True, fmap_fields=(), fmap_result=False,
             fmap_relation=()):
        return {
            ("Flapjack/Example.lean", "slcTlcRw"): (
                "cakeml/pancake/proofs/pan_to_crepProofScript.sml",
                "slc_tlc_rw",
                (), (), (), fmap_fields, fmap_result, fmap_relation, equalities,
            )
        }

    def _errors(self, record, tagged):
        return MAP["validate_inventory"]([record], set(), tagged, set())

    def test_accepts_equalities_status(self):
        self.assertEqual(self._errors(self._record(), self._tag()), [])

    def test_rejects_equalities_status_without_qualifier(self):
        errors = self._errors(self._record(), self._tag(equalities=False))
        self.assertTrue(
            any("needs a fmap_as_finite_support_equalities" in e for e in errors),
            errors,
        )

    def test_rejects_equalities_tag_without_status(self):
        errors = self._errors(
            self._record(statement_status="pending_statement_review",
                         fmap_as_finite_support_equalities=False),
            self._tag(),
        )
        self.assertTrue(
            any("needs a reviewed source classification" in e for e in errors),
            errors,
        )

    def test_rejects_equalities_tag_with_reviewed_exact(self):
        errors = self._errors(
            self._record(statement_status="reviewed_exact"), self._tag())
        self.assertTrue(
            any("cannot have reviewed_exact status" in e for e in errors), errors)


class CombinedFmapWordsStatusTest(unittest.TestCase):
    """fmap_as_finite_support must compose with words_as_type_indexed_bitvec."""

    COMBINED = (
        "reviewed_fmap_as_finite_support_words_as_type_indexed_bitvec"
    )

    def _record(self, **overrides):
        record = {
            "hol_path": "cakeml/pancake/semantics/crepSemScript.sml",
            "hol_name": "evaluate_def",
            "lean_path": "Flapjack/Example.lean",
            "lean_name": "evalProg",
            "statement_status": self.COMBINED,
            "reviewer": "source comparison of HOL/Lean word and finite-map carriers",
            "fmap_as_finite_support": ["locals", "globals", "code"],
            "words_as_type_indexed_bitvec": True,
        }
        record.update(overrides)
        return record

    def _tag(self, fmap_fields=("locals", "globals", "code"), words=True):
        return {
            ("Flapjack/Example.lean", "evalProg"): (
                "cakeml/pancake/semantics/crepSemScript.sml",
                "evaluate_def",
                (), (), (), fmap_fields, False, (), False, words,
            )
        }

    def _errors(self, record, tagged):
        return MAP["validate_inventory"]([record], set(), tagged, set())

    def test_accepts_combined_status(self):
        self.assertEqual(self._errors(self._record(), self._tag()), [])

    def test_rejects_combined_status_without_words_qualifier(self):
        errors = self._errors(self._record(), self._tag(words=False))
        self.assertTrue(any("needs both" in error for error in errors))

    def test_rejects_combined_status_without_fmap_qualifier(self):
        errors = self._errors(self._record(), self._tag(fmap_fields=()))
        self.assertTrue(any("needs both" in error for error in errors))

    def test_rejects_words_status_for_combined_qualifiers(self):
        errors = self._errors(
            self._record(statement_status="reviewed_words_as_type_indexed_bitvec"),
            self._tag(),
        )
        self.assertTrue(any("fmap_as_finite_support" in error for error in errors))

    def test_rejects_fmap_status_for_combined_qualifiers(self):
        errors = self._errors(
            self._record(statement_status="reviewed_fmap_as_finite_support"),
            self._tag(),
        )
        self.assertTrue(any("words_as_type_indexed_bitvec" in error for error in errors))


class WordDimensionAsWidthStatusTest(unittest.TestCase):
    def setUp(self):
        self.path = "Flapjack/Example.lean"
        self.key = (self.path, "wordSemMustTerminateLimit")
        self.hol = (
            "cakeml/compiler/backend/semantics/wordSemScript.sml",
            "MustTerminate_limit_def",
        )
        self.tag = {
            self.key: (
                *self.hol, (), (), (), (), False, (), False, False, (), (), "width",
            )
        }

    def record(self, **overrides):
        record = {
            "hol_path": self.hol[0],
            "hol_name": self.hol[1],
            "lean_path": self.path,
            "lean_name": self.key[1],
            "statement_status": "reviewed_word_dimension_as_width",
            "word_dimension_as_width": "width",
            "reviewer": "source comparison: HOL dimword dimension corresponds to width",
        }
        record.update(overrides)
        return record

    def errors(self, record, tagged=None):
        return MAP["validate_inventory"](
            [record], {self.key}, self.tag if tagged is None else tagged, set()
        )

    def test_accepts_source_reviewed_word_free_dimension_qualifier(self):
        self.assertEqual(self.errors(self.record()), [])

    def test_requires_matching_tag_and_manifest_width(self):
        untagged = {self.key: (*self.tag[self.key][:-1], None)}
        self.assertTrue(any("manifest word_dimension_as_width" in error
                            for error in self.errors(self.record(), untagged)))
        self.assertTrue(any("needs a matching @[hol] qualifier" in error
                            for error in self.errors(
                                self.record(statement_status="reviewed_word_dimension_as_width",
                                            word_dimension_as_width=None),
                                untagged)))

    def test_rejects_exact_status_and_requires_source_note(self):
        self.assertTrue(any("cannot have reviewed_exact" in error
                            for error in self.errors(
                                self.record(statement_status="reviewed_exact"))))
        self.assertTrue(any("source-comparison note" in error
                            for error in self.errors(
                                self.record(reviewer="reviewed only"))))

    def test_rejects_combining_word_free_dimension_and_word_carrier(self):
        tag = dict(self.tag)
        tag[self.key] = (*tag[self.key][:9], True, *tag[self.key][10:])
        errors = self.errors(self.record(), tag)
        self.assertTrue(any("mutually exclusive" in error for error in errors))



class RealsAsRationalCutsStatusTest(unittest.TestCase):
    def setUp(self):
        self.path = "Flapjack/Example.lean"
        self.key = (self.path, "fpSemFpUopComp")
        self.hol = ("cakeml/semantics/fpSemScript.sml", "fp_uop_comp_def")
        base = (*self.hol, (), (), (), (), False, (), False, False, (), (), None, ())
        self.tag = {self.key: (*base, (), True)}
        self.untagged = {self.key: (*base, (), False)}
        words = (*self.hol, (), (), (), ("fpRegs", "store"), False, (), False, True,
                 (), (), None, ())
        self.words_tag = {self.key: (*words, (), True)}

    def record(self, **overrides):
        record = {
            "hol_path": self.hol[0],
            "hol_name": self.hol[1],
            "lean_path": self.path,
            "lean_name": self.key[1],
            "statement_status": "reviewed_reals_as_rational_cuts",
            "reals_as_rational_cuts": True,
            "reviewer": ("source comparison: FP_Sqrt via the reals_as_rational_cuts "
                         "rendering, docs/SOUNDNESS.md item 8"),
        }
        record.update(overrides)
        return {key: value for key, value in record.items() if value is not None}

    def errors(self, record, tagged=None):
        return MAP["validate_inventory"](
            [record], {self.key}, self.tag if tagged is None else tagged, set()
        )

    def test_accepts_source_reviewed_reals_qualifier(self):
        self.assertEqual(self.errors(self.record()), [])

    def test_requires_matching_tag_and_manifest_field(self):
        self.assertTrue(any("manifest reals_as_rational_cuts" in error
                            for error in self.errors(
                                self.record(reals_as_rational_cuts=None))))
        self.assertTrue(any("manifest reals_as_rational_cuts" in error
                            for error in self.errors(self.record(), self.untagged)))
        self.assertTrue(any("needs a matching @[hol] qualifier" in error
                            for error in self.errors(
                                self.record(reals_as_rational_cuts=None), self.untagged)))

    def test_rejects_exact_status_and_requires_note(self):
        self.assertTrue(any("cannot have reviewed_exact" in error
                            for error in self.errors(
                                self.record(statement_status="reviewed_exact"))))
        self.assertTrue(any("naming the qualifier" in error
                            for error in self.errors(
                                self.record(reviewer="source comparison only"))))

    def test_inherited_assumption_needs_note_and_excludes_the_qualifier(self):
        base = (*self.hol, (), (), (), (), False, (), False, False, (), (), None, ())
        dependent_tag = {self.key: (*base, (), False)}
        dependent = self.record(
            statement_status="reviewed_exact", reals_as_rational_cuts=None,
            inherits_reals_as_rational_cuts=True,
            reviewer="source comparison; inherited reals_as_rational_cuts assumption via inst",
        )
        self.assertEqual(self.errors(dependent, dependent_tag), [])
        self.assertTrue(any("naming the inherited" in error
                            for error in self.errors(
                                dict(dependent, reviewer="source comparison"), dependent_tag)))
        both = self.record(inherits_reals_as_rational_cuts=True,
                           reviewer=self.record()["reviewer"] + " inherited too")
        self.assertTrue(any("does not also record an inherited assumption" in error
                            for error in self.errors(both)))

    def test_combined_qualifiers_keep_their_status(self):
        combined = self.record(
            statement_status="reviewed_fmap_as_finite_support_words_as_type_indexed_bitvec",
            fmap_as_finite_support=["fpRegs", "store"],
            words_as_type_indexed_bitvec=True,
        )
        self.assertFalse(any("reals_as_rational_cuts" in error
                             for error in self.errors(combined, self.words_tag)))
        wrong = dict(combined, statement_status="reviewed_reals_as_rational_cuts")
        self.assertTrue(any("keeps the status those qualifiers require" in error
                            for error in self.errors(wrong, self.words_tag)))



class FmapEqualityStatusTest(unittest.TestCase):
    """A single theorem-level map equality needs its own reviewed status."""

    STATUS = "reviewed_fmap_as_finite_support_equality"

    def _record(self, **overrides):
        record = {
            "hol_path": "cakeml/pancake/proofs/pan_globalsProofScript.sml",
            "hol_name": "res_var_FEMPTY",
            "lean_path": "Flapjack/Example.lean",
            "lean_name": "resVarFEMPTYExact",
            "statement_status": self.STATUS,
            "reviewer": "source comparison of the single HOL map equality "
                        "fmap_as_finite_support_equality",
            "fmap_as_finite_support_equality": True,
        }
        record.update(overrides)
        return record

    def _tag(self, equality=True, equalities=False, fmap_fields=()):
        # 0..8 then padding to index 16 for the singular flag.
        head = (
            "cakeml/pancake/proofs/pan_globalsProofScript.sml",
            "res_var_FEMPTY",
            (), (), (), fmap_fields, False, (), equalities,
        )
        tail = ((), (), (), None, (), (), False, equality)
        return {("Flapjack/Example.lean", "resVarFEMPTYExact"): head + tail}

    def _errors(self, record, tagged):
        return MAP["validate_inventory"]([record], set(), tagged, set())

    def test_accepts_equality_status(self):
        self.assertEqual(self._errors(self._record(), self._tag()), [])

    def test_rejects_equality_status_without_qualifier(self):
        errors = self._errors(self._record(), self._tag(equality=False))
        self.assertTrue(
            any("needs a fmap_as_finite_support_equality" in e for e in errors),
            errors,
        )

    def test_rejects_equality_tag_without_status(self):
        errors = self._errors(
            self._record(statement_status="pending_statement_review",
                         fmap_as_finite_support_equality=False),
            self._tag(),
        )
        self.assertTrue(
            any("needs a reviewed source classification" in e for e in errors),
            errors,
        )

    def test_rejects_equality_tag_with_reviewed_exact(self):
        errors = self._errors(
            self._record(statement_status="reviewed_exact"), self._tag())
        self.assertTrue(any("reviewed_exact" in e for e in errors), errors)

    def test_rejects_equality_with_other_fmap_fields(self):
        errors = self._errors(
            self._record(), self._tag(fmap_fields=("locals",)))
        self.assertTrue(any("mutually exclusive" in e for e in errors), errors)

    # Combined single map equality + type-indexed word carrier.
    COMBINED = (
        "reviewed_fmap_as_finite_support_equality_words_as_type_indexed_bitvec"
    )

    def _words_tag(self):
        tag = self._tag()
        key = ("Flapjack/Example.lean", "resVarFEMPTYExact")
        tup = list(tag[key])
        tup[9] = True
        return {key: tuple(tup)}

    def test_accepts_combined_equality_words_status(self):
        record = self._record(
            statement_status=self.COMBINED,
            words_as_type_indexed_bitvec=True,
        )
        self.assertEqual(self._errors(record, self._words_tag()), [])

    def test_rejects_singular_status_with_words_qualifier(self):
        record = self._record(words_as_type_indexed_bitvec=True)
        errors = self._errors(record, self._words_tag())
        self.assertTrue(
            any("combined review status" in e for e in errors), errors)

    def test_rejects_combined_status_without_words_qualifier(self):
        record = self._record(statement_status=self.COMBINED)
        errors = self._errors(record, self._tag())
        self.assertTrue(
            any("needs a reviewed source classification" in e for e in errors),
            errors,
        )


if __name__ == "__main__":
    unittest.main()


class FmapResultObservationInventoryTest(unittest.TestCase):
    def fixture(self):
        record = {"hol_path": "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml",
                  "hol_name": "to_fmap_key_set", "lean_path": "Flapjack/Example.lean",
                  "lean_name": "observer", "statement_status": "reviewed_fmap_as_finite_support_result_observations",
                  "reviewer": "Source comparison: arbitrary cmp/tree domain observation, only reviewed producer map translation.",
                  "fmap_as_finite_support_result_observations": ["toFmap"]}
        tag = (record["hol_path"], record["hol_name"], (), (), (), (), False, (), False,
               False, (), (), None, (), (), False, False, ("toFmap",))
        return record, {(record["lean_path"], record["lean_name"]): tag}

    def test_exact_list_and_status_required(self):
        record, tags = self.fixture()
        self.assertEqual([], MAP["validate_inventory"]([record], set(), tags, set()))
        for changed in [dict(record, statement_status="reviewed_exact"),
                        dict(record, fmap_as_finite_support_result_observations=["other"]),
                        dict(record, reviewer="")]:
            self.assertTrue(MAP["validate_inventory"]([changed], set(), tags, set()))

    def test_status_cannot_be_used_without_qualifier(self):
        record, tags = self.fixture()
        key = next(iter(tags))
        tags[key] = tags[key][:-1] + ((),)
        self.assertTrue(MAP["validate_inventory"]([record], set(), tags, set()))


class FmapResultObservationCombinationTest(unittest.TestCase):
    def test_other_representation_qualifier_rejected(self):
        record, tags = FmapResultObservationInventoryTest().fixture()
        key = next(iter(tags))
        tag = list(tags[key]); tag[3] = ("identifier",); tags[key] = tuple(tag)
        record["names_as_string"] = ["identifier"]
        self.assertTrue(any("cannot combine" in error for error in
            MAP["validate_inventory"]([record], set(), tags, set())))
