"""Regression tests for the theorem-map / elaborated `@[hol]` consistency gate."""

import importlib.util
import json
import unittest
from pathlib import Path
from unittest.mock import patch


SCRIPT = Path(__file__).resolve().parents[1] / "check_hol_ref_export.py"
SPEC = importlib.util.spec_from_file_location("check_hol_ref_export", SCRIPT)
MODULE = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(MODULE)


class HolRefExportTest(unittest.TestCase):
    def setUp(self):
        self.manifest = [{
            "lean_path": "Flapjack/Pancake/Proofs/Example.lean",
            "lean_name": "exampleCorrect",
            "hol_path": "cakeml/pancake/proofs/exampleProofScript.sml",
            "hol_name": "example_correct",
            "statement_status": "reviewed_exact",
        }]
        self.export = [{
            "lean_name": "Flapjack.exampleCorrect",
            "hol_path": "cakeml/pancake/proofs/exampleProofScript.sml",
            "hol_name": "example_correct",
        }]

    def check_qualifier(self, status, manifest_fields, exported, without):
        """`exported` must pass and `without` must be rejected."""
        manifest = [{**self.manifest[0], "statement_status": status, **manifest_fields}]
        self.assertEqual(
            MODULE.check_records(manifest, [{**self.export[0], "qualifiers": exported}]), 1
        )
        with self.assertRaisesRegex(ValueError, "manifest qualifiers differ"):
            MODULE.check_records(manifest, [{**self.export[0], "qualifiers": without}])

    def test_result_observation_producers_match_export(self):
        self.check_qualifier(
            "reviewed_fmap_as_finite_support_result_observations",
            {"fmap_as_finite_support_result_observations": ["BalancedMap.toFmap"]},
            {"fmap_as_finite_support_result_observations": ["BalancedMap.toFmap"]},
            {"fmap_as_finite_support_result_observations": ["different"]},
        )

    def test_reviewed_row_matches_its_declaration(self):
        self.assertEqual(MODULE.check_records(self.manifest, self.export), 1)

    def test_escaped_source_leaf_matches_elaborated_name(self):
        manifest = [{**self.manifest[0], "lean_name": "«dfn'FMIN_S»"}]
        exported = [{**self.export[0], "lean_name": "Flapjack.RiscV.L3.dfn'FMIN_S"}]
        self.assertEqual(MODULE.check_records(manifest, exported), 1)
        with self.assertRaisesRegex(ValueError, "found 0"):
            MODULE.check_records(manifest, [{**exported[0], "lean_name": "Flapjack.dfn'FMIN_D"}])
        with self.assertRaisesRegex(ValueError, "found 2"):
            MODULE.check_records(manifest, exported + exported)

    def test_only_reviewed_rows_are_checked(self):
        pending = [{**self.manifest[0], "statement_status": "pending_statement_review"}]
        self.assertEqual(MODULE.check_records(pending, []), 0)

    def test_every_reviewed_status_prefix_is_checked(self):
        manifest = [{**self.manifest[0],
            "statement_status": "reviewed_fmap_as_finite_support_result_words_as_type_indexed_bitvec"}]
        with self.assertRaisesRegex(ValueError, "found 0"):
            MODULE.check_records(manifest, [])

    def test_names_as_string_qualifiers_must_match(self):
        self.check_qualifier(
            "reviewed_names_as_string",
            {"names_as_string": ["key", "generated"], "names_as_string_boundary": ["generated"]},
            {"list_as_array": [], "names_as_string": ["key", "generated"],
             "names_as_string_boundary": ["generated"]},
            {"list_as_array": [], "names_as_string": ["key", "generated"],
             "names_as_string_boundary": []},
        )

    def test_fmap_as_finite_support_qualifiers_must_match(self):
        self.check_qualifier(
            "reviewed_fmap_as_finite_support",
            {"fmap_as_finite_support": ["locals", "globals"]},
            {"fmap_as_finite_support": ["locals", "globals"]},
            {"fmap_as_finite_support": ["locals"]},
        )

    def test_multi_owner_relation_qualifier_must_match(self):
        self.check_qualifier(
            "reviewed_fmap_as_finite_support_relation",
            {"fmap_as_finite_support_relation": ["PanState.locals", "CrepState.locals"]},
            {"fmap_as_finite_support_relation": ["PanState.locals", "CrepState.locals"]},
            {"fmap_as_finite_support_relation": ["PanState.locals"]},
        )

    def test_heterogeneous_fmap_function_qualifier_must_match(self):
        self.check_qualifier(
            "reviewed_fmap_as_finite_support_heterogeneous_function",
            {"fmap_as_finite_support_heterogeneous_function": ["argument_1", "result_2"]},
            {"fmap_as_finite_support_heterogeneous_function": ["argument_1", "result_2"]},
            {"fmap_as_finite_support_heterogeneous_function": ["argument_1"]},
        )

    def test_fmap_as_finite_support_equalities_qualifier_must_match(self):
        self.check_qualifier(
            "reviewed_fmap_as_finite_support_equalities",
            {"fmap_as_finite_support_equalities": True},
            {"fmap_as_finite_support_equalities": True},
            {},
        )

    def test_fmap_as_finite_support_equality_qualifier_must_match(self):
        self.check_qualifier(
            "reviewed_fmap_as_finite_support_equality",
            {"fmap_as_finite_support_equality": True},
            {"fmap_as_finite_support_equality": True},
            {},
        )

    def test_fmap_as_finite_support_parameters_qualifier_must_match(self):
        self.check_qualifier(
            "reviewed_fmap_as_finite_support_parameters",
            {"fmap_as_finite_support_parameters": ["fm", "fm2"]},
            {"fmap_as_finite_support_parameters": ["fm", "fm2"]},
            {"fmap_as_finite_support_parameters": ["fm"]},
        )

    def test_fmap_as_finite_support_existentials_qualifier_must_match(self):
        self.check_qualifier(
            "reviewed_fmap_as_finite_support_existentials",
            {"fmap_as_finite_support_existentials": ["inl_bag"]},
            {"fmap_as_finite_support_existentials": ["inl_bag"]},
            {},
        )

    def test_words_as_type_indexed_bitvec_qualifier_must_match(self):
        self.check_qualifier(
            "reviewed_fmap_as_finite_support_words_as_type_indexed_bitvec",
            {"fmap_as_finite_support": ["locals", "globals", "code"],
             "words_as_type_indexed_bitvec": True},
            {"fmap_as_finite_support": ["locals", "globals", "code"],
             "words_as_type_indexed_bitvec": True},
            {"fmap_as_finite_support": ["locals", "globals", "code"]},
        )

    def test_combined_relation_words_status_must_match(self):
        self.check_qualifier(
            "reviewed_fmap_as_finite_support_relation_words_as_type_indexed_bitvec",
            {"fmap_as_finite_support_relation": ["PanState.globals", "CrepState.code"],
             "words_as_type_indexed_bitvec": True},
            {"fmap_as_finite_support_relation": ["PanState.globals", "CrepState.code"],
             "words_as_type_indexed_bitvec": True},
            {"words_as_type_indexed_bitvec": True},
        )

    def test_word_dimension_as_width_qualifier_must_match(self):
        self.check_qualifier(
            "reviewed_word_dimension_as_width",
            {"word_dimension_as_width": "width"},
            {"word_dimension_as_width": "width"},
            {},
        )

    def test_reals_as_rational_cuts_qualifier_must_match(self):
        self.check_qualifier(
            "reviewed_reals_as_rational_cuts",
            {"reals_as_rational_cuts": True},
            {"reals_as_rational_cuts": True},
            {},
        )

    def test_reals_as_rational_cuts_export_without_manifest_is_rejected(self):
        export = [{**self.export[0], "qualifiers": {"reals_as_rational_cuts": True}}]
        with self.assertRaisesRegex(ValueError, "carries reals_as_rational_cuts"):
            MODULE.check_records(self.manifest, export)

    def test_inherited_reals_assumption_must_match_the_closure_export(self):
        manifest = [{**self.manifest[0], "inherits_reals_as_rational_cuts": True}]
        export = [{**self.export[0], "inherits_reals_as_rational_cuts": True}]
        self.assertEqual(MODULE.check_records(manifest, export), 1)
        with self.assertRaisesRegex(ValueError, "declaration closure gives True"):
            MODULE.check_records(self.manifest, export)
        with self.assertRaisesRegex(ValueError, "declaration closure gives False"):
            MODULE.check_records(manifest, self.export)

    def test_ambiguous_reference_fails_closed(self):
        duplicate = [{**self.export[0], "lean_name": "Other.exampleCorrect"}]
        with self.assertRaisesRegex(ValueError, "found 2"):
            MODULE.check_records(self.manifest, self.export + duplicate)

    def test_missing_export_fails_closed(self):
        with self.assertRaisesRegex(ValueError, "found 0"):
            MODULE.check_records(self.manifest, [])

    def test_inherited_reals_export_field_is_boolean(self):
        record = {**self.export[0], "inherits_reals_as_rational_cuts": "yes"}
        with self.assertRaisesRegex(ValueError, "non-boolean inherits_reals_as_rational_cuts"):
            MODULE.validate_export_record(record, 1)

    def test_valid_export_records(self):
        for qualifiers in (
            {"words_as_type_indexed_bitvec": True},
            {"fmap_as_finite_support": ["locals"]},
            {"fmap_as_finite_support_existentials": ["inl_bag"]},
            {"word_dimension_as_width": "width"},
            {"list_as_array": [], "names_as_string": ["key"], "names_as_string_boundary": []},
        ):
            record = {**self.export[0], "qualifiers": qualifiers}
            with self.subTest(qualifiers=qualifiers):
                self.assertEqual(MODULE.validate_export_record(record, 1), record)

    def test_unknown_qualifier_fails_closed(self):
        with self.assertRaisesRegex(ValueError, "invalid qualifiers"):
            MODULE.validate_export_record(
                {**self.export[0], "qualifiers": {"finite_map": ["locals"]}}, 1
            )

    def test_malformed_export_qualifier_fails_closed(self):
        with self.assertRaisesRegex(ValueError, "malformed qualifier"):
            MODULE.validate_export_record(
                {**self.export[0], "qualifiers": {"names_as_string": "key"}}, 1
            )

    def test_unknown_export_field_fails_closed(self):
        for extra in ("extra", "type_expr", "value_expr"):
            with self.subTest(extra=extra):
                with self.assertRaisesRegex(ValueError, "invalid fields"):
                    MODULE.validate_export_record({**self.export[0], extra: "x"}, 1)

    def test_missing_required_field_fails_closed(self):
        with self.assertRaisesRegex(ValueError, "invalid fields"):
            MODULE.validate_export_record({"lean_name": "n", "hol_path": "p"}, 1)

    def test_exporter_uses_current_lake_build_graph(self):
        result = type("Completed", (), {
            "returncode": 0,
            "stdout": json.dumps(self.export[0]) + "\n",
            "stderr": "",
        })()
        with patch.object(MODULE.subprocess, "run", return_value=result) as run:
            self.assertEqual(MODULE.exported_refs(), self.export)
        self.assertEqual(run.call_args.args[0], [
            "lake", "--quiet", "lean", str(MODULE.EXPORTER),
        ])

    def test_native_export_sees_recent_crep_props_source_declaration(self):
        # This exact declaration was missing from an old saved
        # Flapjack.setup.json after Lake had rebuilt CrepProps from source.
        # Exercise the real Lake path to ensure the fresh declaration is
        # visible and that no local OLean import is missing.
        names = {item["lean_name"] for item in MODULE.exported_refs()}
        self.assertIn(
            "Flapjack.crepAssignedVarsHOL_nestedSeq_storesHOL", names
        )


if __name__ == "__main__":
    unittest.main()
