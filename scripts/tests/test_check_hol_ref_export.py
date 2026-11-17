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

    def test_parameter_observations_require_elaborated_combined_marker(self):
        fields = {"fmap_as_finite_support_parameters": ["code"],
                  "fmap_as_finite_support_result_observations": ["Flapjack.Map.make"]}
        self.check_qualifier(
            "reviewed_fmap_as_finite_support_parameter_observations", fields,
            {**fields, "fmap_as_finite_support_parameter_observations": True}, fields)

    def test_predicate_domain_binders_must_match_export_in_order(self):
        key = "fmap_as_finite_support_parameter_predicate_domain"
        self.check_qualifier(
            "reviewed_fmap_as_finite_support_parameter_predicate_domain",
            {key: ["code1", "rel"]}, {key: ["code1", "rel"]}, {key: ["rel", "code1"]})

    def test_tmc_universal_binder_must_match_export(self):
        fields = {"fmap_as_finite_support_relation": ["BviState.refs"],
                  "fmap_as_finite_support_existentials": ["nextMap", "wrapMap", "workMap"],
                  "fmap_as_finite_support_universals": ["f"]}
        self.check_qualifier("reviewed_fmap_as_finite_support_relation_existentials_universals",
                             fields, fields, {**fields, "fmap_as_finite_support_universals": ["other"]})

    def test_nested_list_qualifier_must_match_both_directions(self):
        self.check_qualifier(
            "reviewed_nested_list_rel_as_mutual",
            {"nested_list_rel_as_mutual": ["FunctionsRel"]},
            {"nested_list_rel_as_mutual": ["FunctionsRel"]},
            {"nested_list_rel_as_mutual": ["Other"]},
        )
        with self.assertRaisesRegex(ValueError, "nested-list relation qualifier"):
            MODULE.check_records(self.manifest, [{**self.export[0], "qualifiers":
                {"nested_list_rel_as_mutual": ["FunctionsRel"]}}])

    def test_combined_nested_and_fmap_match_export(self):
        fields = {"fmap_as_finite_support": ["refs", "code"],
                  "nested_list_rel_as_mutual": ["FunctionsRel"]}
        status = "reviewed_fmap_as_finite_support_nested_list_rel_as_mutual"
        manifest = [{**self.manifest[0], "statement_status": status, **fields}]
        self.assertEqual(MODULE.check_records(manifest, [{**self.export[0], "qualifiers": fields}]), 1)
        for missing in ("fmap_as_finite_support", "nested_list_rel_as_mutual"):
            with self.subTest(missing=missing), self.assertRaises(ValueError):
                MODULE.check_records(manifest, [{**self.export[0], "qualifiers":
                    {key: value for key, value in fields.items() if key != missing}}])
            with self.subTest(unrecorded=missing), self.assertRaises(ValueError):
                MODULE.check_records([{key: value for key, value in manifest[0].items() if key != missing}],
                                     [{**self.export[0], "qualifiers": fields}])

    def test_nested_relation_existential_arrays_match_export(self):
        fields = {"nested_list_rel_as_mutual": ["FunctionsRel"],
                  "fmap_as_finite_support_relation": ["State.refs", "State.code", "sourceRefs"],
                  "fmap_as_finite_support_existentials": ["targetRefs"]}
        status = "reviewed_fmap_as_finite_support_relation_existentials_nested_list_rel_as_mutual"
        manifest = [{**self.manifest[0], "statement_status": status, **fields}]
        self.assertEqual(MODULE.check_records(manifest, [{**self.export[0], "qualifiers": fields}]), 1)
        for field in fields:
            with self.subTest(field=field), self.assertRaises(ValueError):
                MODULE.check_records(manifest, [{**self.export[0], "qualifiers": {**fields, field: []}}])

    def test_nested_audit_requires_witness_comparison_and_ordered_marker(self):
        source = MODULE.NESTED_AUDIT.read_text(encoding="utf-8")
        MODULE.validate_nested_audit_source(source)
        for missing in ("Lean.Meta.isDefEq witness.type expectedWitness.value",
                        "Lean.collectAxioms ``functionsRel_iff",
                        "private def expectedFunctionsConsRule"):
            with self.subTest(missing=missing), self.assertRaises(ValueError):
                MODULE.validate_nested_audit_source(source.replace(missing, "", 1))
        with self.assertRaises(ValueError):
            MODULE.validate_nested_audit_source(source.replace(
                "Lean.collectAxioms ``functionsRel_iff",
                "/- Lean.collectAxioms ``functionsRel_iff -/", 1))
        marker = "theorem nestedRelationAudit_passed : True := trivial"
        with self.assertRaises(ValueError):
            MODULE.validate_nested_audit_source(marker + "\n" + source.replace(marker, "", 1))

    def test_tuple_map_qualifier_must_match_in_both_directions(self):
        status = "reviewed_fmap_as_finite_support_tuple_words_as_type_indexed_bitvec"
        fields = {"fmap_as_finite_support_tuple": ["component_2", "component_3"],
                  "words_as_type_indexed_bitvec": True}
        self.check_qualifier(status, fields, fields,
                             {"fmap_as_finite_support_tuple": ["component_2"],
                              "words_as_type_indexed_bitvec": True})
        with self.assertRaisesRegex(ValueError, "tuple-map qualifier"):
            MODULE.check_records(self.manifest, [{**self.export[0], "qualifiers": fields}])

    def test_unification_tuple_position_must_match_export(self):
        fields = {"fmap_as_finite_support_tuple": ["component_1"]}
        self.check_qualifier("reviewed_fmap_as_finite_support_tuple", fields, fields,
                             {"fmap_as_finite_support_tuple": ["component_2"]})
        with self.assertRaisesRegex(ValueError, "tuple-map qualifier"):
            MODULE.check_records(self.manifest, [{**self.export[0], "qualifiers": fields}])

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

    def test_generalisation_map_metadata_is_exact_and_bidirectional(self):
        key = "fmap_as_finite_support_parameter_tuple_result"
        fields = {key: ["subst", "component_2"]}
        manifest = [{**self.manifest[0], "lean_name": "generaliseMap",
                     "lean_path": "Flapjack/Compiler/Inference/Infer/Generalise.lean",
                     "hol_path": "cakeml/compiler/inference/inferScript.sml",
                     "hol_name": "generalise_def",
                     "statement_status": "reviewed_" + key, **fields}]
        exported = [{"lean_name": "Flapjack.Compiler.Inference.Infer.Generalise.generaliseMap",
                     "hol_path": manifest[0]["hol_path"], "hol_name": "generalise_def",
                     "qualifiers": fields}]
        self.assertEqual(MODULE.check_records(manifest, exported), 1)
        for qualifier in ({}, {key: ["subst", "component_1"]}):
            with self.subTest(qualifier=qualifier), self.assertRaises(ValueError):
                MODULE.check_records(manifest, [{**exported[0], "qualifiers": qualifier}])
        with self.assertRaises(ValueError):
            MODULE.check_records([{k: v for k, v in manifest[0].items() if k != key}], exported)
        with self.assertRaises(ValueError):
            MODULE.check_records([{k: v for k, v in manifest[0].items() if k != key}],
                                 [{**exported[0], "qualifiers": {}}])
        with self.assertRaises(ValueError):
            MODULE.check_records([{**{k: v for k, v in manifest[0].items() if k != key},
                                   "statement_status": "reviewed_exact"}],
                                 [{**exported[0], "qualifiers": {}}])
        with self.assertRaises(ValueError):
            MODULE.check_records([{**manifest[0], "statement_status": "reviewed_exact"}], exported)
        with self.assertRaises(ValueError):
            MODULE.check_records(manifest, [{**exported[0], "qualifiers":
                {**fields, "words_as_type_indexed_bitvec": True}}])
        with self.assertRaises(ValueError):
            MODULE.check_records(manifest, [{**exported[0],
                "lean_name": "Flapjack.Unrelated.generaliseMap"}])
        with self.assertRaises(ValueError):
            MODULE.check_records([{**manifest[0], "lean_path": "Flapjack/Unrelated.lean"}], exported)
        list_manifest = [{**manifest[0], "lean_name": "generaliseListMap"}]
        list_exported = [{**exported[0], "lean_name":
            "Flapjack.Compiler.Inference.Infer.Generalise.generaliseListMap"}]
        self.assertEqual(MODULE.check_records(list_manifest, list_exported), 1)
        with self.assertRaises(ValueError):
            MODULE.check_records(list_manifest, [{**list_exported[0], "qualifiers": {}}])
        self.assertEqual(MODULE.validate_export_record(exported[0], 1), exported[0])

    def test_generalisation_length_metadata_and_producer_are_exact(self):
        key = "fmap_as_finite_support_parameter_tuple_observations"
        producer = "Flapjack.Compiler.Inference.Infer.Generalise.generaliseListMap"
        fields = {key: ["subst", "out", producer, "component_2"]}
        row = {"lean_path": "Flapjack/Compiler/Inference/InferProps/Generalise.lean",
               "lean_name": "generaliseListLength",
               "hol_path": "cakeml/compiler/inference/inferPropsScript.sml",
               "hol_name": "generalise_list_length", "statement_status": "reviewed_" + key, **fields}
        producer_row = {"lean_path": "Flapjack/Compiler/Inference/Infer/Generalise.lean",
                        "lean_name": "generaliseListMap",
                        "hol_path": "cakeml/compiler/inference/inferScript.sml",
                        "hol_name": "generalise_def",
                        "statement_status": "reviewed_fmap_as_finite_support_parameter_tuple_result",
                        "fmap_as_finite_support_parameter_tuple_result": ["subst", "component_2"]}
        exported = [{"lean_name": "Flapjack.Compiler.Inference.InferProps.Generalise.generaliseListLength",
                     "hol_path": row["hol_path"], "hol_name": row["hol_name"], "qualifiers": fields},
                    {"lean_name": producer, "hol_path": producer_row["hol_path"],
                     "hol_name": producer_row["hol_name"], "qualifiers": {
                         "fmap_as_finite_support_parameter_tuple_result": ["subst", "component_2"]}}]
        self.assertEqual(MODULE.check_records([row, producer_row], exported), 2)
        self.assertEqual(MODULE.validate_export_record(exported[0], 1), exported[0])
        for changed in ({**row, "statement_status": "reviewed_exact"},
                        {**row, "lean_path": "Flapjack/Other.lean"},
                        {**row, "hol_line": 10},
                        {**row, key: ["out", "subst", producer, "component_2"]}):
            with self.subTest(row=changed), self.assertRaises(ValueError):
                MODULE.check_records([changed, producer_row], exported)
        for rows in ([row], [row, producer_row, producer_row],
                     [row, {**producer_row, "statement_status": "reviewed_exact"}],
                     [row, {**producer_row, "words_as_type_indexed_bitvec": True}]):
            with self.subTest(rows=rows), self.assertRaises(ValueError):
                MODULE.check_records(rows, exported)
        for changes in ({"qualifiers": {}}, {"lean_name": "Flapjack.Other.generaliseListLength"},
                        {"qualifiers": {**fields, "words_as_type_indexed_bitvec": True}}):
            with self.subTest(changes=changes), self.assertRaises(ValueError):
                MODULE.check_records([row, producer_row], [{**exported[0], **changes}, exported[1]])

    def test_infer_subst_submap_qualifier_is_exact_and_requires_producer(self):
        key = "fmap_as_finite_support_conjunct_universals"
        fields = {key: ["type_s1", "type_s2", "list_s1", "list_s2"]}
        row = {"lean_path": "Flapjack/Compiler/Inference/InferProps/Substitution.lean",
               "lean_name": "inferSubstSubmap", "hol_path": "cakeml/compiler/inference/inferPropsScript.sml",
               "hol_name": "infer_subst_submap", "statement_status": "reviewed_" + key, **fields}
        producer = {"lean_path": "Flapjack/Compiler/Inference/Infer/Substitution.lean",
                    "lean_name": "inferSubst", "hol_path": "cakeml/compiler/inference/inferScript.sml",
                    "hol_name": "infer_subst_def", "statement_status": "reviewed_fmap_as_finite_support_parameters",
                    "fmap_as_finite_support_parameters": ["subst"]}
        vars_row = {"lean_path": "Flapjack/Compiler/Inference/Unify/Substitution.lean", "lean_name": "tVars",
                    "hol_path": "cakeml/compiler/inference/unifyScript.sml", "hol_name": "t_vars_def",
                    "statement_status": "reviewed_exact"}
        exported = [{"lean_name": "Flapjack.Compiler.Inference.InferProps.Substitution.inferSubstSubmap",
                     "hol_path": row["hol_path"], "hol_name": row["hol_name"], "qualifiers": fields},
                    {"lean_name": "Flapjack.Compiler.Inference.Infer.Substitution.inferSubst",
                     "hol_path": producer["hol_path"], "hol_name": producer["hol_name"],
                     "qualifiers": {"fmap_as_finite_support_parameters": ["subst"]}},
                    {"lean_name": "Flapjack.Compiler.Inference.Unify.tVars", "hol_path": vars_row["hol_path"],
                     "hol_name": vars_row["hol_name"], "qualifiers": {}}]
        self.assertEqual(MODULE.check_records([row, producer, vars_row], exported), 3)
        self.assertEqual(MODULE.validate_export_record(exported[0], 1), exported[0])
        for changed in ({**row, "statement_status": "reviewed_exact"},
                        {**row, "lean_path": "Flapjack/Other.lean"}, {**row, "hol_line": 168},
                        {**row, key: ["type_s1", "type_s2", "type_s1", "type_s2"]}):
            with self.subTest(row=changed), self.assertRaises(ValueError):
                MODULE.check_records([changed, producer, vars_row], exported)
        for rows in ([row, vars_row], [row, producer, producer, vars_row], [row, producer],
                     [row, producer, {**vars_row, "statement_status": "pending_statement_review"}],
                     [row, {**producer, "statement_status": "reviewed_exact"}, vars_row],
                     [row, {**producer, "words_as_type_indexed_bitvec": True}, vars_row]):
            with self.subTest(rows=rows), self.assertRaises(ValueError):
                MODULE.check_records(rows, exported)
        for changes in ({"qualifiers": {}}, {"lean_name": "Flapjack.Other.inferSubstSubmap"},
                        {"qualifiers": {**fields, "words_as_type_indexed_bitvec": True}}):
            with self.subTest(changes=changes), self.assertRaises(ValueError):
                MODULE.check_records([row, producer, vars_row], [{**exported[0], **changes}, *exported[1:]])

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
        self.assertEqual(run.call_count, 8)
        for call in run.call_args_list:
            self.assertEqual(call.args[0][:3], ["lake", "--quiet", "lean"])
            self.assertTrue(call.args[0][3].endswith(".lean"))

    def test_batches_cover_umbrella_and_extra_imports(self):
        umbrella = "import Flapjack.A\nimport Flapjack.B\n"
        exporter = ("import Flapjack\nimport Flapjack.Test.NestedRelationAudit\n"
                    "import Flapjack.HolRef.GeneraliseLengthAudit\n"
                    "import Flapjack.HolRef.InferSubstSubmapAudit\n"
                    "import Flapjack.C\nopen Lean Elab Command Flapjack\n#emit_hol_ref_export\n")
        batches = MODULE.export_batches(umbrella, exporter, count=2)
        self.assertEqual(len(batches), 2)
        for name in ("Flapjack.A", "Flapjack.B", "Flapjack.C"):
            self.assertEqual(sum(f"import {name}\n" in batch for batch in batches), 1)
        self.assertTrue(all("import Flapjack.Test.NestedRelationAudit\n" in batch for batch in batches))
        self.assertTrue(all("import Flapjack.HolRef.GeneraliseLengthAudit\n" in batch for batch in batches))
        self.assertTrue(all("import Flapjack.HolRef.InferSubstSubmapAudit\n" in batch for batch in batches))

    def test_batches_reject_non_import_umbrella(self):
        exporter = ("import Flapjack\nimport Flapjack.Test.NestedRelationAudit\n"
                    "import Flapjack.HolRef.GeneraliseLengthAudit\n"
                    "import Flapjack.HolRef.InferSubstSubmapAudit\n"
                    "open Lean Elab Command Flapjack\n")
        with self.assertRaisesRegex(ValueError, "import-only"):
            MODULE.export_batches("import Flapjack.A\ndef extra := 1\n", exporter)

    def test_batches_require_generalisation_length_audit(self):
        exporter = ("import Flapjack\nimport Flapjack.Test.NestedRelationAudit\n"
                    "open Lean Elab Command Flapjack\n")
        with self.assertRaisesRegex(ValueError, "shared audit modules"):
            MODULE.export_batches("import Flapjack.A\n", exporter)

    def test_batches_require_inference_submap_audit(self):
        exporter = ("import Flapjack\nimport Flapjack.Test.NestedRelationAudit\n"
                    "import Flapjack.HolRef.GeneraliseLengthAudit\n"
                    "open Lean Elab Command Flapjack\n")
        with self.assertRaisesRegex(ValueError, "shared audit modules"):
            MODULE.export_batches("import Flapjack.A\n", exporter)

    def test_batches_reject_disagreeing_records(self):
        first = self.export[0]
        second = {**first, "hol_name": "different"}
        results = [type("Completed", (), {"returncode": 0, "stderr": "", "stdout": json.dumps(r)})()
                   for r in (first, second)]
        with patch.object(MODULE.subprocess, "run", side_effect=results):
            with self.assertRaisesRegex(ValueError, "disagree"):
                MODULE.exported_refs()

    def test_batches_reject_duplicate_record_within_batch(self):
        line = json.dumps(self.export[0])
        result = type("Completed", (), {"returncode": 0, "stderr": "", "stdout": line + "\n" + line})()
        with patch.object(MODULE.subprocess, "run", return_value=result):
            with self.assertRaisesRegex(ValueError, "duplicate declaration"):
                MODULE.exported_refs()


if __name__ == "__main__":
    unittest.main()
