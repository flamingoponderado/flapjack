"""Regression checks for the HOL-reference scanner."""

import os
import runpy
import tempfile
import unittest
from pathlib import Path


CHECKER = runpy.run_path(
    str(Path(__file__).resolve().parents[1] / "check-hol-refs.py")
)
SITES = CHECKER["hol_attribute_sites"]
REF_ERROR = CHECKER["hol_ref_error"]


class ExternalHolSourcesTest(unittest.TestCase):
    def fixture(self, root):
        import hashlib
        import json
        base = root / "hol4"
        (base / "src/finite_maps").mkdir(parents=True)
        (base / "COPYRIGHT").write_text("retained license")
        (base / "src/finite_maps/sptreeScript.sml").write_text("Theorem domain_union: T Proof simp[] QED")
        lock = {"repository": CHECKER["EXTERNAL_HOL_REPOSITORY"], "commit": "a" * 40,
                "files": {p: hashlib.sha256((base / p).read_bytes()).hexdigest()
                          for p in ["COPYRIGHT", "src/finite_maps/sptreeScript.sml"]}}
        (base / "SOURCES.json").write_text(json.dumps(lock))

    def test_repository_snapshot_pin(self):
        self.assertIsNone(CHECKER["hol_source_error"](CHECKER["ROOT"], CHECKER["EXTERNAL_HOL_PATH"]))

    def test_upstream_identity_rejected(self):
        import json
        for field, value in [("commit", "not-a-commit"), ("repository", "https://example.com/other")]:
            with self.subTest(field=field), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                self.fixture(root)
                manifest = root / "hol4/SOURCES.json"
                lock = json.loads(manifest.read_text())
                lock[field] = value
                manifest.write_text(json.dumps(lock))
                self.assertIsNotNone(CHECKER["hol_source_error"](root, CHECKER["EXTERNAL_HOL_PATH"]))

    def test_valid_pin(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self.fixture(root)
            self.assertIsNone(CHECKER["hol_source_error"](root, CHECKER["EXTERNAL_HOL_PATH"]))

    def test_source_and_license_drift_rejected(self):
        for relative in ["COPYRIGHT", "src/finite_maps/sptreeScript.sml"]:
            with self.subTest(relative=relative), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                self.fixture(root)
                (root / "hol4" / relative).write_text("altered")
                self.assertIn("mismatch", CHECKER["hol_source_error"](root, CHECKER["EXTERNAL_HOL_PATH"]))

    def test_unpinned_and_traversal_rejected(self):
        for path in ["hol4/otherScript.sml", "/tmp/source.sml", "cakeml/../source.sml",
                     "cakeml//source.sml", "hol4/src/finite_maps/./sptreeScript.sml"]:
            with self.subTest(path=path):
                self.assertIsNotNone(CHECKER["hol_source_error"](Path("/tmp"), path))

    def test_missing_and_malformed_manifest_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self.assertIsNotNone(CHECKER["hol_source_error"](root, CHECKER["EXTERNAL_HOL_PATH"]))
            self.fixture(root)
            (root / "hol4/SOURCES.json").write_text("[]")
            self.assertIsNotNone(CHECKER["hol_source_error"](root, CHECKER["EXTERNAL_HOL_PATH"]))

    def test_symlink_rejected_even_with_matching_bytes(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self.fixture(root)
            source = root / CHECKER["EXTERNAL_HOL_PATH"]
            source.rename(root / "source-copy")
            source.symlink_to(root / "source-copy")
            self.assertIsNotNone(CHECKER["hol_source_error"](root, CHECKER["EXTERNAL_HOL_PATH"]))


class HolAttributeSitesTest(unittest.TestCase):
    def test_single_line(self):
        self.assertEqual(
            list(SITES(['@[hol "cakeml/pancake/pan_globalsScript.sml" "compile_top_def"]'])),
            [(1, "cakeml/pancake/pan_globalsScript.sml", "compile_top_def", None, (), (), (), (), False, (), False, False, ())],
        )

    def test_multiline(self):
        self.assertEqual(
            list(SITES([
                '@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml"',
                '  "compile_top_shape_wf"]',
                'theorem compileTopShapeWf : True := trivial',
            ])),
            [(1, "cakeml/pancake/proofs/pan_globalsProofScript.sml",
              "compile_top_shape_wf", None, (), (), (), (), False, (), False, False, ())],
        )

    def test_comments_do_not_count(self):
        self.assertEqual(
            list(SITES([
                '/- @[hol "cakeml/pancake/pan_globalsScript.sml" "bad"] -/',
                '-- @[hol "cakeml/pancake/pan_globalsScript.sml" "bad"]',
                '@[hol "cakeml/pancake/pan_globalsScript.sml" "compile_top_def"]',
            ])),
            [(3, "cakeml/pancake/pan_globalsScript.sml", "compile_top_def", None, (), (), (), (), False, (), False, False, ())],
        )

    def test_source_line(self):
        self.assertEqual(
            list(SITES(['@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml"',
                        '  "locals_rel_wf_shape" 2345]'])),
            [(1, "cakeml/pancake/proofs/pan_to_crepProofScript.sml",
              "locals_rel_wf_shape", 2345, (), (), (), (), False, (), False, False, ())],
        )

    def test_list_as_array_fields(self):
        self.assertEqual(
            list(SITES([
                '@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml"',
                '  "dec_deg_def" (list_as_array := [degrees, moves])]'
            ])),
            [(1, "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml",
              "dec_deg_def", None, ("degrees", "moves"), (), (), (), False, (), False, False, ())],
        )

    def test_names_as_string_and_boundary_qualifiers(self):
        self.assertEqual(
            list(SITES([
                '@[hol "cakeml/pancake/panLangScript.sml" "varname"',
                '  (names_as_string := [name, generated])',
                '  (names_as_string_boundary := [generated])]',
            ])),
            [(1, "cakeml/pancake/panLangScript.sml", "varname", None,
              (), ("name", "generated"), ("generated",), (), False, (), False, False, ())],
        )

    def test_word_dimension_as_width_qualifier(self):
        sites = list(SITES([
            '@[hol "cakeml/compiler/backend/semantics/wordSemScript.sml" "MustTerminate_limit_def"',
            '  (word_dimension_as_width := width)]',
        ], include_fmap_existentials=True, include_word_dimension_width=True))
        self.assertEqual(sites[0][-1], "width")
        self.assertEqual(sites[0][-2], ())

    def test_nested_fmap_function_qualifier(self):
        sites = list(SITES([
            '@[hol "cakeml/compiler/backend/semantics/wordSemScript.sml" "gc_fun_type"',
            '  (fmap_as_finite_support_function := [argument_4, result_3])]',
        ], include_fmap_function=True))
        self.assertEqual(sites[0][-1], ("argument_4", "result_3"))


class FmapFunctionQualifierTest(unittest.TestCase):
    CHECK = staticmethod(CHECKER["fmap_as_finite_support_function_errors"])
    POSITIONS = ("argument_4", "result_3")
    SOURCE = """/-- HOL gc function type. -/
abbrev WordSemGcFun (width : Nat) : Type :=
  (List Nat × (Nat → Nat) × (Nat → Bool) × HolFiniteMapExact Nat Nat) →
    Option (List Nat × (Nat → Nat) × HolFiniteMapExact Nat Nat)
"""
    MODULE = SOURCE + """
theorem holFmapAsFiniteSupportWitness : True := by trivial
"""

    def test_accepts_exact_argument_and_result_product_slots(self):
        self.assertEqual(
            self.CHECK(self.MODULE.splitlines(), self.SOURCE,
                       "WordSemGcFun", self.POSITIONS),
            [],
        )

    def test_rejects_missing_argument_or_result_position(self):
        errors = self.CHECK(self.MODULE.splitlines(), self.SOURCE,
                            "WordSemGcFun", ("argument_4",))
        self.assertTrue(any("requires both argument_N and result_N" in error
                            for error in errors))

    def test_rejects_wrong_slot_and_raw_function_map(self):
        wrong_slot = self.CHECK(self.MODULE.splitlines(), self.SOURCE,
                                "WordSemGcFun", ("argument_3", "result_3"))
        self.assertTrue(any("argument_3 must use HolFiniteMapExact" in error
                            for error in wrong_slot))
        raw = self.SOURCE.replace("HolFiniteMapExact Nat Nat", "Nat → Option Nat")
        raw_errors = self.CHECK((self.MODULE.replace(self.SOURCE, raw)).splitlines(),
                                raw, "WordSemGcFun", self.POSITIONS)
        self.assertTrue(any("must use HolFiniteMapExact" in error
                            for error in raw_errors))

    def test_requires_same_map_type_and_canonical_witness(self):
        changed = self.SOURCE.replace(
            "HolFiniteMapExact Nat Nat)", "HolFiniteMapExact Nat Bool)", 1
        )
        changed_module = self.MODULE.replace(self.SOURCE, changed)
        errors = self.CHECK(changed_module.splitlines(), changed,
                            "WordSemGcFun", self.POSITIONS)
        self.assertTrue(any("same exact type" in error for error in errors))
        witness_errors = self.CHECK(self.SOURCE.splitlines(), self.SOURCE,
                                    "WordSemGcFun", self.POSITIONS)
        self.assertTrue(any("requires same-module canonical" in error
                            for error in witness_errors))

    def test_word_qualifier_checks_type_alias_body(self):
        check = CHECKER["words_as_type_indexed_bitvec_errors"]
        alias = """abbrev Words (width : Nat) [NeZero width] : Type :=
  BitVec width → BitVec width
"""
        self.assertEqual(check(alias, "Words"), [])
        missing_positive = alias.replace(" [NeZero width]", "")
        self.assertTrue(any("[NeZero width]" in error
                            for error in check(missing_positive, "Words")))

    def test_word_dimension_as_width_requires_its_nat_and_nezero_binders(self):
        check = CHECKER["word_dimension_as_width_errors"]
        valid = "def example (width : Nat) [NeZero width] : Nat := width"
        self.assertEqual(check(valid, "example", "width"), [])
        missing_nezero = "def example (width : Nat) : Nat := width"
        self.assertTrue(any("retain its own `[NeZero width]`" in error
                            for error in check(missing_nezero, "example", "width")))
        wrong_binder = "def example (n : Nat) [NeZero n] : Nat := n"
        self.assertTrue(any("explicit `(width : Nat)` binder" in error
                            for error in check(wrong_binder, "example", "width")))
        word_carrier = "def example (width : Nat) [NeZero width] : BitVec width := 0"
        self.assertTrue(any("word-free signatures" in error
                            for error in check(word_carrier, "example", "width")))

    def test_reals_as_rational_cuts_site_flag(self):
        sites = list(SITES([
            '@[hol "cakeml/semantics/fpSemScript.sml" "fp_uop_comp_def"',
            '  (reals_as_rational_cuts)]',
        ], include_fmap_existentials=True, include_word_dimension_width=True,
            include_fmap_function=True, include_reals_as_rational_cuts=True))
        self.assertTrue(sites[0][-1])
        plain = list(SITES([
            '@[hol "cakeml/semantics/fpSemScript.sml" "fp_uop_comp_def"]',
        ], include_reals_as_rational_cuts=True))
        self.assertFalse(plain[0][-1])

    def test_reals_as_rational_cuts_required_exactly_for_rendering_users(self):
        check = CHECKER["reals_as_rational_cuts_errors"]
        names = {"holFp64Sqrt", "holFp64Add"}
        user = "noncomputable def uop : BitVec 64 -> BitVec 64\n  | x => holFp64Sqrt .roundTiesToEven x"
        self.assertEqual(check(user, True, names), [])
        self.assertTrue(any("must carry (reals_as_rational_cuts)" in error
                            for error in check(user, False, names)))
        dependent = "def evaluate (s : State) : State := match inst s with | _ => s"
        self.assertEqual(check(dependent, False, names), [])
        self.assertTrue(any("dependents inherit" in error
                            for error in check(dependent, True, names)))
        comment_only = "def f : Nat := 0 -- see holFp64Sqrt"
        self.assertEqual(check(comment_only, False, names), [])

    def test_reals_as_rational_cuts_ignores_following_declarations(self):
        check = CHECKER["reals_as_rational_cuts_errors"]
        names = {"holFp64Equal"}
        datatype = """inductive FpCmp where
  | less | equal
  deriving DecidableEq

/-- next -/
@[hol "cakeml/semantics/fpSemScript.sml" "fp_cmp_comp_def"]
noncomputable def cmp : FpCmp -> Bool
  | .equal => holFp64Equal 0 0
"""
        self.assertEqual(check(datatype, False, names), [])

    def test_reals_rendering_names_cover_machine_ieee(self):
        names = CHECKER["reals_rendering_names"](CHECKER["ROOT"])
        self.assertIn("holFp64Sqrt", names)
        self.assertIn("holFp64Add", names)

    def test_fmap_as_finite_support_fields(self):
        self.assertEqual(
            list(SITES([
                '@[hol "cakeml/pancake/semantics/panSemScript.sml" "set_var_def"',
                '  (fmap_as_finite_support := [locals, globals])]'
            ])),
            [(1, "cakeml/pancake/semantics/panSemScript.sml",
              "set_var_def", None, (), (), (), ("locals", "globals"), False, (), False, False, ())],
        )

    def test_fmap_as_finite_support_result_qualifier(self):
        self.assertEqual(
            list(SITES([
                '@[hol "cakeml/pancake/pan_to_crepScript.sml" "get_eids_from_decls_def"',
                '  (fmap_as_finite_support_result)]'
            ])),
            [(1, "cakeml/pancake/pan_to_crepScript.sml",
              "get_eids_from_decls_def", None, (), (), (), (), True, (), False, False, ())],
        )

    def test_fmap_as_finite_support_parameters_qualifier(self):
        self.assertEqual(
            list(SITES([
                '@[hol "cakeml/pancake/semantics/panPropsScript.sml" "FEVERY_res_var_FLOOKUP"',
                '  (fmap_as_finite_support_parameters := [fm, fm2])]',
            ])),
            [(1, "cakeml/pancake/semantics/panPropsScript.sml",
              "FEVERY_res_var_FLOOKUP", None, (), (), (), (), False, (), False,
              False, ("fm", "fm2"))],
        )

    def test_fmap_as_finite_support_existentials_qualifier(self):
        self.assertEqual(
            list(SITES([
                '@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml"',
                '  "code_inl_rel_def"',
                '  (fmap_as_finite_support_existentials := [inl_bag])]',
            ], include_fmap_existentials=True)),
            [(1, "cakeml/pancake/proofs/crep_inlineProofScript.sml",
              "code_inl_rel_def", None, (), (), (), (), False, (), False,
              False, (), ("inl_bag",))],
        )

    def test_fmap_existential_requires_explicit_exact_carrier_and_witness(self):
        lines = [
            "theorem holFmapAsFiniteSupportExistentialWitness_eval_bag",
            "    (bag : HolFiniteMapExact Nat Nat) :",
            "    (Broad.ofBroad (Broad.toBroad bag)).lookup = bag.lookup ∧",
            "      (Broad.ofBroad (Broad.toBroad bag)).finiteSupport = bag.finiteSupport ∧",
            "      Broad.ofBroad (Broad.toBroad bag) = bag := by",
            "  cases bag; rfl",
        ]
        declaration = "theorem eval : ∃ bag : HolFiniteMapExact Nat Nat, P bag"
        self.assertEqual(
            CHECKER["fmap_as_finite_support_existentials_errors"](
                lines, "Example.lean", declaration, "eval", ("bag",)
            ),
            [],
        )

    def test_fmap_existential_rejects_raw_map_missing_binder_and_vacuous_witness(self):
        errors = CHECKER["fmap_as_finite_support_existentials_errors"](
            [], "Example.lean", "theorem eval : ∃ bag : Nat → Option Nat, P bag",
            "eval", ("bag",),
        )
        self.assertTrue(any("must be an existential typed HolFiniteMapExact" in e for e in errors))
        lines = [
            "theorem holFmapAsFiniteSupportExistentialWitness_eval_bag",
            "    (bag : HolFiniteMapExact Nat Nat) :",
            "    ¬ (mapofBroad = maptoBroadlookup ∧ bag = bag) := by",
            "  intro h; exact absurd h (by decide)",
        ]
        errors = CHECKER["fmap_as_finite_support_existentials_errors"](
            lines, "Example.lean",
            "theorem eval : ∃ bag : HolFiniteMapExact Nat Nat, P bag",
            "eval", ("bag",),
        )
        self.assertTrue(any("canonical lookup/finiteSupport" in e for e in errors))

    def test_fmap_existential_rejects_witness_assumption_and_scans_definition_body(self):
        lines = [
            "theorem holFmapAsFiniteSupportExistentialWitness_eval_bag",
            "    (bag : HolFiniteMapExact Nat Nat)",
            "    (h : (Broad.ofBroad (Broad.toBroad bag)).lookup = bag.lookup) :",
            "    (Broad.ofBroad (Broad.toBroad bag)).lookup = bag.lookup ∧",
            "      (Broad.ofBroad (Broad.toBroad bag)).finiteSupport = bag.finiteSupport ∧",
            "      Broad.ofBroad (Broad.toBroad bag) = bag := by",
            "  exact ⟨h, rfl, rfl⟩",
        ]
        declaration = "def eval (bag : HolFiniteMapExact Nat Nat) : Prop :=\n  ∃ bag : HolFiniteMapExact Nat Nat, P bag"
        errors = CHECKER["fmap_as_finite_support_existentials_errors"](
            lines, "Example.lean", declaration, "eval", ("bag",)
        )
        self.assertTrue(any("canonical lookup/finiteSupport" in e for e in errors))

    def test_fmap_as_finite_support_parameters_requires_direct_exact_binders_and_witnesses(self):
        lines = [
            "theorem holFmapAsFiniteSupportParamWitness_eval_fm",
            "    (fm : HolFiniteMapExact Nat Nat) :",
            "    mapofBroad (maptoBroadlookup fm) fm.finiteSupport = fm := by",
            "  cases fm; rfl",
            "theorem holFmapAsFiniteSupportParamWitness_eval_fm2",
            "    (fm2 : HolFiniteMapExact Nat Nat) :",
            "    mapofBroad (maptoBroadlookup fm2) fm2.finiteSupport = fm2 := by",
            "  cases fm2; rfl",
        ]
        declaration = (
            "theorem eval (fm : HolFiniteMapExact Nat Nat) "
            "(fm2 : HolFiniteMapExact Nat Nat) : Prop"
        )
        self.assertEqual(
            CHECKER["fmap_as_finite_support_parameters_errors"](
                lines, "Example.lean", declaration, "eval", ("fm", "fm2")
            ),
            [],
        )

    def test_fmap_as_finite_support_parameters_rejects_raw_or_missing_binder(self):
        errors = CHECKER["fmap_as_finite_support_parameters_errors"](
            [], "Example.lean", "theorem eval (fm : Nat → Option Nat) : Prop",
            "eval", ("fm",),
        )
        self.assertTrue(any("must be an input parameter typed HolFiniteMapExact" in e for e in errors))

    def test_fmap_as_finite_support_parameters_rejects_vacuous_witness(self):
        lines = [
            "theorem holFmapAsFiniteSupportParamWitness_eval_fm",
            "    (fm : HolFiniteMapExact Nat Nat) :",
            "    ¬ (ofBroad = toBroad ∧ lookup = finiteSupport ∧ fm = fm) := by",
            "  intro h; exact absurd h (by decide)",
        ]
        declaration = "theorem eval (fm : HolFiniteMapExact Nat Nat) : Prop"
        errors = CHECKER["fmap_as_finite_support_parameters_errors"](
            lines, "Example.lean", declaration, "eval", ("fm",)
        )
        self.assertTrue(
            any("canonical lookup/finiteSupport" in e for e in errors)
        )

    def test_fmap_as_finite_support_relation_qualifier(self):
        self.assertEqual(
            list(SITES([
                '@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "state_rel_def"',
                '  (fmap_as_finite_support_relation := [PanSemStateFiniteExact.globals, CrepSemHOLState.locals])]'
            ])),
            [(1, "cakeml/pancake/proofs/pan_to_crepProofScript.sml",
              "state_rel_def", None, (), (), (), (), False,
              (("PanSemStateFiniteExact", "globals"), ("CrepSemHOLState", "locals")), False, False, ())],
        )

    def test_fmap_as_finite_support_relation_accepts_two_carriers(self):
        lines = [
            "structure Source where",
            "  globals : HolFiniteMapExact MlS (ValueHOL width)",
            "",
            "structure Target where",
            "  locals : HolFiniteMapExact Nat (HolWordLab width)",
            "",
            "theorem holFmapAsFiniteSupportRelationWitness_Source :",
            "    Source.toBroad (Source.ofBroad s) = s := rfl",
            "",
            "theorem holFmapAsFiniteSupportRelationWitness_Target :",
            "    Target.toBroad (Target.ofBroad t) = t := rfl",
        ]
        errors = CHECKER["fmap_as_finite_support_relation_errors"](
            lines,
            (("Source", "globals"), ("Target", "locals")),
            "Example.lean",
            "def stateRel (source : Source) (target : Target) : Prop",
        )
        self.assertEqual(errors, [])

    def test_fmap_as_finite_support_relation_rejects_raw_option_map(self):
        lines = [
            "structure Source where",
            "  globals : MlS \u2192 Option (ValueHOL width)",
            "",
            "theorem holFmapAsFiniteSupportRelationWitness_Source :",
            "    Source.toBroad (Source.ofBroad s) = s := rfl",
        ]
        errors = CHECKER["fmap_as_finite_support_relation_errors"](
            lines, (("Source", "globals"),), "Example.lean",
            "def stateRel (source : Source) : Prop",
        )
        self.assertTrue(any("HolFiniteMapExact" in e for e in errors))

    def test_fmap_as_finite_support_relation_requires_per_carrier_witness(self):
        lines = [
            "structure Source where",
            "  globals : HolFiniteMapExact MlS (ValueHOL width)",
        ]
        errors = CHECKER["fmap_as_finite_support_relation_errors"](
            lines, (("Source", "globals"),), "Example.lean",
            "def stateRel (source : Source) : Prop",
        )
        self.assertTrue(
            any("holFmapAsFiniteSupportRelationWitness_Source" in e for e in errors)
        )

    def test_fmap_as_finite_support_relation_requires_carrier_in_declaration(self):
        lines = [
            "structure Source where",
            "  globals : HolFiniteMapExact MlS (ValueHOL width)",
            "",
            "theorem holFmapAsFiniteSupportRelationWitness_Source :",
            "    Source.toBroad (Source.ofBroad s) = s := rfl",
        ]
        errors = CHECKER["fmap_as_finite_support_relation_errors"](
            lines, (("Source", "globals"),), "Example.lean",
            "def stateRel (a : Type) : Prop",
        )
        self.assertTrue(any("not named in the tagged declaration" in e for e in errors))

    def test_fmap_as_finite_support_relation_rejects_unknown_carrier(self):
        lines = ["def stateRel : Prop := True"]
        errors = CHECKER["fmap_as_finite_support_relation_errors"](
            lines, (("Nope", "globals"),), "Example.lean", "def stateRel : Prop",
        )
        self.assertTrue(any("not a structure" in e for e in errors))

    def test_fmap_as_finite_support_relation_rejects_duplicate_entries(self):
        lines = [
            "structure Source where",
            "  globals : HolFiniteMapExact MlS (ValueHOL width)",
            "",
            "theorem holFmapAsFiniteSupportRelationWitness_Source :",
            "    Source.toBroad (Source.ofBroad s) = s := rfl",
        ]
        errors = CHECKER["fmap_as_finite_support_relation_errors"](
            lines, (("Source", "globals"), ("Source", "globals")), "Example.lean",
            "def stateRel (source : Source) : Prop",
        )
        self.assertTrue(any("distinct" in e for e in errors))

    def test_fmap_as_finite_support_relation_accepts_bare_parameters(self):
        lines = [
            "structure Ctxt where",
            "  vars : HolFiniteMapExact MlS (ShapeHOL \u00d7 List Nat)",
            "",
            "theorem holFmapAsFiniteSupportRelationWitness_Ctxt :",
            "    Ctxt.toBroad (Ctxt.ofBroad c) = c := rfl",
        ]
        errors = CHECKER["fmap_as_finite_support_relation_errors"](
            lines,
            (("Ctxt", "vars"), ("sourceLocals", ""), ("targetLocals", "")),
            "Example.lean",
            "def localsRel (context : Ctxt) (sourceLocals : HolFiniteMapExact MlS (ValueHOL width)) (targetLocals : HolFiniteMapExact Nat (HolWordLab width)) : Prop",
        )
        self.assertEqual(errors, [])

    def test_fmap_as_finite_support_relation_rejects_raw_parameter(self):
        lines = ["def localsRel (sourceLocals : MlS \u2192 Option (ValueHOL width)) : Prop := True"]
        errors = CHECKER["fmap_as_finite_support_relation_errors"](
            lines, (("sourceLocals", ""),), "Example.lean",
            "def localsRel (sourceLocals : MlS \u2192 Option (ValueHOL width)) : Prop := True",
        )
        self.assertTrue(any("sourceLocals" in e and "HolFiniteMapExact" in e for e in errors))

    def test_fmap_as_finite_support_relation_rejects_unbound_parameter(self):
        lines = ["def localsRel (other : HolFiniteMapExact MlS (ValueHOL width)) : Prop := True"]
        errors = CHECKER["fmap_as_finite_support_relation_errors"](
            lines, (("sourceLocals", ""),), "Example.lean",
            "def localsRel (other : HolFiniteMapExact MlS (ValueHOL width)) : Prop := True",
        )
        self.assertTrue(any("sourceLocals" in e for e in errors))

    def test_fmap_as_finite_support_equalities_qualifier(self):
        self.assertEqual(
            list(SITES([
                '@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "slc_tlc_rw"',
                '  (fmap_as_finite_support_equalities)]'
            ])),
            [(1, "cakeml/pancake/proofs/pan_to_crepProofScript.sml",
              "slc_tlc_rw", None, (), (), (), (), False, (), True, False, ())],
        )

    def test_fmap_as_finite_support_equalities_accepts_two_witnesses(self):
        declaration = (
            "theorem slcTlcRwHOL {width : Nat} [NeZero width] :\n"
            "    (HolFiniteMapExact.updateListEq HolFiniteMapExact.empty xs = slcHOL xs args) \u2227\n"
            "    (HolFiniteMapExact.updateListEq HolFiniteMapExact.empty ys = tlcHOL ys args)"
        )
        lines = [
            declaration + " := by constructor <;> rfl",
            "",
            "theorem holFmapAsFiniteSupportEqualityWitness_slcTlcRwHOL_1 (k : Nat) :",
            "    (HolFiniteMapExact.updateListEq HolFiniteMapExact.empty xs).lookup k =",
            "      (slcHOL xs args).lookup k := rfl",
            "",
            "theorem holFmapAsFiniteSupportEqualityWitness_slcTlcRwHOL_2 (k : Nat) :",
            "    (HolFiniteMapExact.updateListEq HolFiniteMapExact.empty ys).lookup k =",
            "      (tlcHOL ys args).lookup k := rfl",
        ]
        errors = CHECKER["fmap_as_finite_support_equalities_errors"](
            lines, "Example.lean", declaration, "slcTlcRwHOL",
        )
        self.assertEqual(errors, [])

    def test_fmap_as_finite_support_equalities_requires_both_witnesses(self):
        declaration = (
            "theorem slcTlcRwHOL :\n"
            "    (HolFiniteMapExact.empty = a) \u2227 (HolFiniteMapExact.empty = b)"
        )
        lines = [
            declaration + " := by constructor <;> rfl",
            "theorem holFmapAsFiniteSupportEqualityWitness_slcTlcRwHOL_1 :",
            "    (HolFiniteMapExact.empty).lookup k = a.lookup k := rfl",
        ]
        errors = CHECKER["fmap_as_finite_support_equalities_errors"](
            lines, "Example.lean", declaration, "slcTlcRwHOL",
        )
        self.assertTrue(any("conjunct 2" in error for error in errors))

    def test_fmap_as_finite_support_equalities_rejects_non_conjunction(self):
        declaration = (
            "theorem slcTlcRwHOL :\n"
            "    (HolFiniteMapExact.empty = a)"
        )
        lines = [declaration + " := by rfl"]
        errors = CHECKER["fmap_as_finite_support_equalities_errors"](
            lines, "Example.lean", declaration, "slcTlcRwHOL",
        )
        self.assertTrue(any("at least two" in error for error in errors))

    def test_fmap_as_finite_support_equalities_rejects_ignored_proof_witness(self):
        declaration = (
            "theorem slcTlcRwHOL :\n"
            "    (HolFiniteMapExact.empty = a) \u2227 (HolFiniteMapExact.empty = b)"
        )
        lines = [
            declaration + " := by constructor <;> rfl",
            "theorem holFmapAsFiniteSupportEqualityWitness_slcTlcRwHOL_1 :",
            "    (fun _ => a.lookup k) slcTlcRwHOL = b.lookup k := rfl",
            "theorem holFmapAsFiniteSupportEqualityWitness_slcTlcRwHOL_2 :",
            "    a.lookup k = b.lookup k := rfl",
        ]
        errors = CHECKER["fmap_as_finite_support_equalities_errors"](
            lines, "Example.lean", declaration, "slcTlcRwHOL",
        )
        self.assertTrue(any("ignored-proof" in error for error in errors))

    def test_fmap_as_finite_support_equalities_rejects_self_equality(self):
        declaration = (
            "theorem slcTlcRwHOL :\n"
            "    (HolFiniteMapExact.empty = a) \u2227 (HolFiniteMapExact.empty = b)"
        )
        lines = [
            declaration + " := by constructor <;> rfl",
            "theorem holFmapAsFiniteSupportEqualityWitness_slcTlcRwHOL_1 :",
            "    a.lookup k = a.lookup k := rfl",
            "theorem holFmapAsFiniteSupportEqualityWitness_slcTlcRwHOL_2 :",
            "    a.lookup k = b.lookup k := rfl",
        ]
        errors = CHECKER["fmap_as_finite_support_equalities_errors"](
            lines, "Example.lean", declaration, "slcTlcRwHOL",
        )
        self.assertTrue(any("self-equality" in error for error in errors))

    def test_fmap_as_finite_support_equalities_rejects_one_sided_lookup(self):
        declaration = (
            "theorem slcTlcRwHOL :\n"
            "    (HolFiniteMapExact.empty = a) \u2227 (HolFiniteMapExact.empty = b)"
        )
        lines = [
            declaration + " := by constructor <;> rfl",
            "theorem holFmapAsFiniteSupportEqualityWitness_slcTlcRwHOL_1 :",
            "    a.lookup k = b := rfl",
            "theorem holFmapAsFiniteSupportEqualityWitness_slcTlcRwHOL_2 :",
            "    a.lookup k = b.lookup k := rfl",
        ]
        errors = CHECKER["fmap_as_finite_support_equalities_errors"](
            lines, "Example.lean", declaration, "slcTlcRwHOL",
        )
        self.assertTrue(any("BOTH sides" in error for error in errors))

    def test_fmap_as_finite_support_equalities_rejects_iff_witness(self):
        declaration = (
            "theorem slcTlcRwHOL :\n"
            "    (HolFiniteMapExact.empty = a) \u2227 (HolFiniteMapExact.empty = b)"
        )
        lines = [
            declaration + " := by constructor <;> rfl",
            "theorem holFmapAsFiniteSupportEqualityWitness_slcTlcRwHOL_1 :",
            "    a.lookup k = b.lookup k \u2194 True := Iff.rfl",
            "theorem holFmapAsFiniteSupportEqualityWitness_slcTlcRwHOL_2 :",
            "    a.lookup k = b.lookup k := rfl",
        ]
        errors = CHECKER["fmap_as_finite_support_equalities_errors"](
            lines, "Example.lean", declaration, "slcTlcRwHOL",
        )
        self.assertTrue(any("not an iff" in error for error in errors))

    def test_fmap_as_finite_support_equalities_rejects_premise_assumed_relation(self):
        declaration = (
            "theorem slcTlcRwHOL :\n"
            "    (HolFiniteMapExact.empty = a) \u2227 (HolFiniteMapExact.empty = b)"
        )
        lines = [
            declaration + " := by constructor <;> rfl",
            "theorem holFmapAsFiniteSupportEqualityWitness_slcTlcRwHOL_1",
            "    (h : a.lookup k = b.lookup k) : a.lookup k = b.lookup k := h",
            "theorem holFmapAsFiniteSupportEqualityWitness_slcTlcRwHOL_2 :",
            "    a.lookup k = b.lookup k := rfl",
        ]
        errors = CHECKER["fmap_as_finite_support_equalities_errors"](
            lines, "Example.lean", declaration, "slcTlcRwHOL",
        )
        self.assertTrue(any("assumes the target relation" in error for error in errors))

    def test_fmap_as_finite_support_equalities_rejects_raw_option_map(self):
        declaration = "theorem slcTlcRwHOL :\n    (a = b) \u2227 (c = d)"
        errors = CHECKER["fmap_as_finite_support_equalities_errors"](
            [declaration + " := by constructor <;> rfl"],
            "Example.lean", declaration, "slcTlcRwHOL",
        )
        self.assertTrue(any("HolFiniteMapExact" in error for error in errors))

    def test_fmap_as_finite_support_equalities_rejects_unrelated_witnesses(self):
        declaration = (
            "theorem slcTlcRwHOL :\n"
            "    (HolFiniteMapExact.empty = a) \u2227 (HolFiniteMapExact.empty = b)"
        )
        lines = [
            declaration + " := by constructor <;> rfl",
            "theorem holFmapAsFiniteSupportEqualityWitness_slcTlcRwHOL_1 :",
            "    p.lookup k = q.lookup k := rfl",
            "theorem holFmapAsFiniteSupportEqualityWitness_slcTlcRwHOL_2 :",
            "    r.lookup k = s.lookup k := rfl",
        ]
        errors = CHECKER["fmap_as_finite_support_equalities_errors"](
            lines, "Example.lean", declaration, "slcTlcRwHOL",
        )
        self.assertTrue(any("not associated" in error for error in errors))

    def test_fmap_as_finite_support_equalities_rejects_mismatched_keys(self):
        declaration = (
            "theorem slcTlcRwHOL :\n"
            "    (HolFiniteMapExact.empty = a) \u2227 (HolFiniteMapExact.empty = b)"
        )
        lines = [
            declaration + " := by constructor <;> rfl",
            "theorem holFmapAsFiniteSupportEqualityWitness_slcTlcRwHOL_1 :",
            "    (HolFiniteMapExact.empty).lookup k = a.lookup j := rfl",
            "theorem holFmapAsFiniteSupportEqualityWitness_slcTlcRwHOL_2 :",
            "    (HolFiniteMapExact.empty).lookup k = b.lookup k := rfl",
        ]
        errors = CHECKER["fmap_as_finite_support_equalities_errors"](
            lines, "Example.lean", declaration, "slcTlcRwHOL",
        )
        self.assertTrue(any("SAME key" in error for error in errors))

    def test_fmap_as_finite_support_equalities_rejects_inert_let_bypass(self):
        declaration = (
            "theorem slcTlcRwHOL :\n"
            "    (HolFiniteMapExact.empty = a) \u2227 (HolFiniteMapExact.empty = b)"
        )
        lines = [
            declaration + " := by constructor <;> rfl",
            "theorem holFmapAsFiniteSupportEqualityWitness_slcTlcRwHOL_1 (k : Nat) :",
            "    (let _ := HolFiniteMapExact.empty; HolFiniteMapExact.empty.lookup k) =",
            "      (let _ := a; HolFiniteMapExact.empty.lookup k) := rfl",
            "theorem holFmapAsFiniteSupportEqualityWitness_slcTlcRwHOL_2 (k : Nat) :",
            "    (HolFiniteMapExact.empty).lookup k = b.lookup k := rfl",
        ]
        errors = CHECKER["fmap_as_finite_support_equalities_errors"](
            lines, "Example.lean", declaration, "slcTlcRwHOL",
        )
        self.assertTrue(
            any("not associated" in error or "precisely" in error for error in errors)
        )

    def test_fmap_as_finite_support_equalities_rejects_fixed_key(self):
        declaration = (
            "theorem slcTlcRwHOL :\n"
            "    (HolFiniteMapExact.empty = a) \u2227 (HolFiniteMapExact.empty = b)"
        )
        lines = [
            declaration + " := by constructor <;> rfl",
            "theorem holFmapAsFiniteSupportEqualityWitness_slcTlcRwHOL_1 :",
            "    (HolFiniteMapExact.empty).lookup 0 = a.lookup 0 := rfl",
            "theorem holFmapAsFiniteSupportEqualityWitness_slcTlcRwHOL_2 :",
            "    (HolFiniteMapExact.empty).lookup 0 = b.lookup 0 := rfl",
        ]
        errors = CHECKER["fmap_as_finite_support_equalities_errors"](
            lines, "Example.lean", declaration, "slcTlcRwHOL",
        )
        self.assertTrue(any("universally" in error for error in errors))

    def test_fmap_as_finite_support_result_rejects_ignored_proof_witness(self):
        lines = [
            "def getEidsFromDeclsHOL : HolFiniteMapExact MlS (BitVec width) := fun _ => none",
            "theorem helper : (getEidsFromDeclsHOL d).lookup k = (raw d).lookup k := rfl",
            "theorem holFmapAsFiniteSupportResultWitness_getEidsFromDeclsHOL",
            "    (d : DeclHOL width) (k : MlS) :",
            "    (fun _ => (getEidsFromDeclsHOL d).lookup k) helper =",
            "      (raw d).lookup k :=",
            "  rfl",
        ]
        errors = CHECKER["fmap_as_finite_support_result_errors"](
            lines, "Example.lean",
            "def getEidsFromDeclsHOL : HolFiniteMapExact MlS (BitVec width)",
            "getEidsFromDeclsHOL",
        )
        self.assertTrue(any("directly" in error for error in errors))

    def test_fmap_as_finite_support_result_accepts_lookup_witness(self):
        lines = [
            "def getEidsFromDeclsHOL : HolFiniteMapExact MlS (BitVec width) :=",
            "  fun _ => none",
            "",
            "theorem holFmapAsFiniteSupportResultWitness_getEidsFromDeclsHOL",
            "    (decls : DeclHOL width) (key : MlS) :",
            "    (getEidsFromDeclsHOL decls).lookup key =",
            "      (rawDecls decls).lookup key :=",
            "  rfl",
        ]
        errors = CHECKER["fmap_as_finite_support_result_errors"](
            lines, "Example.lean",
            "def getEidsFromDeclsHOL : HolFiniteMapExact MlS (BitVec width)",
            "getEidsFromDeclsHOL",
        )
        self.assertEqual(errors, [])

    def test_fmap_as_finite_support_result_rejects_self_equality(self):
        lines = [
            "def getEidsFromDeclsHOL : HolFiniteMapExact MlS (BitVec width) := fun _ => none",
            "theorem holFmapAsFiniteSupportResultWitness_getEidsFromDeclsHOL",
            "    (decls : DeclHOL width) (key : MlS) :",
            "    (getEidsFromDeclsHOL decls).lookup key =",
            "      (getEidsFromDeclsHOL decls).lookup key :=",
            "  rfl",
        ]
        errors = CHECKER["fmap_as_finite_support_result_errors"](
            lines, "Example.lean",
            "def getEidsFromDeclsHOL : HolFiniteMapExact MlS (BitVec width)",
            "getEidsFromDeclsHOL",
        )
        self.assertTrue(any("self-equality" in error for error in errors))

    def test_fmap_as_finite_support_result_rejects_premise_assumed_relation(self):
        lines = [
            "def getEidsFromDeclsHOL : HolFiniteMapExact MlS (BitVec width) := fun _ => none",
            "theorem holFmapAsFiniteSupportResultWitness_getEidsFromDeclsHOL",
            "    (decls : DeclHOL width) (key : MlS)",
            "    (h : (getEidsFromDeclsHOL decls).lookup key = (rawDecls decls).lookup key) :",
            "    (getEidsFromDeclsHOL decls).lookup key = (rawDecls decls).lookup key :=",
            "  h",
        ]
        errors = CHECKER["fmap_as_finite_support_result_errors"](
            lines, "Example.lean",
            "def getEidsFromDeclsHOL : HolFiniteMapExact MlS (BitVec width)",
            "getEidsFromDeclsHOL",
        )
        self.assertTrue(any("assumes the target relation" in error for error in errors))

    def test_fmap_as_finite_support_result_rejects_raw_option_map(self):
        errors = CHECKER["fmap_as_finite_support_result_errors"](
            ["def getEids : MlS → Option (BitVec width) := fun _ => none"],
            "Example.lean",
            "def getEids : MlS → Option (BitVec width)",
            "getEids",
        )
        self.assertTrue(any("HolFiniteMapExact" in error for error in errors))

    def test_fmap_as_finite_support_result_requires_canonical_witness(self):
        errors = CHECKER["fmap_as_finite_support_result_errors"](
            ["def getEidsFromDeclsHOL : HolFiniteMapExact MlS (BitVec width) := fun _ => none"],
            "Example.lean",
            "def getEidsFromDeclsHOL : HolFiniteMapExact MlS (BitVec width)",
            "getEidsFromDeclsHOL",
        )
        self.assertTrue(any("witness" in error for error in errors))

    def test_fmap_as_finite_support_result_rejects_vacuous_witness(self):
        lines = [
            "def getEidsFromDeclsHOL : HolFiniteMapExact MlS (BitVec width) := fun _ => none",
            "theorem holFmapAsFiniteSupportResultWitness_getEidsFromDeclsHOL : True := trivial",
        ]
        errors = CHECKER["fmap_as_finite_support_result_errors"](
            lines, "Example.lean",
            "def getEidsFromDeclsHOL : HolFiniteMapExact MlS (BitVec width)",
            "getEidsFromDeclsHOL",
        )
        self.assertTrue(errors)

    def test_fmap_as_finite_support_result_rejects_wrong_declaration(self):
        lines = [
            "def getEidsFromDeclsHOL : HolFiniteMapExact MlS (BitVec width) := fun _ => none",
            "theorem holFmapAsFiniteSupportResultWitness_getEidsFromDeclsHOL",
            "    (x : Nat) : x = x := rfl",
        ]
        errors = CHECKER["fmap_as_finite_support_result_errors"](
            lines, "Example.lean",
            "def getEidsFromDeclsHOL : HolFiniteMapExact MlS (BitVec width)",
            "getEidsFromDeclsHOL",
        )
        self.assertTrue(any("tagged declaration" in error for error in errors))

    def test_fmap_as_finite_support_result_rejects_unrelated_witness(self):
        lines = [
            "def getEidsFromDeclsHOL : HolFiniteMapExact MlS (BitVec width) := fun _ => none",
            "theorem holFmapAsFiniteSupportResultWitness_getEidsFromDeclsHOL",
            "    (other : HolFiniteMapExact MlS (BitVec width)) : other.lookup k = other.lookup k :=",
            "  rfl",
        ]
        errors = CHECKER["fmap_as_finite_support_result_errors"](
            lines, "Example.lean",
            "def getEidsFromDeclsHOL : HolFiniteMapExact MlS (BitVec width)",
            "getEidsFromDeclsHOL",
        )
        self.assertTrue(any("tagged declaration" in error for error in errors))

    def test_fmap_as_finite_support_accepts_canonical_carrier(self):
        lines = [
            "structure State where",
            "  locals : HolFiniteMapExact MlS (ValueHOL width)",
            "  globals : HolFiniteMapExact MlS (ValueHOL width)",
            "",
            "structure Broad where",
            "  clock : Nat",
            "",
            "theorem holFmapAsFiniteSupportWitness {width : Nat} :",
            "    (∀ s : State width, ofExact (toExact s) = s) :=",
            "  fun _ => rfl",
        ]
        errors = CHECKER["fmap_as_finite_support_errors"](
            lines, ("locals", "globals"), "Example.lean"
        )
        self.assertEqual(errors, [])

    def test_fmap_as_finite_support_witness_is_carrier_agnostic(self):
        lines = [
            "structure CrepStateExact where",
            "  locals : HolFiniteMapExact MlS (ValueHOL width)",
            "structure CrepSemBroad where",
            "  clock : Nat",
            "",
            "theorem holFmapAsFiniteSupportWitness {width : Nat} :",
            "    (∀ s : CrepStateExact width,",
            "      ofExact (toExact s) = s) :=",
            "  fun _ => rfl",
        ]
        errors = CHECKER["fmap_as_finite_support_errors"](
            lines, ("locals",), "Flapjack/Pancake/Semantics/CrepSem/StateExact.lean"
        )
        self.assertEqual(errors, [])

    def test_fmap_as_finite_support_witness_accepts_roundtrip(self):
        lines = [
            "structure State where",
            "  locals : HolFiniteMapExact MlS (ValueHOL width)",
            "",
            "theorem holFmapAsFiniteSupportWitness {width : Nat} :",
            "    (ofExact (toExact (State width)) = State width) := by rfl",
        ]
        errors = CHECKER["fmap_as_finite_support_errors"](
            lines, ("locals",), "Example.lean"
        )
        self.assertEqual(errors, [])

    def test_fmap_as_finite_support_rejects_raw_option_map(self):
        lines = [
            "structure State where",
            "  locals : String → Option Nat",
            "",
            "theorem holFmapAsFiniteSupportWitness {width : Nat} :",
            "    State width -> State width := fun s => ofExact s",
        ]
        errors = CHECKER["fmap_as_finite_support_errors"](
            lines, ("locals",), "Example.lean"
        )
        self.assertTrue(
            any("approved HolFiniteMapExact carrier" in error for error in errors)
        )

    def test_fmap_as_finite_support_requires_canonical_witness(self):
        lines = [
            "structure State where",
            "  locals : HolFiniteMapExact MlS (ValueHOL width)",
        ]
        errors = CHECKER["fmap_as_finite_support_errors"](
            lines, ("locals",), "Example.lean"
        )
        self.assertTrue(any("canonical witness" in error for error in errors))

    def test_fmap_as_finite_support_witness_must_mention_owner(self):
        lines = [
            "structure State where",
            "  locals : HolFiniteMapExact MlS (ValueHOL width)",
            "",
            "theorem holFmapAsFiniteSupportWitness {width : Nat} :",
            "    HolFiniteMapExact MlS (ValueHOL width) -> Unit := fun m => ()",
        ]
        errors = CHECKER["fmap_as_finite_support_errors"](
            lines, ("locals",), "Example.lean"
        )
        self.assertTrue(any("canonical witness" in error for error in errors))

    def test_fmap_as_finite_support_rejects_split_owners(self):
        lines = [
            "structure A where",
            "  locals : HolFiniteMapExact MlS (ValueHOL width)",
            "structure B where",
            "  globals : HolFiniteMapExact MlS (ValueHOL width)",
            "",
            "theorem holFmapAsFiniteSupportWitness {width : Nat} :",
            "    A width -> A width := fun s => ofExact s",
        ]
        errors = CHECKER["fmap_as_finite_support_errors"](
            lines, ("locals", "globals"), "Example.lean"
        )
        self.assertTrue(
            any("one owning carrier structure" in error for error in errors)
        )

    def test_fmap_as_finite_support_rejects_unrelated_witness(self):
        lines = [
            "structure State where",
            "  locals : HolFiniteMapExact MlS (ValueHOL width)",
            "structure Other where",
            "  clock : Nat",
            "",
            "theorem holFmapAsFiniteSupportWitness {width : Nat} :",
            "    Other width -> Other width := fun s => s",
        ]
        errors = CHECKER["fmap_as_finite_support_errors"](
            lines, ("locals",), "Example.lean"
        )
        self.assertTrue(any("canonical witness" in error for error in errors))

    def test_fmap_as_finite_support_witness_requires_roundtrip(self):
        lines = [
            "structure State where",
            "  locals : HolFiniteMapExact MlS (ValueHOL width)",
            "",
            "theorem holFmapAsFiniteSupportWitness {width : Nat} :",
            "    State width -> State width := fun s => s",
        ]
        errors = CHECKER["fmap_as_finite_support_errors"](
            lines, ("locals",), "Example.lean"
        )
        self.assertTrue(any("canonical witness" in error for error in errors))

    def test_fmap_as_finite_support_rejects_counterpart_without_roundtrip(self):
        lines = [
            "structure State where",
            "  locals : HolFiniteMapExact MlS (ValueHOL width)",
            "structure Broad where",
            "  clock : Nat",
            "",
            "theorem holFmapAsFiniteSupportWitness {width : Nat} :",
            "    State width -> Broad width -> State width := fun s _ => s",
        ]
        errors = CHECKER["fmap_as_finite_support_errors"](
            lines, ("locals",), "Example.lean"
        )
        self.assertTrue(any("canonical witness" in error for error in errors))

    def test_fmap_as_finite_support_disambiguates_shared_fields_by_carrier(self):
        lines = [
            "structure CrepSemHOLState (width : Nat) where",
            "  locals : HolFiniteMapExact Nat (HolWordLab width)",
            "  globals : HolFiniteMapExact (BitVec 5) (HolWordLab width)",
            "structure CrepSemHOLFiniteState (width : Nat) where",
            "  locals : HolFiniteMapExact Nat (PanWordLab (ι → Bool))",
            "  globals : HolFiniteMapExact (BitVec 5) (PanWordLab (ι → Bool))",
            "",
            "theorem holFmapAsFiniteSupportWitness {width : Nat} :",
            "    (∀ s : CrepSemHOLState width, ofBroad (toBroad s) = s) := by rfl",
            "@[hol \"cakeml/pancake/semantics/crepSemScript.sml\" \"foo_def\"",
            "  (fmap_as_finite_support := [locals, globals])]",
            "def helper (s : CrepSemHOLState width) := s",
        ]
        errors = CHECKER["fmap_as_finite_support_errors"](
            lines, ("locals", "globals"),
            "Flapjack/Pancake/Semantics/CrepSem/HOLState.lean",
            "def helper (s : CrepSemHOLState width) := s",
        )
        self.assertEqual(errors, [])

    def test_fmap_as_finite_support_rejects_ambiguous_shared_fields(self):
        lines = [
            "structure CrepSemHOLState (width : Nat) where",
            "  locals : HolFiniteMapExact Nat (HolWordLab width)",
            "structure CrepSemHOLFiniteState (width : Nat) where",
            "  locals : HolFiniteMapExact Nat (PanWordLab (ι → Bool))",
            "",
            "theorem holFmapAsFiniteSupportWitness {width : Nat} :",
            "    (∀ s : CrepSemHOLState width, ofBroad (toBroad s) = s) := by rfl",
        ]
        errors = CHECKER["fmap_as_finite_support_errors"](
            lines, ("locals",), "Flapjack/Pancake/Semantics/CrepSem/HOLState.lean"
        )
        self.assertTrue(
            any("one owning carrier structure" in error for error in errors)
        )

    def test_fmap_as_finite_support_rejects_carrier_naming_neither_owner(self):
        lines = [
            "structure CrepSemHOLState (width : Nat) where",
            "  locals : HolFiniteMapExact Nat (HolWordLab width)",
            "structure CrepSemHOLFiniteState (width : Nat) where",
            "  locals : HolFiniteMapExact Nat (PanWordLab (ι → Bool))",
            "structure Other where",
            "  clock : Nat",
            "",
            "theorem holFmapAsFiniteSupportWitness {width : Nat} :",
            "    (∀ s : CrepSemHOLState width, ofBroad (toBroad s) = s) := by rfl",
        ]
        errors = CHECKER["fmap_as_finite_support_errors"](
            lines, ("locals",),
            "Flapjack/Pancake/Semantics/CrepSem/HOLState.lean",
            "def helper (s : Other) := s",
        )
        self.assertTrue(
            any("one owning carrier structure" in error for error in errors)
        )

    def test_fmap_as_finite_support_reads_type_from_tagged_carrier(self):
        lines = [
            "structure BroadState where",
            "  locals : Nat \u2192 Option Nat",
            "structure FiniteState where",
            "  locals : HolFiniteMapExact Nat Nat",
            "",
            "theorem holFmapAsFiniteSupportWitness :",
            "    (\u2200 s : FiniteState, ofBroad (toBroad s) = s) := by rfl",
        ]
        errors = CHECKER["fmap_as_finite_support_errors"](
            lines, ("locals",), "Flapjack/Broad.lean",
            "def helper (s : FiniteState) := s",
        )
        self.assertEqual(
            errors, [],
            "the type must be read from the disambiguated owning carrier, not the "
            "first structure declaring the field",
        )

    def test_fmap_as_finite_support_accepts_imported_carrier_witness(self):
        checker_globals = CHECKER["fmap_as_finite_support_errors"].__globals__
        original_root = checker_globals["ROOT"]
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            owner = root / "Flapjack" / "PanToCrep" / "ContextExact.lean"
            consumer = root / "Flapjack" / "PanToCrep" / "CompileExact.lean"
            owner.parent.mkdir(parents=True)
            owner.write_text(
                "\n".join([
                    "structure PanToCrepContextExact where",
                    "  vars : HolFiniteMapExact Name Shape",
                    "  funcs : HolFiniteMapExact Name FunctionInfo",
                    "  eids : HolFiniteMapExact Name Word",
                ]),
                encoding="utf-8",
            )
            consumer.write_text(
                "\n".join([
                    "import Flapjack.PanToCrep.ContextExact",
                    "theorem holFmapAsFiniteSupportWitness",
                    "    (context : PanToCrepContextExact) :",
                    "    PanToCrepContextExact.ofBroad",
                    "      (PanToCrepContextExact.toBroad context) = context := by",
                    "  exact PanToCrepContextExact.holFmapAsFiniteSupportWitness context",
                    '@[hol "cakeml/pancake/pan_to_crepScript.sml" "compile_exp_def"',
                    "  (fmap_as_finite_support := [vars, funcs, eids])]",
                    "def compileExpExactHOLW (context : PanToCrepContextExact) := context.vars",
                ]),
                encoding="utf-8",
            )
            checker_globals["ROOT"] = root
            try:
                lines = consumer.read_text(encoding="utf-8").splitlines()
                errors = CHECKER["fmap_as_finite_support_errors"](
                    lines, ("vars", "funcs", "eids"),
                    "Flapjack/PanToCrep/CompileExact.lean",
                    CHECKER["tagged_declaration_text"](lines, 6),
                )
                self.assertEqual(errors, [])
            finally:
                checker_globals["ROOT"] = original_root

    def test_combined_fmap_words_qualifiers_with_imported_owner(self):
        """A real imported-owner + evaluator-local witness + both qualifiers.

        Mirrors the crepSem `evaluate_def` arrangement: `CrepSemHOLState` lives
        in an imported module, the tagged declaration is in the consumer module
        with a local `holFmapAsFiniteSupportWitness`, and the tag carries both
        `(fmap_as_finite_support := [...])` and `(words_as_type_indexed_bitvec)`.
        """
        checker_globals = CHECKER["fmap_as_finite_support_errors"].__globals__
        original_root = checker_globals["ROOT"]
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            owner = root / "Flapjack" / "PanToCrep" / "ContextExact.lean"
            consumer = root / "Flapjack" / "PanToCrep" / "CompileExact.lean"
            owner.parent.mkdir(parents=True)
            owner.write_text(
                "\n".join([
                    "structure CrepStateExact (width : Nat) where",
                    "  locals : HolFiniteMapExact Nat (HolWordLab width)",
                    "  globals : HolFiniteMapExact (BitVec 5) (HolWordLab width)",
                    "  code : HolFiniteMapExact Name Prog",
                ]),
                encoding="utf-8",
            )
            consumer.write_text(
                "\n".join([
                    "import Flapjack.PanToCrep.ContextExact",
                    "theorem holFmapAsFiniteSupportWitness",
                    "    (state : CrepStateExact width) :",
                    "    CrepStateExact.ofBroad",
                    "      (CrepStateExact.toBroad state) = state := by",
                    "  exact CrepStateExact.holFmapAsFiniteSupportWitness state",
                    '@[hol "cakeml/pancake/semantics/crepSemScript.sml" "evaluate_def" 240',
                    "  (fmap_as_finite_support := [locals, globals, code])",
                    "  (words_as_type_indexed_bitvec)]",
                    "def evalProg {width : Nat} (state : CrepStateExact width) [NeZero width]",
                    "    (address : BitVec width) := address",
                ]),
                encoding="utf-8",
            )
            checker_globals["ROOT"] = root
            try:
                lines = consumer.read_text(encoding="utf-8").splitlines()
                declaration_text = CHECKER["tagged_declaration_text"](lines, 6)
                self.assertEqual(
                    CHECKER["fmap_as_finite_support_errors"](
                        lines, ("locals", "globals", "code"),
                        "Flapjack/PanToCrep/CompileExact.lean",
                        declaration_text,
                    ),
                    [],
                )
                self.assertEqual(
                    CHECKER["words_as_type_indexed_bitvec_errors"](
                        declaration_text, "evalProg",
                    ),
                    [],
                )
            finally:
                checker_globals["ROOT"] = original_root

    def test_fmap_as_finite_support_rejects_local_duplicate_of_imported_owner(self):
        checker_globals = CHECKER["fmap_as_finite_support_errors"].__globals__
        original_root = checker_globals["ROOT"]
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            owner = root / "Flapjack" / "PanToCrep" / "ContextExact.lean"
            consumer = root / "Flapjack" / "PanToCrep" / "CompileExact.lean"
            owner.parent.mkdir(parents=True)
            owner.write_text(
                "\n".join([
                    "structure PanToCrepContextExact where",
                    "  vars : HolFiniteMapExact Name Shape",
                    "  funcs : HolFiniteMapExact Name FunctionInfo",
                    "  eids : HolFiniteMapExact Name Word",
                ]),
                encoding="utf-8",
            )
            consumer.write_text(
                "\n".join([
                    "import Flapjack.PanToCrep.ContextExact",
                    "structure PanToCrepContextExact where",
                    "  vars : HolFiniteMapExact Name Shape",
                    "  funcs : HolFiniteMapExact Name FunctionInfo",
                    "  eids : HolFiniteMapExact Name Word",
                    "theorem holFmapAsFiniteSupportWitness",
                    "    (context : PanToCrepContextExact) :",
                    "    PanToCrepContextExact.ofBroad",
                    "      (PanToCrepContextExact.toBroad context) = context := by",
                    "  exact PanToCrepContextExact.holFmapAsFiniteSupportWitness context",
                    '@[hol "cakeml/pancake/pan_to_crepScript.sml" "compile_exp_def"',
                    "  (fmap_as_finite_support := [vars, funcs, eids])]",
                    "def compileExpExactHOLW (context : PanToCrepContextExact) := context.vars",
                ]),
                encoding="utf-8",
            )
            checker_globals["ROOT"] = root
            try:
                lines = consumer.read_text(encoding="utf-8").splitlines()
                errors = CHECKER["fmap_as_finite_support_errors"](
                    lines, ("vars", "funcs", "eids"),
                    "Flapjack/PanToCrep/CompileExact.lean",
                    CHECKER["tagged_declaration_text"](lines, 11),
                )
                self.assertTrue(
                    any("one owning carrier structure" in e for e in errors),
                    errors,
                )
            finally:
                checker_globals["ROOT"] = original_root

    def test_fmap_as_finite_support_rejects_imported_wrong_owner_type_and_witness(self):
        for wrong_field_type, wrong_witness in [
            ("String \u2192 Option Nat", False),
            ("HolFiniteMapExact Name Shape", True),
        ]:
            with self.subTest(wrong_field_type=wrong_field_type,
                              wrong_witness=wrong_witness):
                checker_globals = CHECKER["fmap_as_finite_support_errors"].__globals__
                original_root = checker_globals["ROOT"]
                with tempfile.TemporaryDirectory() as directory:
                    root = Path(directory)
                    owner = root / "Flapjack" / "PanToCrep" / "ContextExact.lean"
                    consumer = root / "Flapjack" / "PanToCrep" / "CompileExact.lean"
                    owner.parent.mkdir(parents=True)
                    owner.write_text(
                        "\n".join([
                            "structure PanToCrepContextExact where",
                            f"  vars : {wrong_field_type}",
                            "structure OtherContext where",
                            "  vars : HolFiniteMapExact Name Shape",
                        ]),
                        encoding="utf-8",
                    )
                    witness_owner = "OtherContext" if wrong_witness else "PanToCrepContextExact"
                    consumer.write_text(
                        "\n".join([
                            "import Flapjack.PanToCrep.ContextExact",
                            "theorem holFmapAsFiniteSupportWitness",
                            f"    (context : {witness_owner}) :",
                            f"    {witness_owner}.ofBroad ({witness_owner}.toBroad context) = context := by",
                            f"  exact {witness_owner}.roundtrip context",
                            '@[hol "cakeml/pancake/pan_to_crepScript.sml" "compile_exp_def"',
                            "  (fmap_as_finite_support := [vars])]",
                            "def compileExpExactHOLW (context : PanToCrepContextExact) := context.vars",
                        ]),
                        encoding="utf-8",
                    )
                    checker_globals["ROOT"] = root
                    try:
                        lines = consumer.read_text(encoding="utf-8").splitlines()
                        errors = CHECKER["fmap_as_finite_support_errors"](
                            lines, ("vars",),
                            "Flapjack/PanToCrep/CompileExact.lean",
                            CHECKER["tagged_declaration_text"](lines, 6),
                        )
                        if wrong_witness:
                            self.assertTrue(any("canonical witness" in e for e in errors))
                        else:
                            self.assertTrue(any("approved HolFiniteMapExact" in e
                                                for e in errors))
                    finally:
                        checker_globals["ROOT"] = original_root

    def test_fmap_as_finite_support_rejects_num_map_sptree_field(self):
        # A HOL `sptree$num_map` field (here `Spt`) is not a `|->` finite map and
        # must not be claimed by `fmap_as_finite_support`, even though its Lean
        # field could plausibly be represented by a finite-map carrier.
        lines = [
            "structure LoopStateNumMap where",
            "  locals : Spt Nat Nat",
            "  globals : HolFiniteMapExact (BitVec 5) Nat",
            "",
            "theorem holFmapAsFiniteSupportWitness :",
            "    (\u2200 s : LoopStateNumMap, ofBroad (toBroad s) = s) := by rfl",
        ]
        errors = CHECKER["fmap_as_finite_support_errors"](
            lines, ("locals",), "Flapjack/LoopState.lean",
            "def getVarImm (s : LoopStateNumMap) := s.locals",
        )
        self.assertTrue(
            any("approved HolFiniteMapExact" in error for error in errors),
            errors,
        )

    def test_fmap_as_finite_support_rejects_raw_type_on_named_carrier(self):
        lines = [
            "structure BroadState where",
            "  locals : Nat \u2192 Option Nat",
            "structure FiniteState where",
            "  locals : HolFiniteMapExact Nat Nat",
            "",
            "theorem holFmapAsFiniteSupportWitness :",
            "    (\u2200 s : FiniteState, ofBroad (toBroad s) = s) := by rfl",
        ]
        errors = CHECKER["fmap_as_finite_support_errors"](
            lines, ("locals",), "Flapjack/Broad.lean",
            "def helper (s : BroadState) := s",
        )
        self.assertTrue(
            any(
                "owning structure `BroadState`" in error
                and "HolFiniteMapExact" in error
                for error in errors
            ),
            errors,
        )

    def test_fmap_as_finite_support_matches_owner_as_identifier_token(self):
        lines = [
            "structure State where",
            "  locals : HolFiniteMapExact Nat Nat",
            "structure FiniteState where",
            "  locals : HolFiniteMapExact Nat Nat",
            "",
            "theorem holFmapAsFiniteSupportWitness :",
            "    (\u2200 s : FiniteState, ofBroad (toBroad s) = s) := by rfl",
        ]
        errors = CHECKER["fmap_as_finite_support_errors"](
            lines, ("locals",), "Flapjack/Broad.lean",
            "def helper (s : FiniteState) := s",
        )
        self.assertEqual(
            errors, [],
            "`State` must not match inside `FiniteState`; the owner is a whole "
            "identifier token",
        )

    def test_tagged_declaration_text_stops_before_next_declaration(self):
        lines = [
            '@[hol "cakeml/pancake/semantics/panSemScript.sml" "eval_def"',
            "  (fmap_as_finite_support := [locals])]",
            "def evalHOLFinite (s : State width) : Nat := s.clock",
            "",
            "def other : Nat := 0",
        ]
        text = CHECKER["tagged_declaration_text"](lines, 1)
        self.assertIn("State width", text)
        self.assertNotIn("other : Nat", text)

    def test_tagged_noncomputable_def_disambiguates_finite_map_carrier(self):
        lines = [
            "structure BroadState where",
            "  locals : HolFiniteMapExact Nat Nat",
            "structure FiniteState where",
            "  locals : HolFiniteMapExact Nat Nat",
            "theorem holFmapAsFiniteSupportWitness :",
            "    (\u2200 s : FiniteState, ofBroad (toBroad s) = s) := by rfl",
            '@[hol "cakeml/pancake/semantics/crepSemScript.sml" "eval_def"',
            "  (fmap_as_finite_support := [locals])]",
            "noncomputable def evalHOLFinite (s : FiniteState) : Nat := 0",
            "def unrelated (s : BroadState) : Nat := 0",
        ]
        declaration_text = CHECKER["tagged_declaration_text"](lines, 7)
        self.assertIn("FiniteState", declaration_text)
        self.assertNotIn("unrelated", declaration_text)
        errors = CHECKER["fmap_as_finite_support_errors"](
            lines, ("locals",), "Flapjack/Crep/HOLState.lean", declaration_text
        )
        self.assertEqual(errors, [])

    def test_representation_witness_is_checked_in_same_module(self):
        lines = [
            "structure State where",
            "  degrees : CakeNodeMap Nat",
            "theorem holListArrayWitness_degrees (state : State) (xs : List Nat)",
            "    (h : state.degrees = CakeNodeMap.ofList xs) :",
            "    RepresentsHOLNodeList state.degrees xs := by",
            "  rw [h]",
            "  exact CakeNodeMap.ofList_representsHOLNodeList xs",
        ]
        self.assertIn("degrees", CHECKER["structure_fields"](lines))
        self.assertTrue(CHECKER["has_list_array_witness"](lines, "degrees"))
        self.assertFalse(CHECKER["has_list_array_witness"](lines, "moves"))
        self.assertEqual(
            CHECKER["list_as_array_errors"](lines, ("degrees",), "Example.lean"),
            [],
        )
        errors = CHECKER["list_as_array_errors"](
            lines, ("moves",), "Example.lean"
        )
        self.assertTrue(any("not a field" in error for error in errors))
        self.assertTrue(any("no same-module checked witness" in error for error in errors))

    def test_circular_representation_assumption_is_not_a_witness(self):
        lines = [
            "structure State where",
            "  degrees : CakeNodeMap Nat",
            "theorem holListArrayWitness_degrees (state : State) (xs : List Nat)",
            "    (h : RepresentsHOLNodeList state.degrees xs) :",
            "    RepresentsHOLNodeList state.degrees xs := h",
        ]
        self.assertFalse(
            CHECKER["has_list_array_witness"](lines, "degrees")
        )

    def test_comments_cannot_supply_qualified_field_or_witness(self):
        lines = [
            "/- structure State where",
            "  degrees : CakeNodeMap Nat",
            "theorem holListArrayWitness_degrees : RepresentsHOLNodeList s.degrees xs := by",
            "  exact h -/",
        ]
        errors = CHECKER["list_as_array_errors"](
            lines, ("degrees",), "Example.lean"
        )
        self.assertTrue(any("not a field" in error for error in errors))
        self.assertTrue(any("no same-module checked witness" in error for error in errors))

    def test_equality_only_mlstring_identifier_needs_no_byte_witness(self):
        lines = ["def lookupByName (name : String) := name"]
        self.assertEqual(
            CHECKER["names_as_string_errors"](
                lines, ("name",), (), "Example.lean", "lookupByName"
            ),
            [],
        )

    def test_parameter_boundary_accepts_premise_aware_declaration_witness(self):
        lines = [
            "def freshNameHOL (name : String) (names : List String) := name",
            "theorem holMlStringWitness_freshNameHOL (name : String)",
            "    (names : List String) (hname : NameRanged name) :",
            "    Flapjack.Pancake.PanLang.NameRanged (freshNameHOL name names) := by",
            "  exact freshNameHOL_nameRanged name names hname",
        ]
        self.assertTrue(CHECKER["has_mlstring_witness"](lines, "freshNameHOL"))
        self.assertEqual(
            CHECKER["names_as_string_errors"](
                lines, ("name",), ("name",), "PanGlobals.lean", "freshNameHOL"
            ),
            [],
        )

    def test_boundary_requires_same_module_witness_for_tagged_declaration(self):
        missing = ["def freshNameHOL (name : String) := name"]
        errors = CHECKER["names_as_string_errors"](
            missing, ("name",), ("name",), "PanGlobals.lean", "freshNameHOL"
        )
        self.assertTrue(any("no same-module checked witness" in error for error in errors))

        wrong_name = [
            "theorem holMlStringWitness_other (name : String) :",
            "    NameRanged name := by",
            "  exact h",
        ]
        self.assertFalse(CHECKER["has_mlstring_witness"](wrong_name, "freshNameHOL"))

    def test_boundary_classifier_must_be_qualified(self):
        lines = [
            "theorem holMlStringWitness_freshNameHOL (name : String)",
            "    (h : NameRanged name) : NameRanged (freshNameHOL name) := by",
            "  exact h",
        ]
        errors = CHECKER["names_as_string_errors"](
            lines, ("name",), ("generated",), "PanGlobals.lean", "freshNameHOL"
        )
        self.assertTrue(any("not listed by names_as_string" in error for error in errors))

    def test_boundary_witness_must_conclude_name_ranged(self):
        lines = [
            "theorem holMlStringWitness_freshNameHOL (name : String) :",
            "    name = name := by rfl",
        ]
        self.assertFalse(CHECKER["has_mlstring_witness"](lines, "freshNameHOL"))

    def test_duplicate_name_requires_correct_line(self):
        path = Path(__file__).resolve().parents[2] / \
            "cakeml/pancake/proofs/pan_to_crepProofScript.sml"
        cache = {}
        self.assertIn("multiple lines", REF_ERROR(path, "locals_rel_wf_shape", None, cache))
        self.assertIsNone(REF_ERROR(path, "locals_rel_wf_shape", 2345, cache))
        self.assertIsNone(REF_ERROR(path, "locals_rel_wf_shape", 3008, cache))
        self.assertIn("not at line", REF_ERROR(path, "locals_rel_wf_shape", 2346, cache))


DECL = CHECKER["hol_declaration_lines"]


class HolDatatypeDeclarationsTest(unittest.TestCase):
    def _write_sml(self, text):
        handle = tempfile.NamedTemporaryFile(
            "w", suffix=".sml", delete=False, encoding="utf-8"
        )
        handle.write(text)
        handle.close()
        self.addCleanup(lambda: os.unlink(handle.name))
        return Path(handle.name)

    def test_datatype_block_type_name_is_indexed(self):
        path = self._write_sml(
            "Datatype:\n  shape = One\n        | Comb (shape list)\nEnd\n"
        )
        self.assertEqual(DECL(path, {})["shape"], [2])

    def test_panlang_shape_is_resolvable(self):
        path = (
            Path(__file__).resolve().parents[2]
            / "cakeml/pancake/panLangScript.sml"
        )
        cache = {}
        self.assertIsNone(REF_ERROR(path, "shape", None, cache))
        self.assertIn("declares no", REF_ERROR(path, "no_such_type", None, cache))
        self.assertIn("not at line", REF_ERROR(path, "shape", 1, cache))

    def test_repeated_datatype_name_requires_line(self):
        path = self._write_sml(
            "Datatype:\n  foo = A\nEnd\nDatatype:\n  foo = B\nEnd\n"
        )
        cache = {}
        self.assertEqual(DECL(path, cache)["foo"], [2, 5])
        self.assertIn("multiple lines", REF_ERROR(path, "foo", None, cache))
        self.assertIsNone(REF_ERROR(path, "foo", 2, cache))
        self.assertIsNone(REF_ERROR(path, "foo", 5, cache))

    def test_record_field_is_not_a_datatype_name(self):
        path = self._write_sml(
            "Datatype:\n  expr = Rec <| field : num |>\nEnd\n"
        )
        names = DECL(path, {})
        self.assertEqual(names["expr"], [2])
        self.assertNotIn("field", names)


class HolProgWordAliasTest(unittest.TestCase):
    SIGNATURE = "theorem example {width : Nat} [NeZero width] (p : HolProg width) : True := by trivial"
    MODULE = "Flapjack.AliasProbe"

    def fixture(self, root):
        for module in ("Flapjack.Compiler.Backend.StackLang.Prog",
                       "Flapjack.Compiler.Backend.StackLang",
                       "Flapjack.Compiler.Encoders.Asm"):
            relative = Path(module.replace(".", "/") + ".lean")
            destination = root / relative
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_text((CHECKER["ROOT"] / relative).read_text())
        (root / "Flapjack/AliasProbe.lean").write_text(
            "import Flapjack.Compiler.Backend.StackLang.Prog\n" + self.SIGNATURE)

    def errors(self, root, signature=None):
        signature = signature or self.SIGNATURE
        return CHECKER["words_as_type_indexed_bitvec_errors"](
            signature, "example", module=self.MODULE, root=str(root), lines=signature.splitlines())

    def test_exact_alias(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self.fixture(root)
            for name in ("HolProg", "StackLang.HolProg", "Compiler.Backend.StackLang.HolProg",
                         "Flapjack.Compiler.Backend.StackLang.HolProg"):
                self.assertEqual(self.errors(root, self.SIGNATURE.replace("HolProg", name)), [])

    def test_rejects_source_drift(self):
        for old, new in (("[NeZero width]", ""),
                         ("(HolAddr width)", "(HolAddr 64)"),
                         ("HolRegImm width", "HolRegImm 0"),
                         ("HolCmp", "Nat")):
            with self.subTest(change=new), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                self.fixture(root)
                path = root / "Flapjack/Compiler/Backend/StackLang/Prog.lean"
                path.write_text(path.read_text().replace(old, new))
                self.assertTrue(self.errors(root))

    def test_rejects_shadow_and_unimported_alias(self):
        for declaration in ("abbrev HolProg (width : Nat) := Nat",
                            "abbrev Evil.HolProg (width : Nat) := Nat",
                            "inductive HolInst (width : Nat) [NeZero width] where | fake"):
            with self.subTest(shadow=declaration), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                self.fixture(root)
                path = root / "Flapjack/AliasProbe.lean"
                path.write_text(path.read_text() + "\n" + declaration)
                self.assertTrue(self.errors(root))
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self.fixture(root)
            (root / "Flapjack/AliasProbe.lean").write_text(self.SIGNATURE)
            self.assertTrue(self.errors(root))

    def test_rejects_imported_payload_alias_shadow(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self.fixture(root)
            (root / "Flapjack/Shadow.lean").write_text("abbrev HolInst (width : Nat) := Nat")
            path = root / "Flapjack/AliasProbe.lean"
            path.write_text("import Flapjack.Shadow\n" + path.read_text())
            self.assertTrue(self.errors(root))

    def test_rejects_missing_or_wrong_positive_width(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self.fixture(root)
            for signature in (self.SIGNATURE.replace("[NeZero width]", ""),
                              self.SIGNATURE.replace("[NeZero width]", "[NeZero other]"),
                              self.SIGNATURE.replace("HolProg width", "HolProg 0"),
                              self.SIGNATURE.replace("HolProg width", "Evil.HolProg width"),
                              self.SIGNATURE.replace("(p : HolProg width)",
                                  "(p : Evil.HolProg width) (unrelated : BitVec width)")):
                self.assertTrue(self.errors(root, signature))

    def test_rejects_payload_without_own_word_and_positive_width(self):
        for old, new in (("(value : BitVec width)", "(value : Nat)"),
                         ("inductive HolInst (width : Nat) [NeZero width]", "inductive HolInst (width : Nat)")):
            with self.subTest(change=new), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                self.fixture(root)
                path = root / "Flapjack/Compiler/Encoders/Asm.lean"
                path.write_text(path.read_text().replace(old, new))
                self.assertTrue(self.errors(root))


class WordsAsTypeIndexedBitvecQualifierTest(unittest.TestCase):
    """The word-dimension / FFI-universe translation qualifier."""

    ERRORS = staticmethod(CHECKER["words_as_type_indexed_bitvec_errors"])

    GOOD = (
        "@[hol \"cakeml/pancake/semantics/crepSemScript.sml\" \"evaluate_def\" 240",
        "  (fmap_as_finite_support := [locals, globals, code])",
        "  (words_as_type_indexed_bitvec)]",
        "def evalProg {width : Nat} [NeZero width] {σ : Type}",
        "    (state : CrepSemHOLState width σ) (addr : BitVec width)",
        "    (ffi : HolFfiState σ) : HolWordLab width := HolWordLab.word addr",
        "",
    )

    def test_sites_parses_qualifier(self):
        self.assertEqual(
            list(SITES([
                '@[hol "cakeml/pancake/semantics/crepSemScript.sml" "evaluate_def" 240',
                '  (words_as_type_indexed_bitvec)]',
            ])),
            [(1, "cakeml/pancake/semantics/crepSemScript.sml", "evaluate_def", 240,
              (), (), (), (), False, (), False, True, ())],
        )

    def test_accepts_dimindex_and_universe(self):
        self.assertEqual(self.ERRORS("\n".join(self.GOOD), "evalProg"), [])

    def test_rejects_missing_bitvec(self):
        text = "\n".join(self.GOOD).replace("BitVec", "Word")
        self.assertTrue(any("BitVec" in e for e in self.ERRORS(text, "evalProg")))

    def test_rejects_missing_nezero(self):
        text = "\n".join(self.GOOD).replace("[NeZero width]", "")
        self.assertTrue(any("NeZero" in e for e in self.ERRORS(text, "evalProg")))

    def test_rejects_extra_positivity_hypothesis(self):
        text = "\n".join(self.GOOD).replace(
            "(state : CrepSemHOLState width σ)",
            "(hpos : width ≠ 0) (state : CrepSemHOLState width σ)",
        )
        self.assertTrue(
            any("positivity" in e for e in self.ERRORS(text, "evalProg"))
        )

    def test_rejects_ffi_universe_level_variable(self):
        text = "\n".join(self.GOOD).replace("{σ : Type}", "{σ : Type u}")
        self.assertTrue(
            any("universe-level" in e for e in self.ERRORS(text, "evalProg"))
        )

    def test_rejects_empty_declaration_text(self):
        self.assertTrue(
            any("resolvable" in e for e in self.ERRORS("", "evalProg"))
        )

    def test_accepts_combined_fmap_and_words_qualifiers(self):
        self.assertEqual(self.ERRORS("\n".join(self.GOOD), "evalProg"), [])

    def test_rejects_bitvec_only_in_body(self):
        text = "\n".join(self.GOOD).replace(
            "(addr : BitVec width)",
            "(addr : Nat)",
        ).replace(
            ": HolWordLab width := HolWordLab.word addr",
            ": Nat := addr + (1 : BitVec width).toNat",
        )
        self.assertTrue(any("BitVec" in e for e in self.ERRORS(text, "evalProg")))

    def test_rejects_sort_host_universe(self):
        text = "\n".join(self.GOOD).replace("{σ : Type}", "{σ : Sort u}")
        self.assertTrue(
            any("universe" in e or "Type" in e for e in self.ERRORS(text, "evalProg"))
        )

    def test_rejects_one_le_width_hypothesis(self):
        text = "\n".join(self.GOOD).replace(
            "(state : CrepSemHOLState width σ)",
            "(hpos : 1 ≤ width) (state : CrepSemHOLState width σ)",
        )
        self.assertTrue(
            any("positivity" in e for e in self.ERRORS(text, "evalProg"))
        )


    def test_rejects_direct_bitvec_of_other_width(self):
        # `BitVec 5` next to a `Nat` width binder and an unrelated
        # `[NeZero width]` is not evidence of a `BitVec width` translation.
        text = "\n".join(self.GOOD).replace("(addr : BitVec width)", "(addr : BitVec 5)")
        self.assertTrue(any("BitVec" in e for e in self.ERRORS(text, "evalProg")))

    def test_rejects_direct_nezero_of_other_width(self):
        # `BitVec width` with `[NeZero other]` must not pass: positivity must be
        # discharged for the same width identifier.
        text = "\n".join(self.GOOD).replace("[NeZero width]", "[NeZero other]")
        self.assertTrue(any("BitVec" in e for e in self.ERRORS(text, "evalProg")))

    def test_rejects_second_unconstrained_width(self):
        # A second word dimension must also be bound at a `Nat` width with its
        # own `[NeZero <id>]` discharge.
        text = "\n".join(self.GOOD).replace(
            "(addr : BitVec width)",
            "(addr : BitVec width) (other : BitVec otherWidth)",
        ).replace(
            "{width : Nat} [NeZero width] {σ : Type}",
            "{width : Nat} {otherWidth : Nat} [NeZero width] {σ : Type}",
        )
        self.assertTrue(
            any("otherWidth" in e for e in self.ERRORS(text, "evalProg"))
        )

    def test_rejects_bitvec_zero_beside_good_width(self):
        text = "\n".join(self.GOOD).replace(
            "(addr : BitVec width)",
            "(addr : BitVec width) (zero : BitVec 0)",
        )
        self.assertTrue(
            any("BitVec 0" in e or "positive" in e for e in self.ERRORS(text, "evalProg"))
        )

    def test_rejects_bitvec_zero_as_only_word(self):
        text = "\n".join(self.GOOD).replace("(addr : BitVec width)", "(addr : BitVec 0)")
        self.assertTrue(
            any("BitVec 0" in e or "BitVec" in e for e in self.ERRORS(text, "evalProg"))
        )

    def test_rejects_nezero_zero(self):
        text = "\n".join(self.GOOD).replace(
            "[NeZero width]", "[NeZero width] [NeZero 0]",
        )
        self.assertTrue(
            any("NeZero 0" in e or "positive" in e for e in self.ERRORS(text, "evalProg"))
        )

    def test_rejects_standalone_nezero_zero(self):
        # `[NeZero 0]` with no surrounding width discharge must still be caught
        # by the regex scan; the zero spelling is never a valid positivity
        # instance, so it cannot license a `BitVec width` translation.
        text = "\n".join(self.GOOD).replace("[NeZero width]", "[NeZero 0]")
        self.assertTrue(
            any("positive" in e for e in self.ERRORS(text, "evalProg")),
            self.ERRORS(text, "evalProg"),
        )

    def test_rejects_standalone_nezero_leading_zero(self):
        # A leading-zero literal (`00`) is the same nonpositive dimension as
        # `0`; the regex must not let the extra digit smuggle it through.
        text = "\n".join(self.GOOD).replace("[NeZero width]", "[NeZero 00]")
        self.assertTrue(
            any("positive" in e for e in self.ERRORS(text, "evalProg")),
            self.ERRORS(text, "evalProg"),
        )

    def test_rejects_parenthesized_zero_dimension(self):
        text = "\n".join(self.GOOD).replace(
            "(addr : BitVec width)", "(addr : BitVec width) (leak : BitVec (0))",
        )
        self.assertTrue(
            any("positive width" in e for e in self.ERRORS(text, "evalProg")),
            self.ERRORS(text, "evalProg"),
        )

    def test_rejects_leading_zero_dimension(self):
        text = "\n".join(self.GOOD).replace(
            "(addr : BitVec width)", "(addr : BitVec width) (leak : BitVec 00)",
        )
        self.assertTrue(
            any("positive width" in e for e in self.ERRORS(text, "evalProg")),
            self.ERRORS(text, "evalProg"),
        )

    def test_rejects_arithmetic_dimension(self):
        text = "\n".join(self.GOOD).replace(
            "(addr : BitVec width)",
            "(addr : BitVec width) (leak : BitVec (width - width))",
        )
        self.assertTrue(
            any("positive width identifier" in e for e in self.ERRORS(text, "evalProg")),
            self.ERRORS(text, "evalProg"),
        )

    def test_rejects_nezero_leading_zero(self):
        text = "\n".join(self.GOOD).replace(
            "[NeZero width]", "[NeZero width] [NeZero 00]",
        )
        self.assertTrue(
            any("positive" in e for e in self.ERRORS(text, "evalProg")),
            self.ERRORS(text, "evalProg"),
        )

    def test_rejects_literal_nezero_argument(self):
        text = "\n".join(self.GOOD).replace(
            "[NeZero width]", "[NeZero width] [NeZero 5]",
        )
        self.assertTrue(
            any("NeZero 5" in e for e in self.ERRORS(text, "evalProg")),
            self.ERRORS(text, "evalProg"),
        )

    def test_rejects_compound_nezero_argument(self):
        text = "\n".join(self.GOOD).replace(
            "[NeZero width]", "[NeZero width] [NeZero (width - width)]",
        )
        self.assertTrue(
            any("NeZero (width - width)" in e for e in self.ERRORS(text, "evalProg")),
            self.ERRORS(text, "evalProg"),
        )

    def test_accepts_parenthesized_identifier_dimension(self):
        text = "\n".join(self.GOOD).replace("BitVec width", "BitVec (width)")
        self.assertEqual(self.ERRORS(text, "evalProg"), [])

    def test_rejects_ffi_host_at_type_one(self):
        text = "\n".join(self.GOOD).replace("{σ : Type}", "{σ : Type 1}")
        self.assertTrue(
            any("universe" in e or "Type" in e for e in self.ERRORS(text, "evalProg"))
        )


THEOREM_MAP = runpy.run_path(
    str(Path(__file__).resolve().parents[1] / "check_hol_theorem_map.py")
)


class RealCombinedQualifierFixtureTest(unittest.TestCase):
    """End-to-end positive fixture for the combined fmap+words qualifier.

    The three exact HOL `crepSem` shared-memory ports are committed, real
    declarations carrying both `(fmap_as_finite_support := [locals, globals,
    code])` and `(words_as_type_indexed_bitvec)`. This class checks the real
    declarations through the reference checker and through the theorem-map
    manifest validator, including negatives that omit each qualifier/status.
    """

    MODULE = "Flapjack/Pancake/Semantics/CrepSem/EvaluateHOL.lean"
    MODULE_NAME = "Flapjack.Pancake.Semantics.CrepSem.EvaluateHOL"
    HOL_NAMES = ("sh_mem_load_def", "sh_mem_store_def", "sh_mem_op_def")
    FMAP_FIELDS = ("locals", "globals", "code")

    def _lines(self):
        return (Path(__file__).resolve().parents[2] / self.MODULE).read_text(
            encoding="utf-8"
        ).splitlines()

    def _sites(self, lines):
        found = {}
        for site in SITES(lines):
            if site[2] in self.HOL_NAMES:
                found[site[2]] = site
        return found

    def test_real_declarations_carry_both_qualifiers(self):
        sites = self._sites(self._lines())
        for hol_name in self.HOL_NAMES:
            self.assertIn(hol_name, sites, f"{hol_name} is no longer tagged")
            site = sites[hol_name]
            self.assertEqual(tuple(site[7]), self.FMAP_FIELDS, hol_name)
            self.assertTrue(site[11], f"{hol_name} must carry (words_as_type_indexed_bitvec)")

    def test_real_declarations_pass_reference_checker(self):
        lines = self._lines()
        sites = self._sites(lines)
        self.assertEqual(set(sites), set(self.HOL_NAMES))
        for hol_name, site in sites.items():
            declaration_text = CHECKER["tagged_declaration_text"](lines, site[0])
            self.assertEqual(
                CHECKER["fmap_as_finite_support_errors"](
                    lines, self.FMAP_FIELDS, self.MODULE, declaration_text
                ),
                [],
                hol_name,
            )
            self.assertEqual(
                CHECKER["words_as_type_indexed_bitvec_errors"](
                    declaration_text, hol_name
                ),
                [],
                hol_name,
            )

    def test_real_imported_carrier_only_clauses_pass_checker(self):
        # Skip and Break are currently untagged pending whole-evaluator review;
        # neither signature names a literal `BitVec`. Both still exercise
        # resolution of the imported CrepSemHOLState word carrier.
        lines = self._lines()
        for clause, expected_tag in (("skip", False), ("break", False)):
            name = f"evalCrepSemHOLProgExact_{clause}"
            with self.subTest(clause=clause):
                start = next(
                    (index for index, line in enumerate(lines, start=1)
                     if line.startswith(f"theorem {name}")),
                    None,
                )
                self.assertIsNotNone(start, f"{name} not found")
                preceding = lines[max(0, start - 4):start - 1]
                self.assertEqual(
                    any(
                        line.lstrip().startswith("@[hol")
                        for line in preceding
                    ),
                    expected_tag,
                )
                region = []
                for line in lines[start - 1:]:
                    region.append(line)
                    if ":=" in line:
                        break
                self.assertEqual(
                    CHECKER["words_as_type_indexed_bitvec_errors"](
                        "\n".join(region),
                        name,
                        module=self.MODULE_NAME,
                        root=str(Path(__file__).resolve().parents[2]),
                        lines=lines,
                    ),
                    [],
                )

    def _tagged(self, lines):
        tagged = {}
        for hol_name, site in self._sites(lines).items():
            value = (
                site[1], site[2], site[4], site[5], site[6], site[7],
                site[8], site[9], site[10], site[11],
            )
            tagged[(self.MODULE, self._lean_name(hol_name))] = value
        return tagged

    @staticmethod
    def _lean_name(hol_name):
        return {
            "sh_mem_load_def": "crepShMemLoadExactHOL",
            "sh_mem_store_def": "crepShMemStoreExactHOL",
            "sh_mem_op_def": "crepShMemOpExactHOL",
        }[hol_name]

    def _record(self, hol_name, **overrides):
        record = {
            "hol_path": "cakeml/pancake/semantics/crepSemScript.sml",
            "hol_name": hol_name,
            "lean_path": self.MODULE,
            "lean_name": self._lean_name(hol_name),
            "statement_status": (
                "reviewed_fmap_as_finite_support_words_as_type_indexed_bitvec"
            ),
            "fmap_as_finite_support": list(self.FMAP_FIELDS),
            "words_as_type_indexed_bitvec": True,
            "reviewer": "source comparison of the HOL word/finite-map carriers",
        }
        record.update(overrides)
        return record

    def _errors(self, records, tagged):
        return THEOREM_MAP["validate_inventory"](records, set(), tagged, set())

    def test_manifest_accepts_real_combined_fixture(self):
        lines = self._lines()
        tagged = self._tagged(lines)
        self.assertEqual(
            self._errors([self._record(h) for h in self.HOL_NAMES], tagged), []
        )

    def test_manifest_rejects_real_fixture_omitting_words_qualifier(self):
        lines = self._lines()
        tagged = self._tagged(lines)
        errors = self._errors(
            [self._record(h, words_as_type_indexed_bitvec=False) for h in self.HOL_NAMES],
            tagged,
        )
        self.assertTrue(errors)

    def test_manifest_rejects_real_fixture_omitting_fmap_qualifier(self):
        lines = self._lines()
        tagged = self._tagged(lines)
        errors = self._errors(
            [self._record(h, fmap_as_finite_support=[], words_as_type_indexed_bitvec=False)
             for h in self.HOL_NAMES],
            tagged,
        )
        self.assertTrue(errors)

    def test_manifest_rejects_real_fixture_with_single_status(self):
        lines = self._lines()
        tagged = self._tagged(lines)
        for status in (
            "reviewed_fmap_as_finite_support",
            "reviewed_words_as_type_indexed_bitvec",
        ):
            errors = self._errors(
                [self._record(h, statement_status=status) for h in self.HOL_NAMES],
                tagged,
            )
            self.assertTrue(errors, status)

    def test_manifest_rejects_real_fixture_omitting_combined_status(self):
        lines = self._lines()
        tagged = self._tagged(lines)
        errors = self._errors(
            [self._record(h, statement_status="reviewed_exact") for h in self.HOL_NAMES],
            tagged,
        )
        self.assertTrue(errors)


class WordsCarrierResolutionTest(unittest.TestCase):
    """Carrier resolution for `(words_as_type_indexed_bitvec)`.

    A tagged signature may omit a literal `BitVec` when it names a reviewed
    width-indexed structure or inductive carrier whose fields/constructor
    payloads include `BitVec width` and whose declaration retains
    `[NeZero width]`. The carrier is resolved from its declaration (local or
    imported), never from its name alone.
    """

    MODULE = "Flapjack/PanToCrep/CarrierExact.lean"
    MODULE_NAME = "Flapjack.PanToCrep.CarrierExact"

    def _checker_globals(self):
        return CHECKER["words_as_type_indexed_bitvec_errors"].__globals__

    def _run(self, owner_text, consumer_text):
        checker_globals = self._checker_globals()
        original_root = checker_globals["ROOT"]
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            owner = root / "Flapjack" / "PanToCrep" / "ContextExact.lean"
            consumer = root / self.MODULE
            owner.parent.mkdir(parents=True)
            if owner_text is not None:
                owner.write_text(owner_text, encoding="utf-8")
            consumer.write_text(consumer_text, encoding="utf-8")
            checker_globals["ROOT"] = root
            try:
                self.imported_headers = CHECKER["imported_structure_headers"](
                    self.MODULE_NAME, str(root)
                )
                self.imported_field_types = CHECKER[
                    "imported_structure_field_types"
                ](self.MODULE_NAME, str(root))
                self.imported_owners = CHECKER["imported_structure_owners"](
                    self.MODULE_NAME, str(root)
                )
                lines = consumer_text.splitlines()
                attribute_start = next(
                    (
                        index
                        for index, line in enumerate(lines)
                        if "@[hol" in line
                    ),
                    0,
                )
                declaration_text = CHECKER["tagged_declaration_text"](
                    lines, attribute_start
                )
                return CHECKER["words_as_type_indexed_bitvec_errors"](
                    declaration_text,
                    "evalProg",
                    module=self.MODULE_NAME,
                    root=str(root),
                    lines=lines,
                )
            finally:
                checker_globals["ROOT"] = original_root

    OWNER = "\n".join([
        "structure CrepStateExact (width : Nat) [NeZero width] (ffiState : Type) where",
        "  locals : HolFiniteMapExact Nat (HolWordLab width)",
        "  memory : BitVec width → HolWordLab width",
        "  baseAddr : BitVec width",
    ])

    CONSUMER = "\n".join([
        "import Flapjack.PanToCrep.ContextExact",
        '@[hol "cakeml/pancake/semantics/crepSemScript.sml" "evaluate_def" 240',
        "  (fmap_as_finite_support := [locals])",
        "  (words_as_type_indexed_bitvec)]",
        "def evalProg {width : Nat} [NeZero width] {σ : Type}",
        "    (state : CrepStateExact width σ) : Nat := width",
    ])

    def test_accepts_imported_carrier_with_bitvec_fields(self):
        self.assertEqual(self._run(self.OWNER, self.CONSUMER), [])
        self.assertIn("CrepStateExact", self.imported_headers)
        self.assertIn("CrepStateExact", self.imported_field_types)
        self.assertIn("CrepStateExact", self.imported_owners)

    def test_accepts_local_carrier_with_bitvec_fields(self):
        local = "\n".join([
            self.OWNER,
            '@[hol "cakeml/pancake/semantics/crepSemScript.sml" "evaluate_def" 240',
            "  (fmap_as_finite_support := [locals])",
            "  (words_as_type_indexed_bitvec)]",
            "def evalProg {width : Nat} [NeZero width] {σ : Type}",
            "    (state : CrepStateExact width σ) : Nat := width",
        ])
        self.assertEqual(self._run(None, local), [])

    def test_accepts_imported_inductive_carrier_with_bitvec_payload(self):
        owner = "\n".join([
            "inductive CrepProgExact (width : Nat) [NeZero width] where",
            "  | skip",
            "  | raise (value : BitVec width)",
        ])
        consumer = "\n".join([
            "import Flapjack.PanToCrep.ContextExact",
            '@[hol "cakeml/pancake/crep_inlineScript.sml" "unreach_elim_def"',
            "  (words_as_type_indexed_bitvec)]",
            "def unreachExact {width : Nat} [NeZero width]",
            "    (program : CrepProgExact width) : Nat := width",
        ])
        self.assertEqual(self._run(owner, consumer), [])

    def test_accepts_hol_ast_carrier_reaching_nested_bitvec_payload(self):
        owner = "\n".join([
            '@[hol "cakeml/pancake/panLangScript.sml" "decl"]',
            "inductive DeclHOL (width : Nat) [NeZero width] where",
            "  | decl (value : ExpHOL width)",
            '@[hol "cakeml/pancake/panLangScript.sml" "exp"]',
            "inductive ExpHOL (width : Nat) [NeZero width] where",
            "  | const (value : BitVec width)",
        ])
        consumer = "\n".join([
            "import Flapjack.PanToCrep.ContextExact",
            '@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "compile_def"',
            "  (words_as_type_indexed_bitvec)]",
            "def compileExact {width : Nat} [NeZero width]",
            "    (declarations : List (DeclHOL width)) : Nat := width",
        ])
        self.assertEqual(self._run(owner, consumer), [])

    def test_rejects_untagged_intermediate_ast_carrier(self):
        owner = "\n".join([
            '@[hol "cakeml/pancake/panLangScript.sml" "decl"]',
            "inductive DeclHOL (width : Nat) [NeZero width] where",
            "  | decl (value : ExpHOL width)",
            "inductive ExpHOL (width : Nat) [NeZero width] where",
            "  | const (value : BitVec width)",
        ])
        consumer = "\n".join([
            "import Flapjack.PanToCrep.ContextExact",
            '@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "compile_def"',
            "  (words_as_type_indexed_bitvec)]",
            "def compileExact {width : Nat} [NeZero width]",
            "    (declarations : List (DeclHOL width)) : Nat := width",
        ])
        errors = self._run(owner, consumer)
        self.assertTrue(any("BitVec" in error for error in errors), errors)

    VALUE_HOL_OWNER = "\n".join([
        "inductive HolWordLab (width : Nat) [NeZero width] where",
        "  | word (value : BitVec width)",
        "inductive ValueHOL (width : Nat) [NeZero width] where",
        "  | val (value : HolWordLab width)",
        "  | rStruct (fields : List (ValueHOL width))",
        "  | nStruct (name : MlS) (fields : List (MlS × ValueHOL width))",
    ])

    VALUE_HOL_CONSUMER = "\n".join([
        "import Flapjack.PanToCrep.ContextExact",
        '@[hol "cakeml/pancake/semantics/panSemScript.sml" "flatten_def"',
        "  (words_as_type_indexed_bitvec)]",
        "def flattenExact {width : Nat} [NeZero width]",
        "    (value : ValueHOL width) : Nat := width",
    ])

    def test_accepts_value_hol_only_through_resolved_word_lab_payload(self):
        self.assertEqual(
            self._run(self.VALUE_HOL_OWNER, self.VALUE_HOL_CONSUMER), []
        )

    def test_rejects_value_hol_without_width_indexed_word_payload(self):
        owner = self.VALUE_HOL_OWNER.replace(
            "  | val (value : HolWordLab width)",
            "  | val (value : Nat)",
        )
        errors = self._run(owner, self.VALUE_HOL_CONSUMER)
        self.assertTrue(any("BitVec" in error for error in errors), errors)

    def test_rejects_value_hol_if_word_lab_payload_is_not_positive_bitvec(self):
        owner = self.VALUE_HOL_OWNER.replace(
            "inductive HolWordLab (width : Nat) [NeZero width] where",
            "inductive HolWordLab (width : Nat) where",
        )
        errors = self._run(owner, self.VALUE_HOL_CONSUMER)
        self.assertTrue(
            any("positive width" in error or "NeZero" in error for error in errors),
            errors,
        )

    def test_rejects_unrelated_aggregate_with_word_lab_field(self):
        owner = self.VALUE_HOL_OWNER.replace("ValueHOL", "OtherValue")
        consumer = self.VALUE_HOL_CONSUMER.replace("ValueHOL", "OtherValue")
        errors = self._run(owner, consumer)
        self.assertTrue(any("BitVec" in error for error in errors), errors)

    def test_rejects_inductive_carrier_without_same_owner_word_payload(self):
        owner = "\n".join([
            "inductive CrepProgExact (width : Nat) [NeZero width] where",
            "  | skip",
            "  | clock (value : Nat)",
        ])
        consumer = "\n".join([
            "import Flapjack.PanToCrep.ContextExact",
            '@[hol "cakeml/pancake/crep_inlineScript.sml" "unreach_elim_def"',
            "  (words_as_type_indexed_bitvec)]",
            "def unreachExact {width : Nat} [NeZero width]",
            "    (program : CrepProgExact width) : Nat := width",
        ])
        errors = self._run(owner, consumer)
        self.assertTrue(any("BitVec" in error for error in errors), errors)


    def test_rejects_fake_carrier_without_bitvec_field(self):
        owner = "\n".join([
            "structure CrepStateExact (width : Nat) [NeZero width] (ffiState : Type) where",
            "  locals : HolFiniteMapExact Nat (HolWordLab width)",
            "  clock : Nat",
        ])
        errors = self._run(owner, self.CONSUMER)
        self.assertTrue(any("BitVec" in e for e in errors), errors)

    def test_rejects_carrier_missing_positivity(self):
        owner = "\n".join([
            "structure CrepStateExact (width : Nat) (ffiState : Type) where",
            "  locals : HolFiniteMapExact Nat (HolWordLab width)",
            "  memory : BitVec width → HolWordLab width",
        ])
        consumer = self.CONSUMER.replace(" [NeZero width]", "")
        errors = self._run(owner, consumer)
        self.assertTrue(any("NeZero" in e for e in errors), errors)

    def test_rejects_carrier_name_not_declared(self):
        owner = "\n".join([
            "structure SomethingElse (width : Nat) [NeZero width] where",
            "  memory : BitVec width → Nat",
        ])
        errors = self._run(owner, self.CONSUMER)
        self.assertTrue(any("BitVec" in e for e in errors), errors)

    def test_rejects_carrier_width_field_without_width_variable(self):
        owner = "\n".join([
            "structure CrepStateExact (width : Nat) [NeZero width] (ffiState : Type) where",
            "  locals : HolFiniteMapExact Nat (HolWordLab width)",
            "  tag : BitVec 5",
        ])
        errors = self._run(owner, self.CONSUMER)
        self.assertTrue(any("BitVec" in e for e in errors), errors)

    def test_rejects_owner_header_nezero_different_width(self):
        # The owner's header discharges a DIFFERENT width identifier, so the
        # caller's own `[NeZero width]` must not substitute for carrier
        # positivity.
        owner = "\n".join([
            "structure CrepStateExact (width : Nat) [NeZero other] (ffiState : Type) where",
            "  locals : HolFiniteMapExact Nat (HolWordLab width)",
            "  memory : BitVec width → HolWordLab width",
        ])
        errors = self._run(owner, self.CONSUMER)
        self.assertTrue(any("BitVec" in e for e in errors), errors)

    def test_rejects_field_bitvec_of_other_width(self):
        # A field mentioning `BitVec` and the width token separately (here
        # `BitVec 5 × HolWordLab width`) is not an actual `BitVec width` field.
        owner = "\n".join([
            "structure CrepStateExact (width : Nat) [NeZero width] (ffiState : Type) where",
            "  locals : HolFiniteMapExact Nat (HolWordLab width)",
            "  memory : BitVec 5 × HolWordLab width",
        ])
        errors = self._run(owner, self.CONSUMER)
        self.assertTrue(any("BitVec" in e for e in errors), errors)

    def test_accepts_carrier_field_via_word_abbrev(self):
        # A reviewed word abbreviation such as `RiscV.Word width` denotes the
        # standard `BitVec width` translation of HOL `'a word`, so a carrier
        # typed through the abbrev must satisfy the qualifier.
        owner = "\n".join([
            "structure CrepStateExact (width : Nat) [NeZero width] (ffiState : Type) where",
            "  locals : HolFiniteMapExact Nat (HolWordLab width)",
            "  memory : RiscV.Word width → HolWordLab width",
            "  baseAddr : RiscV.Word width",
        ])
        self.assertEqual(self._run(owner, self.CONSUMER), [])

    def test_rejects_carrier_word_abbrev_of_other_width(self):
        # `RiscV.Word 5` is not a word field at the carrier's width identifier.
        owner = "\n".join([
            "structure CrepStateExact (width : Nat) [NeZero width] (ffiState : Type) where",
            "  locals : HolFiniteMapExact Nat (HolWordLab width)",
            "  memory : RiscV.Word 5 → HolWordLab width",
        ])
        errors = self._run(owner, self.CONSUMER)
        self.assertTrue(any("BitVec" in e for e in errors), errors)

    def test_rejects_ambiguous_owners_borrowing_cross_owner_evidence(self):
        # The imported owner has `[NeZero width]` but no `BitVec width` field;
        # the local same-named shadow has a `BitVec width` field but no
        # positivity. Pooling the two owners' evidence would wrongly accept the
        # tag, so the name is ambiguous and must be rejected.
        owner = "\n".join([
            "structure CrepStateExact (width : Nat) [NeZero width] (ffiState : Type) where",
            "  locals : HolFiniteMapExact Nat (HolWordLab width)",
            "  clock : Nat",
        ])
        consumer = "\n".join([
            "import Flapjack.PanToCrep.ContextExact",
            "structure CrepStateExact (width : Nat) (ffiState : Type) where",
            "  locals : HolFiniteMapExact Nat (HolWordLab width)",
            "  memory : BitVec width → HolWordLab width",
            '@[hol "cakeml/pancake/semantics/crepSemScript.sml" "evaluate_def" 240',
            "  (fmap_as_finite_support := [locals])",
            "  (words_as_type_indexed_bitvec)]",
            "def evalProg {width : Nat} [NeZero width] {σ : Type}",
            "    (state : CrepStateExact width σ) : Nat := width",
        ])
        errors = self._run(owner, consumer)
        self.assertTrue(
            any("ambiguous same-named owners" in e for e in errors), errors
        )

    def test_rejects_ambiguous_owners_without_positivity(self):
        # Both owners are same-named with `BitVec width` fields, but only the
        # local shadow retains `[NeZero width]`; no single owner supplies both
        # and the name is ambiguous.
        owner = "\n".join([
            "structure CrepStateExact (width : Nat) (ffiState : Type) where",
            "  locals : HolFiniteMapExact Nat (HolWordLab width)",
            "  memory : BitVec width → HolWordLab width",
        ])
        consumer = "\n".join([
            "import Flapjack.PanToCrep.ContextExact",
            "structure CrepStateExact (width : Nat) [NeZero width] (ffiState : Type) where",
            "  locals : HolFiniteMapExact Nat (HolWordLab width)",
            "  memory : BitVec width → HolWordLab width",
            '@[hol "cakeml/pancake/semantics/crepSemScript.sml" "evaluate_def" 240',
            "  (fmap_as_finite_support := [locals])",
            "  (words_as_type_indexed_bitvec)]",
            "def evalProg {width : Nat} [NeZero width] {σ : Type}",
            "    (state : CrepStateExact width σ) : Nat := width",
        ])
        errors = self._run(owner, consumer)
        self.assertTrue(
            any("ambiguous same-named owners" in e for e in errors), errors
        )


class RealCrepPropsWordCarrierResolutionTest(unittest.TestCase):
    """The real CrepProps imports must resolve the exact state carrier."""

    MODULE = "Flapjack/Pancake/Semantics/CrepProps.lean"
    MODULE_NAME = "Flapjack.Pancake.Semantics.CrepProps"
    HOL_NAMES = {
        "dec_clock_simp",
        "empty_locals_simp",
        "FLOOKUP_set_globals",
        "eval_upd_clock_eq",
        "update_locals_not_vars_eval_eq",
    }

    def test_real_imported_crep_state_resolves_for_five_tags(self):
        root = Path(__file__).resolve().parents[2]
        lines = (root / self.MODULE).read_text(encoding="utf-8").splitlines()
        sites = {site[2]: site for site in SITES(lines) if site[2] in self.HOL_NAMES}
        self.assertEqual(set(sites), self.HOL_NAMES)
        for hol_name, site in sites.items():
            declaration = CHECKER["tagged_declaration_text"](lines, site[0])
            self.assertEqual(
                CHECKER["words_as_type_indexed_bitvec_errors"](
                    declaration,
                    hol_name,
                    module=self.MODULE_NAME,
                    root=str(root),
                    lines=lines,
                ),
                [],
                hol_name,
            )


if __name__ == "__main__":
    unittest.main()
