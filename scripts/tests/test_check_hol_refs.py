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


class HolAttributeSitesTest(unittest.TestCase):
    def test_single_line(self):
        self.assertEqual(
            list(SITES(['@[hol "cakeml/pancake/pan_globalsScript.sml" "compile_top_def"]'])),
            [(1, "cakeml/pancake/pan_globalsScript.sml", "compile_top_def", None, (), (), (), (), False, (), False)],
        )

    def test_multiline(self):
        self.assertEqual(
            list(SITES([
                '@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml"',
                '  "compile_top_shape_wf"]',
                'theorem compileTopShapeWf : True := trivial',
            ])),
            [(1, "cakeml/pancake/proofs/pan_globalsProofScript.sml",
              "compile_top_shape_wf", None, (), (), (), (), False, (), False)],
        )

    def test_comments_do_not_count(self):
        self.assertEqual(
            list(SITES([
                '/- @[hol "cakeml/pancake/pan_globalsScript.sml" "bad"] -/',
                '-- @[hol "cakeml/pancake/pan_globalsScript.sml" "bad"]',
                '@[hol "cakeml/pancake/pan_globalsScript.sml" "compile_top_def"]',
            ])),
            [(3, "cakeml/pancake/pan_globalsScript.sml", "compile_top_def", None, (), (), (), (), False, (), False)],
        )

    def test_source_line(self):
        self.assertEqual(
            list(SITES(['@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml"',
                        '  "locals_rel_wf_shape" 2345]'])),
            [(1, "cakeml/pancake/proofs/pan_to_crepProofScript.sml",
              "locals_rel_wf_shape", 2345, (), (), (), (), False, (), False)],
        )

    def test_list_as_array_fields(self):
        self.assertEqual(
            list(SITES([
                '@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml"',
                '  "dec_deg_def" (list_as_array := [degrees, moves])]'
            ])),
            [(1, "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml",
              "dec_deg_def", None, ("degrees", "moves"), (), (), (), False, (), False)],
        )

    def test_names_as_string_and_boundary_qualifiers(self):
        self.assertEqual(
            list(SITES([
                '@[hol "cakeml/pancake/panLangScript.sml" "varname"',
                '  (names_as_string := [name, generated])',
                '  (names_as_string_boundary := [generated])]',
            ])),
            [(1, "cakeml/pancake/panLangScript.sml", "varname", None,
              (), ("name", "generated"), ("generated",), (), False, (), False)],
        )

    def test_fmap_as_finite_support_fields(self):
        self.assertEqual(
            list(SITES([
                '@[hol "cakeml/pancake/semantics/panSemScript.sml" "set_var_def"',
                '  (fmap_as_finite_support := [locals, globals])]'
            ])),
            [(1, "cakeml/pancake/semantics/panSemScript.sml",
              "set_var_def", None, (), (), (), ("locals", "globals"), False, (), False)],
        )

    def test_fmap_as_finite_support_result_qualifier(self):
        self.assertEqual(
            list(SITES([
                '@[hol "cakeml/pancake/pan_to_crepScript.sml" "get_eids_from_decls_def"',
                '  (fmap_as_finite_support_result)]'
            ])),
            [(1, "cakeml/pancake/pan_to_crepScript.sml",
              "get_eids_from_decls_def", None, (), (), (), (), True, (), False)],
        )

    def test_fmap_as_finite_support_relation_qualifier(self):
        self.assertEqual(
            list(SITES([
                '@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "state_rel_def"',
                '  (fmap_as_finite_support_relation := [PanSemStateFiniteExact.globals, CrepSemHOLState.locals])]'
            ])),
            [(1, "cakeml/pancake/proofs/pan_to_crepProofScript.sml",
              "state_rel_def", None, (), (), (), (), False,
              (("PanSemStateFiniteExact", "globals"), ("CrepSemHOLState", "locals")), False)],
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
              "slc_tlc_rw", None, (), (), (), (), False, (), True)],
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


if __name__ == "__main__":
    unittest.main()
