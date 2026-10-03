"""Fail-closed tests for the narrowly approved gc predicate alias inheritance."""
import runpy
import json
import tempfile
import unittest
from pathlib import Path

CHECKER = runpy.run_path(str(Path(__file__).resolve().parents[1] / "check-hol-refs.py"))
OWNER = "Flapjack.Compiler.Backend.Semantics.WordSem.State"
TAG = '@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "gc_fun_ok_def" (fmap_as_finite_support_function := [argument_4, result_3]) (words_as_type_indexed_bitvec)]'
CONST_REFERENCE = ("cakeml/compiler/backend/proofs/word_simpProofScript.sml", "gc_fun_const_ok_def")
CONST_TAG = TAG.replace("cakeml/compiler/backend/semantics/wordPropsScript.sml",
                        CONST_REFERENCE[0]).replace('"gc_fun_ok_def"', '"gc_fun_const_ok_def"')
PREDICATE = "def gcOk {width : Nat} [NeZero width] (f : WordSemGcFun width) : Prop := True"
ALIAS = """@[hol "cakeml/compiler/backend/semantics/wordSemScript.sml" "gc_fun_type" 193
(fmap_as_finite_support_function := [argument_4, result_3]) (words_as_type_indexed_bitvec)]
abbrev WordSemGcFun (width : Nat) [NeZero width] : Type :=
(List (WordLocW width) × (BitVec width → WordLocW width) × (BitVec width → Bool) ×
HolFiniteMapExact WordStoreHOL (WordLocW width)) →
Option (List (WordLocW width) × (BitVec width → WordLocW width) ×
HolFiniteMapExact WordStoreHOL (WordLocW width))
theorem holFmapAsFiniteSupportWitness : True := by trivial
"""

class GcPredicateInheritanceTest(unittest.TestCase):
    def check(self, alias=ALIAS, predicate=PREDICATE, positions=("argument_4", "result_3"),
              reference=("cakeml/compiler/backend/semantics/wordPropsScript.sml", "gc_fun_ok_def"),
              extra="", words=False, reviewed=True, words_qualifier=True, tag=TAG):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "docs").mkdir()
            (root / "docs/HOL-THEOREM-MAP.json").write_text(json.dumps([{
                "lean_path": OWNER.replace(".", "/") + ".lean",
                "lean_name": "WordSemGcFun",
                "hol_path": "cakeml/compiler/backend/semantics/wordSemScript.sml",
                "hol_name": "gc_fun_type",
                "statement_status": ("reviewed_fmap_as_finite_support_function_words_as_type_indexed_bitvec"
                                     if reviewed else "pending_statement_review"),
                "fmap_as_finite_support_function": ["argument_4", "result_3"],
                "words_as_type_indexed_bitvec": True,
            }]))
            owner = root / (OWNER.replace(".", "/") + ".lean")
            owner.parent.mkdir(parents=True)
            owner.write_text(alias)
            source = "import " + OWNER + "\n" + extra + "\n" + tag + "\n" + predicate
            (root / "Fixture.lean").write_text(source)
            if words:
                return CHECKER["words_as_type_indexed_bitvec_errors"](
                    tag + "\n" + predicate, "gcOk", "Fixture", str(root),
                    source.splitlines())
            return CHECKER["fmap_as_finite_support_function_errors"](
                source.splitlines(), predicate, "gcOk", positions, module="Fixture",
                root=str(root), hol_reference=reference, words_bitvec=words_qualifier)

    def test_accepts_existing_exact_alias(self):
        self.assertEqual(self.check(), [])
        self.assertEqual(self.check(words=True), [])

    def test_rejects_missing_canonical_alias_witness(self):
        self.assertTrue(self.check(alias=ALIAS.split("theorem")[0]))

    def test_rejects_unreviewed_alias(self):
        self.assertTrue(self.check(reviewed=False))

    def test_requires_both_inherited_qualifiers(self):
        self.assertTrue(self.check(words_qualifier=False))

    def test_word_inheritance_rejects_shadow_and_changed_alias(self):
        self.assertTrue(self.check(extra="abbrev WordSemGcFun := Nat", words=True))
        self.assertTrue(self.check(alias=ALIAS.replace("BitVec width → Bool",
                                                      "BitVec 64 → Bool"), words=True))

    def test_rejects_other_predicate_reference(self):
        self.assertTrue(self.check(reference=("cakeml/x.sml", "another_def")))

    def test_rejects_wrong_slots(self):
        self.assertTrue(self.check(positions=("argument_3", "result_3")))

    def test_rejects_raw_map_and_changed_word_payload(self):
        for alias in (ALIAS.replace("HolFiniteMapExact WordStoreHOL (WordLocW width)",
                                    "WordStoreHOL → Option (WordLocW width)"),
                      ALIAS.replace("BitVec width → Bool", "BitVec 64 → Bool")):
            with self.subTest(alias=alias):
                self.assertTrue(self.check(alias=alias))

    def test_rejects_shadow_owner(self):
        self.assertTrue(self.check(extra="abbrev WordSemGcFun := Nat"))

    def test_rejects_missing_alias_qualification(self):
        self.assertTrue(self.check(alias=ALIAS.replace("(words_as_type_indexed_bitvec)", "")))

    def test_rejects_extra_or_ambient_premises(self):
        self.assertTrue(self.check(predicate=PREDICATE.replace(" : Prop", " (h : True) : Prop")))
        self.assertTrue(self.check(extra="variable (h : True)"))

    def test_rejects_missing_or_wrong_positivity(self):
        for predicate in (PREDICATE.replace("[NeZero width]", ""),
                          PREDICATE.replace("[NeZero width]", "[NeZero 0]")):
            self.assertTrue(self.check(predicate=predicate))

    def const_check(self, **kwargs):
        kwargs.setdefault("reference", CONST_REFERENCE)
        return self.check(tag=CONST_TAG, **kwargs)

    def test_accepts_word_simp_gc_fun_const_ok_at_both_guards(self):
        self.assertEqual(self.const_check(), [])
        self.assertEqual(self.const_check(words=True), [])

    def test_gc_fun_const_ok_keeps_slot_carrier_and_binder_guards(self):
        self.assertTrue(self.const_check(positions=("argument_3", "result_3")))
        self.assertTrue(self.const_check(words_qualifier=False))
        self.assertTrue(self.const_check(reviewed=False))
        self.assertTrue(self.const_check(extra="abbrev WordSemGcFun := Nat"))
        self.assertTrue(self.const_check(extra="abbrev WordSemGcFun := Nat", words=True))
        self.assertTrue(self.const_check(extra="variable (h : True)"))
        self.assertTrue(self.const_check(
            predicate=PREDICATE.replace("[NeZero width]", "")))
        self.assertTrue(self.const_check(
            predicate=PREDICATE.replace("[NeZero width]", "[NeZero 0]")))

    def test_rejects_other_word_simp_predicates(self):
        other = ("cakeml/compiler/backend/proofs/word_simpProofScript.sml", "gc_fun_sf_gc_consts")
        tag = CONST_TAG.replace('"gc_fun_const_ok_def"', '"gc_fun_sf_gc_consts"')
        self.assertTrue(self.check(tag=tag, reference=other))
        self.assertTrue(self.check(tag=tag, reference=other, words=True))

    def test_rejects_multi_argument_gc_theorem_signature(self):
        multi = ("def gcOk {width : Nat} [NeZero width] (f : WordSemGcFun width) "
                 "(s : List Nat) : Prop := True")
        self.assertTrue(self.const_check(predicate=multi))
        self.assertTrue(self.const_check(predicate=multi, words=True))
