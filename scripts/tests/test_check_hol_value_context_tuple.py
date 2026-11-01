"""Regression tests for the proposed value-context finite-map tuple gate."""

import runpy
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
CHECK = runpy.run_path(str(ROOT / "scripts/check-hol-refs.py"))["fmap_value_context_tuple_errors"]
SOURCE = (ROOT / "Flapjack/Compiler/Backend/DataToWord/Proofs/Memory/ValueInv.lean").read_text()
HOL = ("cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml", "v_inv_ck")
POSITIONS = ("component_2", "component_3")


class ValueContextTupleQualifierTest(unittest.TestCase):
    def check(self, source=SOURCE, positions=POSITIONS, hol=HOL):
        declaration = source[source.index("inductive ClockValueInv"):]
        return CHECK(source.splitlines(), declaration, positions, hol)

    def test_actual_canonical_carrier_and_witnesses(self):
        self.assertEqual(self.check(), [])

    def test_source_and_both_positions_are_required(self):
        self.assertTrue(self.check(positions=("component_2",)))
        self.assertTrue(self.check(positions=("component_2", "component_2")))
        self.assertTrue(self.check(hol=(HOL[0], "v_inv_eq")))

    def test_raw_or_omitted_map_slot_is_rejected(self):
        alias = "HeapAddress (WordLocW width) × HolFiniteMapExact Nat Nat × HolFiniteMapExact Nat Nat × ValueHeap width"
        self.assertIn(alias, SOURCE)
        self.assertTrue(self.check(SOURCE.replace(alias, alias.replace(
            "HolFiniteMapExact Nat Nat", "(Nat → Option Nat)", 1))))
        self.assertTrue(self.check(SOURCE.replace(alias, alias.replace(
            " × HolFiniteMapExact Nat Nat", "", 1))))

    def test_raw_lookup_alias_must_keep_both_slots(self):
        raw = "HeapAddress (WordLocW width) × (Nat → Option Nat) × (Nat → Option Nat) × ValueHeap width"
        self.assertIn(raw, SOURCE)
        self.assertTrue(self.check(SOURCE.replace(raw, raw.replace("(Nat → Option Nat)", "Nat", 1))))

    def test_rejects_extra_context_alias(self):
        self.assertTrue(self.check(SOURCE + "\nabbrev ValueContext := Nat\n"))

    def test_rejects_wrong_signature(self):
        self.assertTrue(self.check(SOURCE.replace(
            "Nat → Config → Value → Spt (BvlSem.Ref Value) → ValueContext width → Prop where",
            "Nat → Config → Value → Spt (BvlSem.Ref Value) → ValueHeap width → Prop where", 1)))

    def test_rejects_discarded_map_and_decoy_witness(self):
        body = "(context.1, context.2.1.lookup, context.2.2.1.lookup, context.2.2.2)"
        changed = SOURCE.replace(body, "(context.1, context.2.1.lookup, context.2.1.lookup, context.2.2.2)", 1)
        self.assertTrue(self.check(changed + "\n-- decoy\ndef decoy := " + body + "\n"))

    def test_rejects_swapped_reconstruction_and_duplicate_witness(self):
        body = "⟨context.2.2.1, secondFinite⟩"
        self.assertIn(body, SOURCE)
        self.assertTrue(self.check(SOURCE.replace(body, "⟨context.2.1, firstFinite⟩", 1)))
        self.assertTrue(self.check(SOURCE + "\ntheorem holFmapAsFiniteSupportTupleWitness : True := by trivial\n"))

    def test_rejects_missing_or_vacuous_roundtrip(self):
        self.assertTrue(self.check(SOURCE.replace("theorem holFmapAsFiniteSupportTupleWitness",
                                                  "theorem missingTupleWitness", 1)))
        self.assertTrue(self.check(SOURCE.replace(
            "valueContextOfLookups (valueContextToLookups context)\n      context.2.1.finiteSupport context.2.2.1.finiteSupport = context",
            "context = context", 1)))

    def test_rejects_witness_with_extra_premise(self):
        self.assertTrue(self.check(SOURCE.replace(
            "(context : ValueContext width) :\n    valueContextOfLookups",
            "(context : ValueContext width) (h : False) :\n    valueContextOfLookups", 1)))

    def test_rejects_ambient_assumptions(self):
        self.assertTrue(self.check(SOURCE.replace("mutual\n", "variable (h : False)\ninclude h\nmutual\n", 1)))


if __name__ == "__main__":
    unittest.main()
