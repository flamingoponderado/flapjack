"""Guards for the reviewed unused HOL witness qualifier."""
import runpy
import unittest
from pathlib import Path

SCRIPTS = Path(__file__).resolve().parents[1]
ROOT = SCRIPTS.parent
REFS = runpy.run_path(str(SCRIPTS / "check-hol-refs.py"))
EXPORT = runpy.run_path(str(SCRIPTS / "check_hol_ref_export.py"))
MAP = runpy.run_path(str(SCRIPTS / "check_hol_theorem_map.py"))


class ConsAltExistentialInhabitantsTest(unittest.TestCase):
    def test_parser_rejects_repeated_qualifiers(self):
        qualifier = "(hol_unused_existential_inhabitants := [β._unused])"
        source = "@[hol \"cake.sml\" \"test\" " + qualifier + "]"
        scan = REFS["hol_attribute_sites"]
        self.assertEqual(list(scan([source], include_hol_unused_existential_inhabitants=True))[0][-1], ("β._unused",))
        repeated = source.replace(qualifier, qualifier + " " + qualifier)
        self.assertEqual(list(scan([repeated], include_hol_unused_existential_inhabitants=True))[0][-1], ("",))

    def test_header_rejects_extra_premises_and_changed_conclusions(self):
        source = (ROOT / "Flapjack/Compiler/Backend/DataToWord/Proofs/Memory/Relation/ConsAltWritten.lean").read_text()
        check = REFS["cons_alt_existential_header_errors"]
        self.assertEqual(check(source), [])
        self.assertTrue(check(source.replace("[Nonempty β]", "[Nonempty β] (extra : False)")))
        self.assertTrue(check(source.replace("ws.length < sp", "ws.length ≤ sp")))
        self.assertTrue(check(source.replace("ts + 1", "ts + 2")))
        self.assertTrue(check(source.replace("namespace Flapjack", "variable (extra : False)\nnamespace Flapjack", 1)))

    def test_export_metadata_must_match_both_ways(self):
        fields = ["β._unused"]
        manifest = {"hol_path": "cake.sml", "hol_name": "example", "lean_path": "Flapjack/Example.lean",
                    "lean_name": "example", "statement_status": "reviewed_exact",
                    "hol_unused_existential_inhabitants": fields}
        exported = {"hol_path": "cake.sml", "hol_name": "example", "lean_name": "Example.example", "qualifiers": {}}
        with self.assertRaises(ValueError):
            EXPORT["check_records"]([manifest], [exported])
        del manifest["hol_unused_existential_inhabitants"]
        exported["qualifiers"]["hol_unused_existential_inhabitants"] = fields
        with self.assertRaises(ValueError):
            EXPORT["check_records"]([manifest], [exported])

    def test_byte_array_header_rejects_witness_and_statement_changes(self):
        source = (ROOT / "Flapjack/Compiler/Backend/DataToWord/Proofs/Memory/Relation/ByteArrayImp.lean").read_text()
        check = REFS["byte_array_existential_header_errors"]
        self.assertEqual(check(source), [])
        self.assertTrue(check(source.replace("[Nonempty β]", "[Nonempty β] (extra : False)")))
        self.assertTrue(check(source.replace("(_unused : β)", "(_unused : Unit)")))
        self.assertTrue(check(source.replace("i < bytes.length", "i ≤ bytes.length")))
        self.assertTrue(check(source.replace("namespace Flapjack", "variable (extra : False)\nnamespace Flapjack", 1)))

    def test_byte_array_manifest_requires_exact_site(self):
        hol = "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml"
        lean = "Flapjack/Compiler/Backend/DataToWord/Proofs/Memory/Relation/ByteArrayImp.lean"
        tag = (hol, "memory_rel_ByteArray_IMP", (), (), (), (), False, (("store", ""),), (), True, (), (),
               None, (), (), False, False, (), (), (), (), (), (), (), (), (), (), (), (), (), (), ("β._unused",))
        record = {"hol_path": hol, "hol_name": "memory_rel_ByteArray_IMP", "lean_path": lean,
                  "lean_name": "memoryRel_byteArrayImp",
                  "statement_status": "reviewed_fmap_as_finite_support_relation_words_as_type_indexed_bitvec",
                  "fmap_as_finite_support_relation": ["store"], "words_as_type_indexed_bitvec": True,
                  "hol_unused_existential_inhabitants": ["β._unused"],
                  "reviewer": "Source comparison of hol_unused_existential_inhabitants and words."}
        tagged = {(lean, "memoryRel_byteArrayImp"): tag}
        self.assertEqual(MAP["validate_inventory"]([record], set(), tagged, set()), [])
        record["lean_name"] = "wrongSite"
        self.assertTrue(MAP["validate_inventory"]([record], set(), tagged, set()))

    def test_pointer_header_rejects_extra_premises_and_changed_conclusions(self):
        source = (ROOT / "Flapjack/Compiler/Backend/DataToWord/Proofs/Assign/MakePtrBits.lean").read_text()
        check = REFS["make_ptr_existential_header_errors"]
        self.assertEqual(check(source), [])
        self.assertTrue(check(source.replace("[Nonempty β]", "[Nonempty β] (extra : False)")))
        self.assertTrue(check(source.replace("tagReg ≠ dest", "tagReg = dest")))
        self.assertTrue(check(source.replace("(f - d) tag len", "(d - f) tag len")))
    def test_manifest_requires_exact_witness_and_site(self):
        hol = "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml"
        lean = "Flapjack/Compiler/Backend/DataToWord/Proofs/Memory/Relation/ConsAltWritten.lean"
        tag = (hol, "memory_rel_Cons_alt", (), (), (), (), False, (("st", ""),), (), True, (), (),
               None, (), (), False, False, (), (), (), (), (), (), (), (), (), (), (), (), (), (), ("β._unused",))
        record = {"hol_path": hol, "hol_name": "memory_rel_Cons_alt", "lean_path": lean, "lean_name": "memoryRel_consAlt",
                  "statement_status": "reviewed_fmap_as_finite_support_relation_words_as_type_indexed_bitvec",
                  "fmap_as_finite_support_relation": ["st"], "words_as_type_indexed_bitvec": True,
                  "hol_unused_existential_inhabitants": ["β._unused"],
                  "reviewer": "Source comparison of hol_unused_existential_inhabitants and words."}
        tagged = {(lean, "memoryRel_consAlt"): tag}
        self.assertEqual(MAP["validate_inventory"]([record], set(), tagged, set()), [])
        record["hol_unused_existential_inhabitants"] = ["β.other"]
        self.assertTrue(MAP["validate_inventory"]([record], set(), tagged, set()))

    def test_pointer_manifest_requires_exact_site(self):
        hol = "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml"
        lean = "Flapjack/Compiler/Backend/DataToWord/Proofs/Assign/MakePtrBits.lean"
        tag = (hol, "Make_ptr_bits_thm", (), (), (), ("fpRegs", "store"), False, (), (), True, (), (),
               None, (), (), False, False, (), (), (), (), (), (), (), (), (), (), (), (), (), (), ("β._unused",))
        record = {"hol_path": hol, "hol_name": "Make_ptr_bits_thm", "lean_path": lean, "lean_name": "makePtrBits_correct",
                  "statement_status": "reviewed_fmap_as_finite_support_words_as_type_indexed_bitvec",
                  "fmap_as_finite_support": ["fpRegs", "store"], "words_as_type_indexed_bitvec": True,
                  "hol_unused_existential_inhabitants": ["β._unused"],
                  "reviewer": "Source comparison of hol_unused_existential_inhabitants and words."}
        tagged = {(lean, "makePtrBits_correct"): tag}
        self.assertEqual(MAP["validate_inventory"]([record], set(), tagged, set()), [])
        record["lean_name"] = "wrongSite"
        self.assertTrue(MAP["validate_inventory"]([record], set(), tagged, set()))


if __name__ == "__main__":
    unittest.main()
