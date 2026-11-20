"""Guards for the fresh-reference unused HOL witness qualifier."""
import runpy
import unittest
from pathlib import Path

SCRIPTS = Path(__file__).resolve().parents[1]
ROOT = SCRIPTS.parent
REFS = runpy.run_path(str(SCRIPTS / "check-hol-refs.py"))
EXPORT = runpy.run_path(str(SCRIPTS / "check_hol_ref_export.py"))
MAP = runpy.run_path(str(SCRIPTS / "check_hol_theorem_map.py"))


class NewRefExistentialInhabitantsTest(unittest.TestCase):
    def test_qualifier_parser_and_repetition(self):
        qualifier = "(new_ref_existential_inhabitants := [β._p])"
        source = "@[hol \"cake.sml\" \"test\" " + qualifier + "]"
        scan = REFS["hol_attribute_sites"]
        self.assertEqual(list(scan([source], include_new_ref_existential_inhabitants=True))[0][-1], ("β._p",))
        repeated = source.replace(qualifier, qualifier + " " + qualifier)
        self.assertEqual(list(scan([repeated], include_new_ref_existential_inhabitants=True))[0][-1], ("",))

    def test_header_rejects_weakened_and_extra_hypotheses(self):
        source = (ROOT / "Flapjack/Compiler/Backend/DataToWord/Proofs/Memory/Relation/FreshRefProof.lean").read_text()
        check = REFS["new_ref_existential_header_errors"]
        self.assertEqual(check(source), [])
        self.assertTrue(check(source.replace("values.length + 1 ≤ sp", "values.length + 2 ≤ sp")))
        self.assertTrue(check(source.replace("[Nonempty β]", "[Nonempty β] (extra : False)")))
        self.assertTrue(check(source.replace("namespace Flapjack", "variable (extra : False)\nnamespace Flapjack", 1)))

    def test_export_metadata_must_match_both_ways(self):
        fields = ["β._p"]
        manifest = {"hol_path": "cake.sml", "hol_name": "example", "lean_path": "Flapjack/Example.lean",
                    "lean_name": "example", "statement_status": "reviewed_exact",
                    "new_ref_existential_inhabitants": fields}
        exported = {"hol_path": "cake.sml", "hol_name": "example", "lean_name": "Example.example", "qualifiers": {}}
        with self.assertRaises(ValueError):
            EXPORT["check_records"]([manifest], [exported])
        del manifest["new_ref_existential_inhabitants"]
        exported["qualifiers"]["new_ref_existential_inhabitants"] = fields
        with self.assertRaises(ValueError):
            EXPORT["check_records"]([manifest], [exported])

    def test_manifest_requires_exact_witness_and_site(self):
        hol = "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml"
        lean = "Flapjack/Compiler/Backend/DataToWord/Proofs/Memory/Relation/FreshRefProof.lean"
        fields = ("β._p",)
        tag = (hol, "new_ref_thm", (), (), (), (), False, (), False, True, (), (),
               None, (), (), False, False, (), (), (), (), (), (), (), (), (), (), (), (), fields)
        record = {"hol_path": hol, "hol_name": "new_ref_thm", "lean_path": lean, "lean_name": "newRef",
                  "statement_status": "reviewed_words_as_type_indexed_bitvec",
                  "words_as_type_indexed_bitvec": True, "new_ref_existential_inhabitants": list(fields),
                  "reviewer": "Source comparison of new_ref_existential_inhabitants and words."}
        tagged = {(lean, "newRef"): tag}
        self.assertEqual(MAP["validate_inventory"]([record], set(), tagged, set()), [])
        record["new_ref_existential_inhabitants"] = ["β.other"]
        self.assertTrue(MAP["validate_inventory"]([record], set(), tagged, set()))


if __name__ == "__main__":
    unittest.main()
