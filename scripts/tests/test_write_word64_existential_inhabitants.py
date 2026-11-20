"""Guards for the Word64 evaluator unused HOL witness qualifier."""
import runpy
import unittest
from pathlib import Path

SCRIPTS = Path(__file__).resolve().parents[1]
ROOT = SCRIPTS.parent
REFS = runpy.run_path(str(SCRIPTS / "check-hol-refs.py"))
EXPORT = runpy.run_path(str(SCRIPTS / "check_hol_ref_export.py"))
MAP = runpy.run_path(str(SCRIPTS / "check_hol_theorem_map.py"))


class WriteWord64ExistentialInhabitantsTest(unittest.TestCase):
    def test_qualifier_parser_and_repetition(self):
        qualifier = "(write_word64_existential_inhabitants := [β._unused])"
        source = "@[hol \"cake.sml\" \"test\" " + qualifier + "]"
        scan = REFS["hol_attribute_sites"]
        self.assertEqual(list(scan([source], include_write_word64_existential_inhabitants=True))[0][-1], ("β._unused",))
        repeated = source.replace(qualifier, qualifier + " " + qualifier)
        self.assertEqual(list(scan([repeated], include_write_word64_existential_inhabitants=True))[0][-1], ("",))

    def test_headers_reject_changed_premises_and_extra_hypotheses(self):
        source = (ROOT / "Flapjack/Compiler/Backend/DataToWord/Proofs/Assign/WriteWord64.lean").read_text()
        check = REFS["word64_existential_header_errors"]
        for name in ("evaluateWriteWord64", "evaluateWriteWord64On32"):
            self.assertEqual(check(source, name), [])
            self.assertTrue(check(source.replace("[Nonempty β]", "[Nonempty β] (extra : False)"), name))
            self.assertTrue(check(source.replace("namespace Flapjack", "variable (extra : False)\nnamespace Flapjack", 1), name))
        self.assertTrue(check(source.replace("src ≠ 1", "src ≠ 2"), "evaluateWriteWord64"))
        self.assertTrue(check(source.replace("src2 ≠ 1", "src2 ≠ 2"), "evaluateWriteWord64On32"))

    def test_export_metadata_must_match_both_ways(self):
        fields = ["β._unused"]
        manifest = {"hol_path": "cake.sml", "hol_name": "example", "lean_path": "Flapjack/Example.lean",
                    "lean_name": "example", "statement_status": "reviewed_exact",
                    "write_word64_existential_inhabitants": fields}
        exported = {"hol_path": "cake.sml", "hol_name": "example", "lean_name": "Example.example", "qualifiers": {}}
        with self.assertRaises(ValueError):
            EXPORT["check_records"]([manifest], [exported])
        del manifest["write_word64_existential_inhabitants"]
        exported["qualifiers"]["write_word64_existential_inhabitants"] = fields
        with self.assertRaises(ValueError):
            EXPORT["check_records"]([manifest], [exported])

    def test_manifest_requires_exact_witness_and_site(self):
        hol = "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml"
        lean = "Flapjack/Compiler/Backend/DataToWord/Proofs/Assign/WriteWord64.lean"
        for hol_name, lean_name in (("evaluate_WriteWord64", "evaluateWriteWord64"),
                                    ("evaluate_WriteWord64_on_32", "evaluateWriteWord64On32")):
            tag = (hol, hol_name, (), (), (), ("fpRegs", "store"), False, (), (), True, (), (),
                   None, (), (), False, False, (), (), (), (), (), (), (), (), (), (), (), (), (), ("β._unused",))
            record = {"hol_path": hol, "hol_name": hol_name, "lean_path": lean, "lean_name": lean_name,
                      "statement_status": "reviewed_fmap_as_finite_support_words_as_type_indexed_bitvec",
                      "fmap_as_finite_support": ["fpRegs", "store"], "words_as_type_indexed_bitvec": True,
                      "write_word64_existential_inhabitants": ["β._unused"],
                      "reviewer": "Source comparison of write_word64_existential_inhabitants and words."}
            tagged = {(lean, lean_name): tag}
            self.assertEqual(MAP["validate_inventory"]([record], set(), tagged, set()), [])
            record["write_word64_existential_inhabitants"] = ["β.other"]
            self.assertTrue(MAP["validate_inventory"]([record], set(), tagged, set()))


if __name__ == "__main__":
    unittest.main()
