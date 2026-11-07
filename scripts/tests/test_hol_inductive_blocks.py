"""Generated HOL inductive names require a real terminated source block."""

import runpy
import tempfile
import unittest
from pathlib import Path

SCRIPTS = Path(__file__).resolve().parents[1]
DECLS = runpy.run_path(str(SCRIPTS / "hol_sml_declarations.py"))["inductive_block_declarations"]
LINES = runpy.run_path(str(SCRIPTS / "check-hol-refs.py"))["hol_declaration_lines"]


class InductiveBlocksTest(unittest.TestCase):
    def test_generated_names_and_kinds(self):
        text = "Inductive foo[local]:\n  P\nEnd\nCoInductive bar:\n  Q\nEnd\n"
        self.assertEqual(DECLS(text), [
            (("foo_rules", "foo_ind", "foo_strongind", "foo_cases"), 1, 3),
            (("bar_rules", "bar_coind", "bar_cases"), 4, 6),
        ])

    def test_reject_hidden_and_unterminated(self):
        text = ("(* Inductive comment:\nEnd *)\n"
                "val q = ``Inductive quoted:\nEnd``;\n"
                "local\nInductive nested:\n P\nEnd\nin end;\n"
                " Inductive indented:\n P\nEnd\n"
                "Inductive unfinished:\n P\n")
        self.assertEqual(DECLS(text), [])

    def test_new_header_cannot_terminate_previous_block(self):
        text = "Inductive missing:\n P\nInductive real:\n Q\nEnd\n"
        self.assertEqual(DECLS(text), [])
        self.assertEqual(DECLS("Theorem outer:\nEnd\nInductive fake:\n P\nEnd\nQED\n"), [])

    def test_inductive_after_theorem(self):
        text = "Theorem earlier:\n T\nProof simp[] QED\nInductive ok:\n P\nEnd\n"
        self.assertEqual(DECLS(text), [(("ok_rules", "ok_ind", "ok_strongind", "ok_cases"), 4, 6)])

    def test_list_cons_in_theorem_binding_is_not_a_block_header(self):
        text = "Theorem refs_defs = LIST_CONJ (a :: b :: c)\nInductive inferred:\n P\nEnd\n"
        self.assertEqual(DECLS(text), [(("inferred_rules", "inferred_ind", "inferred_strongind", "inferred_cases"), 2, 4)])

    def test_semicolon_after_qed_closes_theorem(self):
        for terminator in ("QED;", "Proof simp[] QED;", "QED; (* comment *)"):
            with self.subTest(terminator=terminator):
                text = f"Theorem a:\n T\nProof\n simp[]\n{terminator}\nInductive r:\n P\nEnd\n"
                self.assertEqual(DECLS(text), [(("r_rules", "r_ind", "r_strongind", "r_cases"), 6, 8)])

    def test_reference_index_records_ambiguity(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "sampleScript.sml"
            path.write_text("Inductive foo:\n P\nEnd\nTheorem foo_cases:\n T\nProof simp[] QED\n")
            names = LINES(path, {})
            self.assertEqual(names["foo_cases"], [1, 4])
            self.assertEqual(names["foo_ind"], [1])
            self.assertNotIn("foo_coind", names)
            self.assertNotIn("bar_ind", names)


if __name__ == "__main__":
    unittest.main()
