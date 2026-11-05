"""Unit tests for the Python half of scripts/report-unused-theorems.py.

The Lean half (scripts/UnusedTheorems.lean) needs the built library and is
exercised by running the script itself."""

import importlib.util
import pathlib
import sys
import tempfile
import unittest

SCRIPT = pathlib.Path(__file__).resolve().parent.parent / "report-unused-theorems.py"
spec = importlib.util.spec_from_file_location("report_unused_theorems", SCRIPT)
rut = importlib.util.module_from_spec(spec)
sys.modules["report_unused_theorems"] = rut
spec.loader.exec_module(rut)


class SourceTheoremsTest(unittest.TestCase):
    def test_written_theorems_only(self):
        text = ("theorem a : True := trivial\n"
                "@[simp] private theorem Ns.b : True := trivial\n"
                "lemma c : True := trivial\n"
                "def d : Nat := 1\n"
                "  theorem indented : True := trivial\n")
        with tempfile.TemporaryDirectory() as tmp:
            path = pathlib.Path(tmp) / "F.lean"
            path.write_text(text)
            self.assertEqual(rut.source_theorems(path), {"a", "b", "c"})

    def test_missing_file(self):
        self.assertEqual(rut.source_theorems(pathlib.Path("/nonexistent/F.lean")), set())


class TextRootsTest(unittest.TestCase):
    def test_repository_roots(self):
        repo = SCRIPT.parent.parent
        roots = rut.text_roots(repo)
        # A name from a tracked script is a root; the theorem inventory is not
        # read, so its Lean names do not all become roots.
        self.assertIn("unittest", roots)  # an identifier in tracked Python files
        self.assertNotIn("HOL-THEOREM-MAP", rut.TEXT_GLOBS)
        self.assertIn("docs/HOL-THEOREM-MAP.json", rut.EXCLUDED_TEXT)


if __name__ == "__main__":
    unittest.main()
