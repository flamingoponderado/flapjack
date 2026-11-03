#!/usr/bin/env python3
"""Unit tests for scripts/check-stepped-import-closure.py."""

import importlib.util
import subprocess
import tempfile
import unittest
from pathlib import Path


SCRIPTS = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    "stepped_closure", SCRIPTS / "check-stepped-import-closure.py")
assert SPEC is not None and SPEC.loader is not None
CLOSURE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CLOSURE)


class SteppedImportClosureTest(unittest.TestCase):
    def test_transitive_import_is_reported_with_chain(self):
        imports = {
            "Flapjack.CompileMain": ["Flapjack.Middle"],
            "Flapjack.Middle": ["Flapjack.Stepped"],
            "Flapjack.Stepped": [],
        }
        found = CLOSURE.violations(imports, ["Flapjack.Stepped"])
        self.assertEqual(found, [
            ("Flapjack.CompileMain", ["Flapjack.CompileMain", "Flapjack.Middle", "Flapjack.Stepped"]),
            ("Flapjack.Middle", ["Flapjack.Middle", "Flapjack.Stepped"]),
        ])

    def test_tests_umbrellas_and_stepped_modules_are_exempt(self):
        imports = {
            "Flapjack": ["Flapjack.Stepped", "Flapjack.Tests"],
            "Flapjack.Tests": ["Flapjack.Test.Stepped"],
            "Flapjack.Test.Stepped": ["Flapjack.Stepped"],
            "Flapjack.Stepped": ["Flapjack.StepBase"],
            "Flapjack.StepBase": ["Flapjack.Core"],
            "Flapjack.Core": [],
        }
        self.assertEqual(
            CLOSURE.violations(imports, ["Flapjack.Stepped", "Flapjack.StepBase"]), [])

    def test_clean_graph_has_no_violations(self):
        imports = {"Flapjack.A": ["Flapjack.B", "Mathlib.Data.Nat"], "Flapjack.B": []}
        self.assertEqual(CLOSURE.violations(imports, ["Flapjack.Stepped"]), [])

    def test_list_file_ignores_comments_and_blank_lines(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "list.txt"
            path.write_text("# header\n\nFlapjack.A  # trailing\n  Flapjack.B\n")
            self.assertEqual(CLOSURE.read_stepped(path), ["Flapjack.A", "Flapjack.B"])

    def test_only_header_imports_count(self):
        source = ("/- Copyright -/\nmodule\n\nimport Flapjack.B\n\n/-!\nimport Flapjack.X\n-/\n"
                  "namespace Flapjack\nimport Flapjack.Y\n")
        self.assertEqual(CLOSURE.header_imports(source), ["Flapjack.B"])

    def test_import_lines_are_read_from_tracked_sources(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "Flapjack").mkdir()
            (root / "Flapjack/A.lean").write_text(
                "module\n\npublic import Flapjack.B\nimport all Flapjack.C\n"
                "meta import Flapjack.D\n-- import Flapjack.E\n")
            (root / "Flapjack/Untracked.lean").write_text("import Flapjack.A\n")
            subprocess.run(["git", "init", "-q", str(root)], check=True)
            subprocess.run(["git", "-C", str(root), "add", "Flapjack/A.lean"], check=True)
            self.assertEqual(CLOSURE.module_imports(root),
                             {"Flapjack.A": ["Flapjack.B", "Flapjack.C", "Flapjack.D"]})


if __name__ == "__main__":
    unittest.main()
