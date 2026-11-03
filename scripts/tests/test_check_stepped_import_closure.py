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


def tracked_tree(files):
    """A temporary Git tree with the given tracked files; returns the directory."""
    directory = tempfile.TemporaryDirectory()
    root = Path(directory.name)
    for name, text in files.items():
        path = root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")
    subprocess.run(["git", "init", "-q", str(root)], check=True)
    subprocess.run(["git", "-C", str(root), "add", "--", *files], check=True)
    return directory


class ViolationsTest(unittest.TestCase):
    def test_transitive_import_is_reported_with_chain(self):
        imports = {
            "Flapjack.CompileMain": ["Flapjack.Middle"],
            "Flapjack.Middle": ["Flapjack.Stepped"],
            "Flapjack.Stepped": [],
        }
        self.assertEqual(CLOSURE.violations(imports, ["Flapjack.Stepped"]), [
            ("Flapjack.CompileMain", ["Flapjack.CompileMain", "Flapjack.Middle", "Flapjack.Stepped"]),
            ("Flapjack.Middle", ["Flapjack.Middle", "Flapjack.Stepped"]),
        ])

    def test_test_modules_are_restricted_unless_allowlisted(self):
        imports = {
            "Flapjack.Test.CompilerParity": ["Flapjack.Test.Stepped", "Flapjack.Test.Clean"],
            "Flapjack.Test.Stepped": ["Flapjack.Stepped"],
            "Flapjack.Test.Clean": [],
            "Flapjack.Stepped": [],
        }
        self.assertEqual([m for m, _ in CLOSURE.violations(imports, ["Flapjack.Stepped"])],
                         ["Flapjack.Test.CompilerParity", "Flapjack.Test.Stepped"])
        self.assertEqual(CLOSURE.violations(
            imports, ["Flapjack.Stepped"],
            ["Flapjack.Test.CompilerParity", "Flapjack.Test.Stepped"]), [])

    def test_umbrellas_and_stepped_modules_are_exempt(self):
        imports = {
            "Flapjack": ["Flapjack.Stepped", "Flapjack.Tests"],
            "Flapjack.Tests": ["Flapjack.Test.Stepped"],
            "Flapjack.Test.Stepped": ["Flapjack.Stepped"],
            "Flapjack.Stepped": ["Flapjack.StepBase"],
            "Flapjack.StepBase": ["Flapjack.Core"],
            "Flapjack.Core": [],
        }
        self.assertEqual(CLOSURE.violations(
            imports, ["Flapjack.Stepped", "Flapjack.StepBase"], ["Flapjack.Test.Stepped"]), [])

    def test_stale_allowlist_entries_are_reported(self):
        imports = {"Flapjack.Test.Clean": [], "Flapjack.Test.Stepped": ["Flapjack.Stepped"],
                   "Flapjack.Stepped": []}
        allowed = ["Flapjack.Test.Clean", "Flapjack.Test.Stepped", "Flapjack.Test.Gone"]
        self.assertEqual(CLOSURE.stale_allowlist(imports, ["Flapjack.Stepped"], allowed),
                         ["Flapjack.Test.Clean", "Flapjack.Test.Gone"])

    def test_unresolved_flapjack_imports_are_reported(self):
        imports = {"Flapjack.A": ["Flapjack.Missing", "Mathlib.Data.Nat", "Flapjack.B"],
                   "Flapjack.B": []}
        self.assertEqual(CLOSURE.unresolved(imports), [("Flapjack.A", "Flapjack.Missing")])


class ParsingTest(unittest.TestCase):
    def test_only_header_imports_count(self):
        source = ("/- Copyright -/\nmodule\n\nimport Flapjack.B\n\n/-!\nimport Flapjack.X\n-/\n"
                  "namespace Flapjack\nimport Flapjack.Y\n")
        self.assertEqual(CLOSURE.header_imports(source), ["Flapjack.B"])

    def test_nested_and_line_comments_do_not_hide_imports(self):
        source = ("/- outer /- inner -/ still outer -/\n"
                  "-- a line comment with /- in it\n"
                  "import Flapjack.A\n"
                  "public import Flapjack.B -- trailing comment\n")
        self.assertEqual(CLOSURE.header_imports(source), ["Flapjack.A", "Flapjack.B"])

    def test_import_forms_and_quoted_names(self):
        source = ("module\nprelude\npublic import Flapjack.B\nimport all Flapjack.C\n"
                  "meta import Flapjack.D\nimport Flapjack.«PanValueFfiSemantics»\n"
                  "import Flapjack.Ünïcode\n")
        self.assertEqual(CLOSURE.header_imports(source), [
            "Flapjack.B", "Flapjack.C", "Flapjack.D", "Flapjack.PanValueFfiSemantics",
            "Flapjack.Ünïcode"])

    def test_unparseable_import_line_is_an_error(self):
        with self.assertRaises(CLOSURE.ParseError):
            CLOSURE.header_imports("import Flapjack.A Flapjack.B\n")

    def test_list_file_ignores_comments_and_blank_lines(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "list.txt"
            path.write_text("# header\n\nFlapjack.A  # trailing\n  Flapjack.B\n", encoding="utf-8")
            self.assertEqual(CLOSURE.read_list(path), ["Flapjack.A", "Flapjack.B"])

    def test_tracked_sources_with_spaces_and_unicode_in_paths(self):
        tree = tracked_tree({
            "Flapjack/A.lean": "module\n\npublic import Flapjack.«B C»\n-- import Flapjack.E\n",
            "Flapjack/B C.lean": "import Flapjack.Ü\n",
            "Flapjack/Ü.lean": "",
        })
        with tree:
            root = Path(tree.name)
            (root / "Flapjack/Untracked.lean").write_text("import Flapjack.A\n", encoding="utf-8")
            self.assertEqual(CLOSURE.module_imports(root), {
                "Flapjack.A": ["Flapjack.B C"],
                "Flapjack.B C": ["Flapjack.Ü"],
                "Flapjack.Ü": [],
            })


if __name__ == "__main__":
    unittest.main()
