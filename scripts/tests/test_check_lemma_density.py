"""Unit tests for scripts/check-lemma-density.py."""

import importlib.util
import io
import json
import pathlib
import sys
import tempfile
import unittest
from collections import Counter
from contextlib import redirect_stdout

SCRIPT = pathlib.Path(__file__).resolve().parent.parent / "check-lemma-density.py"
spec = importlib.util.spec_from_file_location("check_lemma_density", SCRIPT)
cld = importlib.util.module_from_spec(spec)
sys.modules["check_lemma_density"] = cld
spec.loader.exec_module(cld)

LEAN = '''import Flapjack.HolRef

/-- Mentions @[hol "a/xScript.sml" "fake"] and
theorem notATheorem in prose. -/
@[hol "a/xScript.sml" "t1"]
theorem one : True := trivial

-- @[hol "a/yScript.sml" "commented"]
@[simp] theorem two : True := trivial

private lemma three : True := trivial

@[hol "a/yScript.sml" "d"]
def four : Nat := 4
'''


class LeanStatsTest(unittest.TestCase):
    def test_comments_are_ignored(self):
        lines, theorems, tags = cld.lean_file_stats(LEAN)
        self.assertEqual(lines, LEAN.count("\n"))
        self.assertEqual(theorems, 3)
        self.assertEqual(tags, Counter({"a/xScript.sml": 1, "a/yScript.sml": 1}))


class HolStatsTest(unittest.TestCase):
    def test_declarations_outside_comments(self):
        text = ("Theorem a:\n  T\nQED\n(* Theorem b:\n (* nested *) Definition c:\n*)\n"
                "Definition d:\n  x = 1\nEnd\nTriviality e:\n T\nQED\n  Theorem indented\n")
        with tempfile.TemporaryDirectory() as d:
            tmp = pathlib.Path(d) / "xScript.sml"
            tmp.write_text(text)
            self.assertEqual(cld.hol_file_stats(tmp), (text.count("\n"), 3))

    def test_missing_script(self):
        self.assertIsNone(cld.hol_file_stats(pathlib.Path("/nonexistent/xScript.sml")))


class AttributionTest(unittest.TestCase):
    def test_majority_and_ancestors(self):
        files = {
            "P/A/tagged.lean": Counter({"x": 2, "y": 1}),
            "P/A/helper.lean": Counter(),
            "P/A/Sub/deep.lean": Counter(),
            "P/B/tie.lean": Counter({"y": 1, "x": 1}),
            "P/B/helper.lean": Counter(),
            "Q/none.lean": Counter(),
        }
        owner = cld.attribute(files)
        self.assertEqual(owner["P/A/tagged.lean"], "x")
        self.assertEqual(owner["P/A/helper.lean"], "x")
        self.assertEqual(owner["P/A/Sub/deep.lean"], "x")
        self.assertEqual(owner["P/B/tie.lean"], "x")
        self.assertEqual(owner["P/B/helper.lean"], "x")
        # Q has no tags of its own; the repository root's majority is used.
        self.assertEqual(owner["Q/none.lean"], "x")

    def test_no_tags_anywhere(self):
        self.assertEqual(cld.attribute({"a/b.lean": Counter()}), {"a/b.lean": cld.UNATTRIBUTED})


class MainTest(unittest.TestCase):
    def test_json_on_repository_subtree(self):
        out = io.StringIO()
        with redirect_stdout(out):
            self.assertEqual(cld.main(["Flapjack/Pancake/PanLang", "--json"]), 0)
        report = json.loads(out.getvalue())
        self.assertTrue(report["scripts"])
        self.assertEqual(report["totals"]["lean_lines"],
                         sum(r["lean_lines"] for r in report["scripts"]))
        for row in report["scripts"]:
            if row["hol_lines"]:
                self.assertEqual(row["line_ratio"],
                                 round(row["lean_lines"] / row["hol_lines"], 1))

    def test_text_output(self):
        out = io.StringIO()
        with redirect_stdout(out):
            self.assertEqual(cld.main(["Flapjack/Pancake/PanLang", "--sort", "script"]), 0)
        self.assertIn("total (", out.getvalue())


if __name__ == "__main__":
    unittest.main()
