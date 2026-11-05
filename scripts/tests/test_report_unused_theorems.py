"""Unit tests for the Python half of scripts/report-unused-theorems.py.

The Lean half (scripts/UnusedTheorems.lean) needs the built library and is
exercised by running the script itself."""

import importlib.util
import pathlib
import sys
import tempfile
import unittest
import io
import json
from contextlib import redirect_stderr, redirect_stdout
from unittest import mock

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


LEAN = """
/-- doc @[simp] theorem inDoc : True := trivial -/
@[simp] theorem simpOne : True := trivial

@[hol "a/xScript.sml" "t"]
theorem holOnly : True := trivial

@[hol "a/xScript.sml" "u" (list_as_array := [f])]
theorem holQualified : True := trivial

@[hol "a/xScript.sml" "v", grind =]
private theorem Ns.holAndGrind : True := trivial

@[local simp]
lemma localSimp : True := trivial

@[ext] theorem
  extSplit : True := trivial

@[simp] def simpDef : Nat := 1

theorem plain : True := trivial

theorem later : True := trivial
theorem laterToo : True := trivial
attribute [simp] later Ns.laterToo
attribute [-simp] removedAttr
attribute [local irreducible] simpDef
attribute [simp]
  multiOne
  Ns.multiTwo
theorem afterMulti : True := trivial
-- attribute [simp] commented
"""


class AttributedTheoremsTest(unittest.TestCase):
    def test_non_hol_attributes(self):
        self.assertEqual(
            rut.attributed_theorems(LEAN),
            {"simpOne", "holAndGrind", "localSimp", "extSplit", "later", "laterToo",
             "removedAttr", "simpDef", "multiOne", "multiTwo", "Ns"},
        )


NAMED = """
theorem usedByRfl : (1 : Nat) = 1 := rfl

theorem kept : True := by
  simp [usedByRfl]

theorem deadA : True := deadB

theorem deadB : True := trivial

-- deadC is mentioned only in a comment
theorem deadC : True := trivial

theorem chainA : True := chainB

theorem chainB : True := trivial

example : True := by simp [inExample]

theorem inExample : True := trivial

theorem stringOnly : True := trivial
def s : String := "stringOnly"

theorem iffThm : True ↔ True := Iff.rfl

example : True := by simp [iffThm.mp]

theorem nsThm : True := trivial

theorem usesNs : True := Flapjack.nsThm
"""


class NamedUsesTest(unittest.TestCase):
    def test_fixed_point(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = pathlib.Path(tmp) / "F.lean"
            path.write_text(NAMED)
            names = ["usedByRfl", "deadA", "deadB", "deadC", "chainB", "inExample",
                     "stringOnly", "iffThm", "nsThm"]
            found = [{"file": "F.lean", "module": "F", "name": "Flapjack." + n} for n in names]
            kept = rut.filter_named_uses({"F.lean": path}, found)
        # usedByRfl is named by the surviving `kept`; chainB by the surviving
        # chainA (not a candidate); inExample by an example.  deadB is named
        # only by the candidate deadA, deadC only in a comment, stringOnly
        # only inside a string.  iffThm is named through `iffThm.mp` and
        # nsThm through the qualified `Flapjack.nsThm`.
        self.assertEqual({d["name"].split(".")[-1] for d in kept},
                         {"deadA", "deadB", "deadC", "stringOnly"})


class InventoryRootsTest(unittest.TestCase):
    def test_only_placeholder_rows_are_candidates(self):
        rows = [
            {"hol_path": None, "hol_name": None, "lean_name": "Flapjack.placeholder",
             "statement_status": "no_hol_reference_pending_classification"},
            {"hol_path": "a/xScript.sml", "hol_name": "x", "lean_name": "Flapjack.mismatch",
             "statement_status": "documented_mismatch"},
            {"hol_path": "a/xScript.sml", "hol_name": "y", "lean_name": "exact",
             "statement_status": "reviewed_exact"},
        ]
        with tempfile.TemporaryDirectory() as tmp:
            (pathlib.Path(tmp) / "docs").mkdir()
            (pathlib.Path(tmp) / rut.INVENTORY).write_text(json.dumps(rows))
            self.assertEqual(rut.inventory_roots(pathlib.Path(tmp)), {"mismatch", "exact"})


class MainRootsTest(unittest.TestCase):
    def test_automation_names_reach_the_lean_half(self):
        captured = {}

        def fake_run(cmd, **kwargs):
            if cmd[:2] == ["lake", "env"]:
                captured["roots"] = pathlib.Path(
                    kwargs["env"]["UNUSED_THEOREMS_TEXT_ROOTS"]).read_text().split()
                return mock.Mock(returncode=0, stdout="", stderr="")
            return real_run(cmd, **kwargs)

        real_run = rut.subprocess.run
        with mock.patch.object(rut, "automation_roots", return_value={"onlyByAttribute"}), \
                mock.patch.object(rut, "inventory_roots", return_value={"onlyByInventory"}), \
                mock.patch.object(rut, "text_roots", return_value={"onlyByText"}), \
                mock.patch.object(rut.subprocess, "run", side_effect=fake_run), \
                redirect_stderr(io.StringIO()), redirect_stdout(io.StringIO()):
            self.assertEqual(rut.main([]), 0)
        # Every root source reaches the Lean half, and nothing else does.
        self.assertEqual(sorted(captured["roots"]),
                         ["onlyByAttribute", "onlyByInventory", "onlyByText"])


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
