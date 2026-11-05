"""Unit tests for scripts/report-proof-duplication.py."""

import importlib.util
import io
import json
import pathlib
import sys
import tempfile
import unittest
from contextlib import redirect_stdout

SCRIPT = pathlib.Path(__file__).resolve().parent.parent / "report-proof-duplication.py"
spec = importlib.util.spec_from_file_location("report_proof_duplication", SCRIPT)
rpd = importlib.util.module_from_spec(spec)
sys.modules["report_proof_duplication"] = rpd
spec.loader.exec_module(rpd)

BODY = "\n".join(f"  have h{i} : {i} + x = x + {i} := by omega" for i in range(25))

SOURCE = f"""import Foo

/-- doc -/
theorem first (x : Nat) : True := by
{BODY}
  trivial

-- a comment between declarations
theorem second (x : Nat) : True := by
{BODY.replace('omega', 'omega -- trailing comment')}
  trivial

theorem short (x : Nat) : True := by
  trivial

def unrelated : Nat := 1
"""


class ReportProofDuplicationTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.path = pathlib.Path(self.tmp.name) / "A.lean"
        self.path.write_text(SOURCE)

    def tearDown(self):
        self.tmp.cleanup()

    def test_parse_decls(self):
        decls = rpd.parse_decls(self.path, "A.lean")
        self.assertEqual([d.name for d in decls], ["first", "second", "short", "unrelated"])
        self.assertEqual(decls[0].kind, "theorem")
        self.assertEqual(decls[0].lines, 27)
        self.assertEqual(decls[3].kind, "def")

    def test_strip_comments(self):
        text = "a /- b /- nested -/ c -/ d -- e\nf"
        self.assertEqual(rpd.strip_comments(text), "a  d \nf")

    def test_clusters_ignore_names_numbers_and_comments(self):
        decls = [d for d in rpd.parse_decls(self.path, "A.lean") if d.lines >= 20]
        groups = rpd.clusters(decls, 8, 0.8, 200)
        self.assertEqual([[d.name for d in g] for g in groups], [["first", "second"]])

    def test_dissimilar_proofs_do_not_cluster(self):
        other = "\n".join(f"  have k{i} : {i} * y = y * {i} := by ring" for i in range(25))
        self.path.write_text(SOURCE.replace(BODY.replace("omega", "omega -- trailing comment"),
                                            other))
        decls = [d for d in rpd.parse_decls(self.path, "A.lean") if d.lines >= 20]
        self.assertEqual(rpd.clusters(decls, 8, 0.8, 200), [])

    def test_json_report(self):
        buf = io.StringIO()
        with redirect_stdout(buf):
            self.assertEqual(rpd.main([str(self.path), "--json"]), 0)
        report = json.loads(buf.getvalue())
        self.assertEqual(report["files"][0]["theorems"], 3)
        self.assertEqual(report["compared_declarations"], 2)
        self.assertEqual(len(report["clusters"]), 1)
        self.assertEqual(report["lines_in_clusters"], 54)


if __name__ == "__main__":
    unittest.main()
