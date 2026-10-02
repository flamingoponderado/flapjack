#!/usr/bin/env python3
"""Regression checks for the actual CI native-trust gate in isolated Git trees."""

import importlib.util
import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path


SCRIPTS = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("native_trust", SCRIPTS / "check-native-trust.py")
assert SPEC is not None and SPEC.loader is not None
TRUST = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(TRUST)


class NativeTrustTest(unittest.TestCase):
    def gate(self, source: str, allowance: str = "") -> subprocess.CompletedProcess:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "scripts").mkdir()
            for name in ("check-native-decide.sh", "check-native-trust.py"):
                shutil.copyfile(SCRIPTS / name, root / "scripts" / name)
            (root / "scripts/native-decide-allowlist.txt").write_text(allowance)
            (root / "Example.lean").write_text(source)
            subprocess.run(["git", "init", "-q", str(root)], check=True)
            subprocess.run(["git", "-C", str(root), "add", "Example.lean"], check=True)
            return subprocess.run(["bash", "scripts/check-native-decide.sh"], cwd=root,
                                  text=True, capture_output=True)

    def test_kernel_proofs_pass(self):
        result = self.gate("example : True := by decide\nexample : 1 = 1 := by rfl\n")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_each_new_mechanism_is_rejected_by_ci_entrypoint(self):
        sources = ["example : True := by bv_decide\n",
                   "example := Lean.ofReduceBool true rfl\n",
                   "set_option debug.skipKernelTC.trustCompiler true\n"]
        for source in sources:
            with self.subTest(source=source):
                result = self.gate(source)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("has no native-trust allowance", result.stdout)

    def test_allowlisted_native_decide_cannot_allow_other_mechanisms(self):
        result = self.gate("example : True := by native_decide\n"
                           "example : True := by bv_decide\n", "1 Example.lean\n")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("bv_decide has no native-trust allowance", result.stdout)

    def test_existing_native_decide_allowance_is_retained(self):
        source = "example : True := by native_decide\n"
        self.assertEqual(self.gate(source, "1 Example.lean\n").returncode, 0)
        self.assertNotEqual(self.gate(source).returncode, 0)
        self.assertNotEqual(self.gate(source * 2, "1 Example.lean\n").returncode, 0)

    def test_nested_and_line_comment_mentions_are_ignored(self):
        source = "-- bv_decide\n/- outer ofReduceBool /- trustCompiler -/ still outer -/\n"
        self.assertEqual(TRUST.violations(source), [])
        self.assertEqual(self.gate(source).returncode, 0)

    def test_comment_end_does_not_hide_a_following_use(self):
        source = "/- /- bv_decide -/ -/\nexample : True := by bv_decide\n"
        self.assertEqual(TRUST.violations(source), [(2, "bv_decide")])

    def test_quoted_comment_markers_do_not_hide_code(self):
        for prefix in ['def text := "-- /-"', 'def text := "escaped \\\" /-"',
                       "def character := '\"'"]:
            with self.subTest(prefix=prefix):
                self.assertEqual(TRUST.violations(prefix + "\nexample := Lean.ofReduceBool\n"),
                                 [(2, "ofReduceBool")])

    def test_string_mentions_are_conservatively_rejected(self):
        self.assertEqual(TRUST.violations('def text := "ofReduceBool"'), [(1, "ofReduceBool")])

    def test_identifier_substrings_are_not_mechanism_names(self):
        self.assertEqual(TRUST.violations("def bv_decide_helper := 1\ndef untrustCompiler := 0"), [])

    def test_namespaced_and_escaped_names_are_rejected(self):
        self.assertEqual(TRUST.violations("Lean.ofReduceBool\n«bv_decide»"),
                         [(1, "ofReduceBool"), (2, "bv_decide")])

    def test_bad_native_allowlist_remains_fail_closed(self):
        for allowance in ("1 Example.lean\n1 Example.lean\n", "oops Example.lean\n"):
            with self.subTest(allowance=allowance):
                self.assertNotEqual(self.gate("example : True := by decide\n", allowance).returncode, 0)


if __name__ == "__main__":
    unittest.main()
