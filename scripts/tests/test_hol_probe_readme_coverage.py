import subprocess
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
CHECKER = ROOT / "scripts" / "hol-probes" / "check-readme-coverage.py"
README = ROOT / "scripts" / "hol-probes" / "README.md"
MANIFEST = ROOT / "scripts" / "hol-probes" / "readme-coverage.txt"


class ProbeReadmeCoverageTest(unittest.TestCase):
    def test_checker_passes(self):
        result = subprocess.run(
            [sys.executable, str(CHECKER)],
            cwd=ROOT,
            capture_output=True,
            text=True,
        )
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_manifest_entries_named_in_readme(self):
        readme = README.read_text()
        names = [line.strip() for line in MANIFEST.read_text().splitlines() if line.strip()]
        self.assertTrue(names)
        missing = [name for name in names if name not in readme]
        self.assertEqual(missing, [])


if __name__ == "__main__":
    unittest.main()
