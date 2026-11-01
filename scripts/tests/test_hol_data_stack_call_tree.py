"""Check the complete arithmetic call tree against the HOL capture."""
from pathlib import Path
import subprocess
import sys
import unittest

ROOT = Path(__file__).resolve().parents[2]


class DataStackCallTreeTest(unittest.TestCase):
    def test_lean_tree_matches_original(self):
        subprocess.run([sys.executable, str(ROOT / "scripts/check-data-stack-call-tree.py")],
                       cwd=ROOT, check=True, capture_output=True, text=True)


if __name__ == "__main__":
    unittest.main()
