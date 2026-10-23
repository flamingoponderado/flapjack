"""Exercise the syntax script's platform/tool selection without running Lake."""

import os
from pathlib import Path
import subprocess
import tempfile
import unittest


SCRIPT = Path(__file__).resolve().parents[1] / "test-hol-ref-syntax.sh"


class SyntaxScriptToolsTest(unittest.TestCase):
    def run_script(self, platform, *, gnu_prefixed=False, gnu_unprefixed=False):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            log = root / "calls"

            def tool(name, body):
                path = root / name
                path.write_text("#!/bin/sh\n" + body + "\n")
                path.chmod(0o755)

            tool("uname", f"printf '%s\\n' '{platform}'")
            tool("lake", 'echo lake >> "$TOOL_CALLS"')
            version = "GNU coreutils" if gnu_unprefixed else "BSD mktemp"
            tool("mktemp", f'''if [ "$1" = --version ]; then
  echo '{version}'
  exit 0
fi
echo "mktemp $*" >> "$TOOL_CALLS"
exit 37''')
            if gnu_prefixed:
                tool("gmktemp", 'echo "gmktemp $*" >> "$TOOL_CALLS"\nexit 37')

            environment = dict(os.environ, PATH=f"{root}:/usr/bin:/bin", TOOL_CALLS=str(log))
            result = subprocess.run(
                ["/bin/bash", str(SCRIPT)], env=environment, capture_output=True, text=True
            )
            calls = log.read_text().splitlines() if log.exists() else []
            return result, calls

    def test_macos_uses_gmktemp(self):
        result, calls = self.run_script("Darwin", gnu_prefixed=True)
        self.assertEqual(result.returncode, 37)
        self.assertEqual(calls, ["lake", "gmktemp --suffix=.lean"])

    def test_macos_accepts_gnu_mktemp_on_path(self):
        result, calls = self.run_script("Darwin", gnu_unprefixed=True)
        self.assertEqual(result.returncode, 37)
        self.assertEqual(calls, ["lake", "mktemp --suffix=.lean"])

    def test_macos_missing_gnu_fails_before_build(self):
        result, calls = self.run_script("Darwin")
        self.assertEqual(result.returncode, 1)
        self.assertIn("requires GNU mktemp on macOS", result.stderr)
        self.assertIn("brew install coreutils", result.stderr)
        self.assertEqual(calls, [])

    def test_linux_uses_mktemp(self):
        result, calls = self.run_script("Linux", gnu_prefixed=True)
        self.assertEqual(result.returncode, 37)
        self.assertEqual(calls, ["lake", "mktemp --suffix=.lean"])


if __name__ == "__main__":
    unittest.main()
