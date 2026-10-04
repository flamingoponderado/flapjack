#!/usr/bin/env python3
"""Enforce probe README coverage for PR1213-era HOL probes.

Rule (documented in scripts/hol-probes/README.md): every ``*_probe.out`` file
added after the pinned PR1213 base commit must be named in the README, either
in its own paragraph or in the "Probe coverage index" section.  The committed
manifest ``scripts/hol-probes/readme-coverage.txt`` lists the probes that rely
on the index.  This checker verifies both directions:

* every manifest entry is mentioned in the README; and
* every probe output added since the base is mentioned in the README or listed
  in the manifest (so a new undocumented probe fails the check).

When the pinned base commit is unavailable (for example a shallow checkout) the
git-derived half is skipped and only the manifest is checked.
"""

from __future__ import annotations

import subprocess
import sys
from pathlib import Path

BASE = "96cfe8164"
HERE = Path(__file__).resolve().parent
README = HERE / "README.md"
MANIFEST = HERE / "readme-coverage.txt"


def probes_added_since_base() -> list[str] | None:
    try:
        subprocess.run(
            ["git", "cat-file", "-e", f"{BASE}^{{commit}}"],
            check=True,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        )
    except Exception:
        return None
    out = subprocess.check_output(
        [
            "git",
            "diff",
            "--name-only",
            "--diff-filter=A",
            f"{BASE}..HEAD",
            "--",
            "scripts/hol-probes/*_probe.out",
        ],
        text=True,
    )
    return [Path(line.strip()).name for line in out.splitlines() if line.strip()]


def main() -> int:
    readme = README.read_text()
    manifest = [
        line.strip()
        for line in MANIFEST.read_text().splitlines()
        if line.strip()
    ]
    errors: list[str] = []

    for name in manifest:
        if name not in readme:
            errors.append(f"{name}: listed in manifest but not named in README.md")

    added = probes_added_since_base()
    if added is not None:
        covered = set(manifest)
        for name in added:
            if name not in readme and name not in covered:
                errors.append(
                    f"{name}: probe added since {BASE} is neither named in README.md "
                    "nor listed in readme-coverage.txt"
                )

    if errors:
        for err in errors:
            print(err, file=sys.stderr)
        return 1
    suffix = "" if added is None else f"; {len(added)} probes added since {BASE}"
    print(f"probe README coverage PASS: {len(manifest)} indexed probes{suffix}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
