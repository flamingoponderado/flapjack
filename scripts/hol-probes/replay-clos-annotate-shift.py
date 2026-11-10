#!/usr/bin/env python3
"""Replay the pinned local shift_correct proof in an isolated HOL theory."""
from __future__ import annotations

import json
import os
from pathlib import Path
import subprocess
import tempfile

PROBES = Path(__file__).resolve().parent
SOURCE = Path(os.environ["CAKEML"]).resolve()
HOL = Path(os.environ["HOL4"]).resolve()
LABEL = "shift_correct_replay_typed="


def main() -> None:
    original = (SOURCE / "compiler/backend/proofs/clos_annotateProofScript.sml").read_text()
    begin = original.index("Theorem shift_correct[local]:")
    end = original.index("\nQED", begin) + len("\nQED")
    prefix = original[:end]
    header = "Theory clos_annotateProof\n"
    if prefix.count(header) != 1:
        raise ValueError("unexpected closure-annotation theory header")
    prefix = prefix.replace(header, "Theory clos_annotateReplay\n", 1)
    snippet = (PROBES / "clos_annotate_shift_replay_probeScript.sml").read_text()
    temp_root = os.environ.get("TMPDIR", "/var/tmp")
    with tempfile.TemporaryDirectory(prefix="flapjack-shift-replay-", dir=temp_root) as name:
        work = Path(name)
        (work / "holproject.toml").write_text(
            'name = "flapjack_shift_replay"\n\n[projects.cakeml]\npath = '
            + json.dumps(str(SOURCE)) + "\n"
        )
        (work / "clos_annotateReplayScript.sml").write_text(prefix + "\n\n" + snippet)
        command = [str(HOL / "bin/Holmake"), "--no_prereqs", "--no_preexecs", "-C", str(work)]
        dirs = sorted(p.parent.parent for p in SOURCE.rglob("objs") if p.parent.name == ".hol")
        for directory in dirs:
            command.extend(["-I", str(directory)])
        command.append("clos_annotateReplayTheory.uo")
        env = os.environ.copy()
        env["CAKEMLDIR"] = str(SOURCE)
        result = subprocess.run(command, env=env, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, text=True)
        log_path = work / ".hol/logs/clos_annotateReplayTheory"
        log = log_path.read_text() if log_path.exists() else ""
        if result.returncode:
            raise RuntimeError(f"HOL replay failed:\n{result.stdout[-4000:]}\n{log[-4000:]}")
        rows = [line for line in log.splitlines() if line.startswith(LABEL)]
        if len(rows) != 1:
            raise RuntimeError(f"expected one replay result, found {len(rows)}")
        (PROBES / "clos_annotate_shift_replay_probe.out").write_text(rows[0] + "\n")


if __name__ == "__main__":
    main()
