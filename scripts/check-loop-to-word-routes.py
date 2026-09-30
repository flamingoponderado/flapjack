#!/usr/bin/env python3
"""Check actual exact Loop-to-Word route selection on original-accepted corpus
programs and the pinned guest. This is finite execution evidence, not a proof
that every accepted Pancake program is encodable. No CakeML files are changed.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("corpus", ROOT / "scripts/parity-corpus.py")
corpus = importlib.util.module_from_spec(spec)
spec.loader.exec_module(corpus)
GUEST_SHA256 = "daf135834eb1628faf498a768833b04e4c1e67168f6920e5065482fd358a55b4"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cake", default=corpus.DEFAULT_CAKE)
    parser.add_argument("--debug", type=Path, default=ROOT / ".lake/build/bin/flapjack-debug")
    parser.add_argument("--guest", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    if hashlib.sha256(args.guest.read_bytes()).hexdigest() != GUEST_SHA256:
        parser.error("guest source does not match pinned original parity fixture")
    args.out.mkdir(parents=True, exist_ok=True)
    rows = []
    with tempfile.TemporaryDirectory(prefix="loop-route-corpus-") as temporary:
        programs = corpus.extract_programs(corpus.DEFAULT_SUBMODULE)
        written = corpus.write_corpus(programs, temporary)
        cases = [(name, Path(path)) for name, path in written
                 if corpus.accepts_cake(args.cake, path)]
        cases.append(("pinned-guest", args.guest))
        for name, path in cases:
            result = subprocess.run([str(args.debug.resolve()), "--loop-to-word-routes", str(path)],
                                    capture_output=True, text=True)
            rows.append(dict(case=name, source_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
                             exit_code=result.returncode, stdout=result.stdout, stderr=result.stderr))
            print(f"{name}: exit={result.returncode} {result.stdout.strip()}", flush=True)
    (args.out / "results.json").write_text(json.dumps(rows, indent=2) + "\n")
    failures = sum(row["exit_code"] != 0 for row in rows)
    print(f"corpus-candidates={len(written)} original-accepted-corpus={len(rows)-1} "
          f"original-rejected={len(written)-(len(rows)-1)} guest=1 failures={failures}")
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
