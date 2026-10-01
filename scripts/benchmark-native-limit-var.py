#!/usr/bin/env python3
"""Run the compiled actual-program limit-var audit without omitting failures."""
import argparse
import json
import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("paths", nargs="*", type=Path)
    parser.add_argument("--corpus", action="store_true")
    parser.add_argument("--repeats", type=int, default=20)
    parser.add_argument("--samples", type=int, default=5)
    args = parser.parse_args()
    if args.repeats <= 0 or args.samples <= 0:
        parser.error("repeats and samples must be positive")
    paths = [str(path.resolve()) for path in args.paths]
    if args.corpus:
        fixtures = json.loads((ROOT / "scripts/parity-small-corpus.json").read_text())["fixtures"]
        paths = [str(ROOT / item["path"]) for item in fixtures] + paths
    if not paths:
        parser.error("provide --corpus or explicit source files")
    environment = dict(os.environ, LIMIT_BENCH_REPEATS=str(args.repeats),
                       LIMIT_BENCH_SAMPLES=str(args.samples))
    return subprocess.run([str(ROOT / ".lake/build/bin/flapjack-limit-var-bench"), *paths],
                          cwd=ROOT, env=environment).returncode


if __name__ == "__main__":
    sys.exit(main())
