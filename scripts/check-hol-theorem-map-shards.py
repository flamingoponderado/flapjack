#!/usr/bin/env python3
"""Deterministic drift gate for the per-HOL-script theorem-map shards.

The canonical record store is ``docs/hol-theorem-map/`` (one JSON array per HOL
script, plus ``no-hol/<lean_path>.json`` for records whose ``hol_path`` is
null). ``docs/HOL-THEOREM-MAP.json`` is kept as the byte-stable compatibility
view. This gate fails if the two disagree in any way: a record missing or
changed on either side, a duplicate key, an invalid record, or a stale/extra
shard file that the monolith no longer produces.

With ``--sync`` the shards are regenerated deterministically from the monolith
(with stale-shard cleanup) instead of checking drift.
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import hol_theorem_map  # noqa: E402


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--shard-dir",
        type=Path,
        default=hol_theorem_map.SHARD_DIR,
        help="per-HOL-script shard directory",
    )
    parser.add_argument(
        "--manifest",
        type=Path,
        default=hol_theorem_map.LEGACY_MANIFEST,
        help="authoritative legacy JSON array compatibility view",
    )
    parser.add_argument(
        "--sync",
        action="store_true",
        help="regenerate the shards from the manifest (with stale cleanup) and exit",
    )
    args = parser.parse_args(argv)

    if args.sync:
        try:
            records = hol_theorem_map.load_manifest(args.manifest)
            written = hol_theorem_map.sync_shards(args.shard_dir, records)
        except (OSError, ValueError) as exc:
            print(f"error: {exc}", file=sys.stderr)
            return 1
        print(f"wrote {len(written)} shard files under {args.shard_dir}")
        return 0

    try:
        diff = hol_theorem_map.check_drift(args.shard_dir, args.manifest)
    except (OSError, ValueError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 1

    if not diff.ok():
        for message in diff.messages():
            print(f"error: {message}", file=sys.stderr)
        return 1

    count = len(hol_theorem_map.load_manifest(args.shard_dir))
    try:
        shown = args.manifest.resolve().relative_to(hol_theorem_map.ROOT)
    except ValueError:
        shown = args.manifest
    print(
        f"HOL theorem-map shards match {shown}: {count} records"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
