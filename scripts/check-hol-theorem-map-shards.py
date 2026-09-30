#!/usr/bin/env python3
"""Deterministic drift gate for the per-HOL-script theorem-map shards.

The canonical record store is ``docs/hol-theorem-map/`` (one JSON array per HOL
script, plus ``no-hol/<lean_path>.json`` for records whose ``hol_path`` is
null). ``docs/HOL-THEOREM-MAP.json`` is a *generated compatibility view* of the
canonical shards and must never be hand-edited.

The default mode fails if the two disagree in either direction: a record missing
or changed on either side, a duplicate key, an invalid record, or a stale/extra
shard file that the canonical record set does not produce. The comparison is
content-level (order-insensitive, duplicate-detecting), not byte-level.

Contributor workflow: edit the per-script shards, then regenerate the
compatibility view with ``--sync-compat``. For a batch change expressed as a
single JSON array, ``--sync`` expands that array into the canonical shards
(with stale-shard cleanup); regenerate the compatibility view afterwards so the
generated view reflects the edited shards.
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import hol_theorem_map  # noqa: E402


def _shown(path: Path) -> Path | str:
    try:
        return path.resolve().relative_to(hol_theorem_map.ROOT)
    except ValueError:
        return path


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--shard-dir",
        type=Path,
        default=hol_theorem_map.SHARD_DIR,
        help="canonical per-HOL-script shard directory",
    )
    parser.add_argument(
        "--manifest",
        type=Path,
        default=hol_theorem_map.LEGACY_MANIFEST,
        help=(
            "generated compatibility view (docs/HOL-THEOREM-MAP.json); the shard "
            "tree is canonical and this view is regenerated from it"
        ),
    )
    parser.add_argument(
        "--sync-compat",
        action="store_true",
        help=(
            "regenerate the compatibility view deterministically from the "
            "canonical shards and exit"
        ),
    )
    parser.add_argument(
        "--sync",
        action="store_true",
        help=(
            "batch helper: expand the JSON array at --manifest into the canonical "
            "shards (with stale cleanup) and exit; then run --sync-compat"
        ),
    )
    parser.add_argument(
        "--skip-compat",
        action="store_true",
        help=(
            "check only shard-internal consistency (shape, duplicates, stale "
            "files), skipping the compatibility-view comparison"
        ),
    )
    args = parser.parse_args(argv)

    if args.sync and args.sync_compat:
        print("error: --sync and --sync-compat are mutually exclusive", file=sys.stderr)
        return 2
    if args.skip_compat and (args.sync or args.sync_compat):
        print(
            "error: --skip-compat cannot be combined with --sync/--sync-compat",
            file=sys.stderr,
        )
        return 2

    if args.sync_compat:
        try:
            records = hol_theorem_map.load_manifest(args.shard_dir)
            hol_theorem_map.write_compat(args.manifest, records)
        except (OSError, ValueError) as exc:
            print(f"error: {exc}", file=sys.stderr)
            return 1
        print(
            f"wrote compatibility view {_shown(args.manifest)} "
            f"from shards: {len(records)} records"
        )
        return 0

    if args.sync:
        try:
            records = hol_theorem_map.load_manifest(args.manifest)
            written = hol_theorem_map.sync_shards(args.shard_dir, records)
        except (OSError, ValueError) as exc:
            print(f"error: {exc}", file=sys.stderr)
            return 1
        print(
            f"wrote {len(written)} shard files under {_shown(args.shard_dir)}; "
            "run --sync-compat to regenerate the compatibility view"
        )
        return 0

    if args.skip_compat:
        try:
            records = hol_theorem_map.load_manifest(args.shard_dir)
            stale = hol_theorem_map.stale_shard_files(args.shard_dir, records)
        except (OSError, ValueError) as exc:
            print(f"error: {exc}", file=sys.stderr)
            return 1
        if stale:
            for relpath in stale:
                print(f"error: stale/extra shard file: {relpath}", file=sys.stderr)
            return 1
        print(
            f"HOL theorem-map shards are internally consistent "
            f"(compatibility view skipped): {len(records)} records"
        )
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
    print(
        f"HOL theorem-map shards match compat view {_shown(args.manifest)}: "
        f"{count} records"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
