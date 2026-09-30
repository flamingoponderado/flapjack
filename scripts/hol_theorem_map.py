#!/usr/bin/env python3
"""Load and write the reviewed HOL-tag manifest as deterministic shards.

The manifest started as a single ``docs/HOL-THEOREM-MAP.json`` array. It is
large enough that concurrent fleet merges conflict at the monolithic tail, so
it is now stored as one JSON array per HOL script under
``docs/hol-theorem-map/``. Records whose ``hol_path`` is null (Flapjack-only
classifications such as ``no_hol_reference_pending_classification``) are
grouped by their Lean module under ``docs/hol-theorem-map/no-hol/``.

This module is shared infrastructure: it only derives shard paths, loads and
validates records, and renders byte-stable shard text. It does not change any
review status or source-review semantics; the gates in
``scripts/check_hol_theorem_map.py`` and ``scripts/check_hol_type_hashes.py``
remain authoritative.
"""

from __future__ import annotations

import json
import runpy
from pathlib import Path
from typing import Any, Iterable

ROOT = Path(__file__).resolve().parent.parent
SHARD_DIR = ROOT / "docs" / "hol-theorem-map"
LEGACY_MANIFEST = ROOT / "docs" / "HOL-THEOREM-MAP.json"
NO_HOL_DIRNAME = "no-hol"

_STATUS_MODULE = runpy.run_path(str(ROOT / "scripts" / "check_hol_theorem_map.py"))
REQUIRED_FIELDS: tuple[str, ...] = (
    "hol_path",
    "hol_name",
    "lean_path",
    "lean_name",
    "statement_status",
    "reviewer",
)
# Fields other than reviewer kept in a fixed order for byte-stable output.
STATUS_FIELDS: tuple[str, ...] = REQUIRED_FIELDS[:5]
VALID_STATUSES: frozenset[str] = frozenset(_STATUS_MODULE["VALID_STATUSES"])

# Optional qualifier / line metadata observed in reviewed records.
OPTIONAL_FIELDS: frozenset[str] = frozenset(
    {
        "list_as_array",
        "names_as_string",
        "names_as_string_boundary",
        "fmap_as_finite_support",
        "fmap_as_finite_support_result",
        "fmap_as_finite_support_parameters",
        "fmap_as_finite_support_existentials",
        "fmap_as_finite_support_relation",
        "fmap_as_finite_support_equalities",
        "fmap_as_finite_support_function",
        "words_as_type_indexed_bitvec",
        "word_dimension_as_width",
        "hol_line",
    }
)
ALLOWED_FIELDS: frozenset[str] = frozenset(REQUIRED_FIELDS) | OPTIONAL_FIELDS


def record_key(record: dict[str, Any]) -> tuple[str, str]:
    return (str(record.get("lean_path")), str(record.get("lean_name")))


def shard_relpath(record: dict[str, Any]) -> str:
    """Return the deterministic shard path (POSIX, relative) for a record."""
    hol_path = record.get("hol_path")
    if hol_path:
        return f"{hol_path}.json"
    return f"{NO_HOL_DIRNAME}/{record['lean_path']}.json"


def shard_sort_key(record: dict[str, Any]) -> tuple[str, str, str, str]:
    return (
        str(record.get("hol_path") or ""),
        str(record.get("hol_name") or ""),
        str(record.get("lean_path")),
        str(record.get("lean_name")),
    )


def canonical_record(record: dict[str, Any]) -> dict[str, Any]:
    """Return a record with a fixed key order for byte-stable output."""
    ordered: dict[str, Any] = {}
    for field in STATUS_FIELDS:
        ordered[field] = record[field]
    for field in sorted(record.keys()):
        if field in STATUS_FIELDS or field == "reviewer":
            continue
        ordered[field] = record[field]
    ordered["reviewer"] = record["reviewer"]
    return ordered


def validate_records(records: Iterable[Any]) -> list[dict[str, Any]]:
    """Validate record shape and reject duplicate keys.

    Raises ``ValueError`` on the first structural problem; the caller decides
    how to report it.
    """
    validated: list[dict[str, Any]] = []
    seen: dict[tuple[str, str], str] = {}
    for index, record in enumerate(records, start=1):
        if not isinstance(record, dict):
            raise ValueError(f"record {index}: manifest entry is not an object")
        unknown = set(record) - ALLOWED_FIELDS
        if unknown:
            raise ValueError(f"record {index}: unknown fields {sorted(unknown)}")
        missing = set(REQUIRED_FIELDS) - set(record)
        if missing:
            raise ValueError(f"record {index}: missing fields {sorted(missing)}")
        # hol_path / hol_name are null for Flapjack-only classifications;
        # every other required field must be a string.
        for field in ("hol_path", "hol_name"):
            if record[field] is not None and not isinstance(record[field], str):
                raise ValueError(f"record {index}: {field} must be a string or null")
        for field in ("lean_path", "lean_name", "statement_status", "reviewer"):
            if not isinstance(record[field], str):
                raise ValueError(f"record {index}: {field} must be a string")
        if not record["reviewer"].strip():
            raise ValueError(f"record {index}: reviewer metadata is required")
        status = record["statement_status"]
        if status not in VALID_STATUSES:
            raise ValueError(f"record {index}: invalid statement_status {status!r}")
        if "words_as_type_indexed_bitvec" in record and not isinstance(
            record["words_as_type_indexed_bitvec"], bool
        ):
            raise ValueError(
                f"record {index}: words_as_type_indexed_bitvec must be a bool"
            )
        key = record_key(record)
        if key in seen:
            raise ValueError(
                f"duplicate manifest entry: {key[0]}:{key[1]} (also in {seen[key]})"
            )
        seen[key] = str(record.get("hol_path") or NO_HOL_DIRNAME)
        validated.append(record)
    return validated


def _canonical_records(records: Iterable[dict[str, Any]]) -> list[dict[str, Any]]:
    return [
        canonical_record(record)
        for record in sorted(records, key=shard_sort_key)
    ]


def load_manifest(path: Path | str = LEGACY_MANIFEST) -> list[dict[str, Any]]:
    """Load the manifest from a shard directory or a legacy JSON array file.

    Records are returned in deterministic order with canonical key order.
    """
    path = Path(path)
    if path.is_dir():
        records: list[dict[str, Any]] = []
        for shard in sorted(path.rglob("*.json")):
            payload = json.loads(shard.read_text(encoding="utf-8"))
            if not isinstance(payload, list):
                raise ValueError(f"{shard}: shard root must be a JSON array")
            records.extend(payload)
    else:
        payload = json.loads(path.read_text(encoding="utf-8"))
        if not isinstance(payload, list):
            raise ValueError("manifest root must be a JSON array")
        records = payload
    validate_records(records)
    return _canonical_records(records)


def render_shards(records: Iterable[dict[str, Any]]) -> dict[str, str]:
    """Group records by shard and return ``{relative_path: text}``.

    Every value is byte-stable for a fixed set of records.
    """
    grouped: dict[str, list[dict[str, Any]]] = {}
    for record in records:
        grouped.setdefault(shard_relpath(record), []).append(record)
    rendered: dict[str, str] = {}
    for relpath, group in grouped.items():
        ordered = sorted(group, key=shard_sort_key)
        rendered[relpath] = json.dumps(
            [canonical_record(record) for record in ordered],
            indent=2,
            ensure_ascii=False,
        ) + "\n"
    return rendered


def write_shards(
    root: Path | str, records: Iterable[dict[str, Any]]
) -> list[str]:
    """Write shards under ``root`` and return the relative paths written."""
    root = Path(root)
    rendered = render_shards(records)
    for relpath, text in rendered.items():
        target = root / relpath
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(text, encoding="utf-8")
    return sorted(rendered)


def shard_files(root: Path | str = SHARD_DIR) -> list[Path]:
    root = Path(root)
    if not root.exists():
        return []
    return sorted(root.rglob("*.json"))
