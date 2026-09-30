#!/usr/bin/env python3
"""Load and write the reviewed HOL-tag manifest in a deterministic shard layout.

The canonical record store lives under ``docs/hol-theorem-map/``: one JSON array
per HOL script, and records whose ``hol_path`` is null (Flapjack-only
classifications such as ``no_hol_reference_pending_classification``) grouped by
their Lean module under ``docs/hol-theorem-map/no-hol/``. This per-script layout
avoids the large monolithic tail where concurrent fleet merges conflict.

``docs/HOL-THEOREM-MAP.json`` is a *generated compatibility view* of the
canonical shards, not an independent source of truth. It is produced
deterministically by ``render_compat`` / ``write_compat`` as
``json.dumps(canonical_sorted_records, indent=2, ensure_ascii=False) + "\\n"``
and regenerated with
``python3 scripts/check-hol-theorem-map-shards.py --sync-compat``. The generated
format uses literal Unicode rather than the mixed literal/``\\uXXXX`` escapes the
pre-migration monolith happened to contain; every record's semantic content is
preserved, and the drift checker compares records field-for-field rather than
byte-for-byte, so the generated view is deterministic and byte-stable for a
fixed shard set. Do not hand-edit the compatibility view; edit the shards.

Contributor workflow: edit the per-script shards (or expand a batch JSON array
into shards with ``sync_shards``), then regenerate the compatibility view with
``write_compat`` / ``--sync-compat`` so the two stay in sync. ``load_manifest``
reads either a shard directory or a JSON array file; ``check_drift`` compares
them in both directions and flags missing/changed rows, duplicate keys, and
stale or extra shard files. This module does not change any review status or
source-review semantics.
"""

from __future__ import annotations

import ast
import json
from dataclasses import dataclass, field as dataclass_field
from pathlib import Path
from typing import Any, Iterable

ROOT = Path(__file__).resolve().parent.parent
SHARD_DIR = ROOT / "docs" / "hol-theorem-map"
LEGACY_MANIFEST = ROOT / "docs" / "HOL-THEOREM-MAP.json"
NO_HOL_DIRNAME = "no-hol"

_STATUS_DEFINING_MODULE = ROOT / "scripts" / "check_hol_theorem_map.py"


def _extract_valid_statuses(source_path: Path) -> frozenset[str]:
    """Read ``VALID_STATUSES`` from the checker source without executing it.

    ``check_hol_theorem_map.py`` is expected to import this module once the
    migration lands, so executing it here via ``runpy`` would risk circular
    execution. Instead the literal assignment is extracted from the AST and
    must still be a literal collection of strings.
    """
    tree = ast.parse(
        source_path.read_text(encoding="utf-8"), filename=str(source_path)
    )
    for node in tree.body:
        if isinstance(node, ast.Assign):
            targets = list(node.targets)
        elif isinstance(node, ast.AnnAssign) and node.value is not None:
            targets = [node.target]
        else:
            continue
        for target in targets:
            if isinstance(target, ast.Name) and target.id == "VALID_STATUSES":
                value = ast.literal_eval(node.value)
                if not isinstance(value, (set, frozenset, tuple, list)):
                    raise ValueError("VALID_STATUSES must be a literal collection")
                statuses = frozenset(value)
                if not statuses or not all(isinstance(s, str) for s in statuses):
                    raise ValueError("VALID_STATUSES must be literal strings")
                return statuses
    raise ValueError(f"VALID_STATUSES literal not found in {source_path}")


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
VALID_STATUSES: frozenset[str] = _extract_valid_statuses(_STATUS_DEFINING_MODULE)

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


def _check_safe_relpath(relpath: str) -> str:
    """Reject shard paths that could escape the shard directory.

    A shard path must be a repo-relative POSIX path: no absolute prefix, no
    backslash, no drive/scheme prefix, and no empty, ``.`` or ``..`` component.
    """
    if not relpath or relpath.startswith("/") or "\\" in relpath:
        raise ValueError(f"shard path must be a repo-relative POSIX path: {relpath!r}")
    parts = relpath.split("/")
    if any(part in ("", ".", "..") for part in parts):
        raise ValueError(
            f"shard path must not contain empty, '.' or '..' components: {relpath!r}"
        )
    if ":" in parts[0]:
        raise ValueError(f"shard path must not contain a drive/scheme prefix: {relpath!r}")
    return relpath


def shard_relpath(record: dict[str, Any]) -> str:
    """Return the deterministic shard path (POSIX, relative) for a record."""
    hol_path = record.get("hol_path")
    if hol_path:
        return _check_safe_relpath(f"{hol_path}.json")
    return _check_safe_relpath(f"{NO_HOL_DIRNAME}/{record['lean_path']}.json")


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


def _read_records(path: Path | str) -> list[dict[str, Any]]:
    """Read raw records from a shard directory or a legacy JSON array file.

    This is the non-validating primitive shared by ``load_manifest`` and the
    drift checker. Reading a directory concatenates every ``*.json`` shard in
    sorted order; reading a file expects a JSON array. No shape, status or
    duplicate validation happens here.
    """
    path = Path(path)
    if path.is_dir():
        records: list[dict[str, Any]] = []
        for shard in sorted(path.rglob("*.json")):
            payload = json.loads(shard.read_text(encoding="utf-8"))
            if not isinstance(payload, list):
                raise ValueError(f"{shard}: shard root must be a JSON array")
            records.extend(payload)
        return records
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, list):
        raise ValueError("manifest root must be a JSON array")
    return payload


def load_manifest(path: Path | str = SHARD_DIR) -> list[dict[str, Any]]:
    """Load records from a shard directory or a JSON array compatibility view.

    Records are validated (shape, statuses, duplicates) and returned in
    deterministic order with canonical key order. The default is the canonical
    shard tree; a JSON array file (the generated compatibility view) may also be
    read for batch distribution.
    """
    records = _read_records(path)
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
    root: Path | str,
    records: Iterable[dict[str, Any]],
    *,
    cleanup: bool = False,
) -> list[str]:
    """Write shards under ``root`` and return the relative paths written.

    Records are validated (shape, duplicates, statuses) and every shard path is
    checked as repo-relative before any file is created, so an invalid record
    cannot cause a write outside ``root``. Every resolved target is additionally
    checked against ``root`` before any file is created or written, so a
    pre-existing symlink inside the shard tree cannot redirect a write outside
    the root.

    When ``cleanup`` is true, shard ``*.json`` files that the current records no
    longer produce are removed first (see ``remove_stale_shards``), so a record
    that moves between shards does not leave a duplicate leftover behind. The
    batch-expansion path passes ``cleanup=True``; the default is a
    non-destructive write so callers that only append do not have to reason
    about deletion.
    """
    root = Path(root)
    validated = validate_records(list(records))
    rendered = render_shards(validated)
    # Reject any escaping target before creating or writing any file, so a
    # symlinked shard directory/file cannot redirect a write outside ``root``.
    for relpath in rendered:
        _ensure_within(root, root / relpath)
    if cleanup:
        remove_stale_shards(root, validated)
    for relpath, text in rendered.items():
        target = root / relpath
        target.parent.mkdir(parents=True, exist_ok=True)
        # Re-check after mkdir in case a parent symlink was introduced.
        _ensure_within(root, target)
        target.write_text(text, encoding="utf-8")
    return sorted(rendered)


def render_compat(records: Iterable[dict[str, Any]]) -> str:
    """Render the generated compatibility view text from ``records``.

    The view (``docs/HOL-THEOREM-MAP.json``) is a single JSON array of every
    record in deterministic ``shard_sort_key`` order with canonical key order.
    Output is byte-stable for a fixed record set. It is generated from the
    canonical shards and must not be hand-edited.
    """
    validated = validate_records(list(records))
    ordered = _canonical_records(validated)
    return json.dumps(ordered, indent=2, ensure_ascii=False) + "\n"


def write_compat(path: Path | str, records: Iterable[dict[str, Any]]) -> Path:
    """Write the generated compatibility view to ``path``; return the path.

    The target is resolved against its parent directory before writing, so a
    pre-existing symlink at ``path`` cannot redirect the write outside the
    intended directory.
    """
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    _ensure_within(path.parent, path)
    path.write_text(render_compat(records), encoding="utf-8")
    return path


def _ensure_within(root: Path, candidate: Path) -> Path:
    """Resolve ``candidate`` and reject any path that escapes ``root``.

    Guards against symlinked shard files or directories pointing outside the
    shard root before the cleanup path deletes anything.
    """
    root_resolved = root.resolve()
    candidate_resolved = candidate.resolve()
    if candidate_resolved != root_resolved and root_resolved not in candidate_resolved.parents:
        raise ValueError(
            f"refusing to touch path outside shard root: {candidate} -> {candidate_resolved}"
        )
    return candidate_resolved


def shard_files(root: Path | str = SHARD_DIR) -> list[Path]:
    root = Path(root)
    if not root.exists():
        return []
    return sorted(root.rglob("*.json"))


def stale_shard_files(
    root: Path | str, records: Iterable[dict[str, Any]]
) -> list[str]:
    """Return shard-relative paths of ``*.json`` files no longer produced.

    ``records`` is the record set to test against (the canonical shard records
    when checking internal consistency, or an expanded batch when distributing
    one). Every existing shard path is validated as a safe repo-relative path
    that resolves inside ``root``; an unsafe/escaping path raises ``ValueError``
    instead of being silently ignored.
    """
    root = Path(root)
    if not root.exists():
        return []
    produced = set(render_shards(list(records)))
    stale: list[str] = []
    for shard in sorted(root.rglob("*.json")):
        relpath = _check_safe_relpath(shard.relative_to(root).as_posix())
        _ensure_within(root, shard)
        if relpath not in produced:
            stale.append(relpath)
    return stale


def _prune_empty_dirs(root: Path) -> None:
    """Remove now-empty directories beneath ``root`` (never ``root`` itself)."""
    if not root.exists():
        return
    for path in sorted(root.rglob("*"), key=lambda p: len(p.parts), reverse=True):
        if path.is_dir() and path != root:
            try:
                path.rmdir()
            except OSError:
                pass


def remove_stale_shards(
    root: Path | str, records: Iterable[dict[str, Any]]
) -> list[str]:
    """Delete shard files no longer produced by ``records``; return their paths.

    Rejects unsafe or escaping paths before deleting anything, then prunes any
    directories left empty by the removals.
    """
    root = Path(root)
    stale = stale_shard_files(root, records)
    for relpath in stale:
        target = _ensure_within(root, root / relpath)
        if target.is_symlink() or target.is_file():
            target.unlink()
    _prune_empty_dirs(root)
    return stale


def sync_shards(root: Path | str, records: Iterable[dict[str, Any]]) -> list[str]:
    """Deterministically write shards and remove stale leftovers.

    This is the batch-expansion helper: it distributes an edited JSON array
    (the compatibility view or any equivalent record list) into the canonical
    shard tree, removing leftovers, so the shard tree equals exactly the
    rendered output of ``records``. After expanding a batch change this way,
    regenerate the compatibility view from the shards so the generated view
    reflects the canonical tree.
    """
    return write_shards(root, records, cleanup=True)


def _record_identity(record: dict[str, Any]) -> str:
    return json.dumps(canonical_record(record), sort_keys=True, ensure_ascii=False)


@dataclass
class ManifestDiff:
    """Structured result of comparing canonical shard records with the compat view."""

    missing_from_shards: list[str] = dataclass_field(default_factory=list)
    missing_from_monolith: list[str] = dataclass_field(default_factory=list)
    changed: list[str] = dataclass_field(default_factory=list)
    duplicates_in_shards: list[str] = dataclass_field(default_factory=list)
    duplicates_in_monolith: list[str] = dataclass_field(default_factory=list)
    stale_shard_files: list[str] = dataclass_field(default_factory=list)
    invalid_shards: list[str] = dataclass_field(default_factory=list)
    invalid_monolith: list[str] = dataclass_field(default_factory=list)

    def ok(self) -> bool:
        return not any(
            (
                self.missing_from_shards,
                self.missing_from_monolith,
                self.changed,
                self.duplicates_in_shards,
                self.duplicates_in_monolith,
                self.stale_shard_files,
                self.invalid_shards,
                self.invalid_monolith,
            )
        )

    def messages(self) -> list[str]:
        messages: list[str] = []
        for key in self.missing_from_monolith:
            messages.append(f"record present in shards but missing from monolith: {key}")
        for key in self.missing_from_shards:
            messages.append(f"record present in monolith but missing from shards: {key}")
        for key in self.changed:
            messages.append(f"record differs between shards and monolith: {key}")
        for key in self.duplicates_in_shards:
            messages.append(f"duplicate shard entry: {key}")
        for key in self.duplicates_in_monolith:
            messages.append(f"duplicate monolith entry: {key}")
        for relpath in self.stale_shard_files:
            messages.append(f"stale/extra shard file: {relpath}")
        for message in self.invalid_shards:
            messages.append(f"invalid shard records: {message}")
        for message in self.invalid_monolith:
            messages.append(f"invalid monolith records: {message}")
        return messages


def _key_string(key: tuple[str, str]) -> str:
    return f"{key[0]}:{key[1]}"


def _group_by_key(
    records: Iterable[dict[str, Any]],
) -> tuple[dict[tuple[str, str], list[dict[str, Any]]], list[str]]:
    """Group records by ``record_key``; return groups plus malformed messages."""
    groups: dict[tuple[str, str], list[dict[str, Any]]] = {}
    malformed: list[str] = []
    for index, record in enumerate(records, start=1):
        if not isinstance(record, dict):
            malformed.append(f"entry {index} is not an object")
            continue
        try:
            key = record_key(record)
            canonical_record(record)
        except (KeyError, TypeError) as exc:
            malformed.append(f"entry {index} is missing required fields ({exc})")
            continue
        groups.setdefault(key, []).append(record)
    return groups, malformed


def compare_records(
    shard_records: Iterable[dict[str, Any]],
    monolith_records: Iterable[dict[str, Any]],
) -> ManifestDiff:
    """Compare shard and monolith records as canonical records.

    Equality is exact and field-for-field over canonical records (key order
    does not matter). The comparison is order-insensitive and detects duplicate
    keys on either side. It returns structured diagnostics; it never raises for
    a mere disagreement.
    """
    diff = ManifestDiff()
    shard_groups, shard_malformed = _group_by_key(shard_records)
    mono_groups, mono_malformed = _group_by_key(monolith_records)
    diff.invalid_shards.extend(shard_malformed)
    diff.invalid_monolith.extend(mono_malformed)
    for key, group in shard_groups.items():
        if len(group) > 1:
            diff.duplicates_in_shards.append(_key_string(key))
    for key, group in mono_groups.items():
        if len(group) > 1:
            diff.duplicates_in_monolith.append(_key_string(key))
    shard_keys = set(shard_groups)
    mono_keys = set(mono_groups)
    for key in sorted(mono_keys - shard_keys):
        diff.missing_from_shards.append(_key_string(key))
    for key in sorted(shard_keys - mono_keys):
        diff.missing_from_monolith.append(_key_string(key))
    for key in sorted(shard_keys & mono_keys):
        shard_identities = {_record_identity(r) for r in shard_groups[key]}
        mono_identities = {_record_identity(r) for r in mono_groups[key]}
        if shard_identities != mono_identities:
            diff.changed.append(_key_string(key))
    return diff


def check_drift(
    shard_root: Path | str = SHARD_DIR,
    monolith_path: Path | str = LEGACY_MANIFEST,
) -> ManifestDiff:
    """Fail-worthy drift report for the canonical shards versus the compat view.

    The shard tree is canonical and ``docs/HOL-THEOREM-MAP.json`` is its
    generated compatibility view. The comparison is bidirectional and
    content-level (order-insensitive, duplicate-detecting): it reports
    record-level disagreements in either direction, duplicate keys on either
    side, invalid records, and stale/extra shard files (shard files that the
    canonical record set does not produce).
    """
    shard_records = _read_records(shard_root)
    monolith_records = _read_records(monolith_path)
    diff = compare_records(shard_records, monolith_records)
    try:
        validate_records(shard_records)
    except ValueError as exc:
        diff.invalid_shards.append(str(exc))
    try:
        validate_records(monolith_records)
    except ValueError as exc:
        diff.invalid_monolith.append(str(exc))
    diff.stale_shard_files = stale_shard_files(shard_root, shard_records)
    return diff
