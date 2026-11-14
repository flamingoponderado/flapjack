#!/usr/bin/env python3
"""Check reviewed theorem-map rows against the elaborated `@[hol]` attributes.

`scripts/HolRefExport.lean` lists every tagged declaration with the qualifiers
recorded by its elaborated `@[hol]` attribute and, unless the declaration itself
carries `(reals_as_rational_cuts)`, whether its constant closure reaches a
declaration that does. For every `reviewed_*` row of `docs/HOL-THEOREM-MAP.json`
this script requires

* exactly one tagged declaration with the row's HOL reference and Lean leaf name,
* the manifest qualifiers to equal the elaborated qualifiers, and
* the manifest `inherits_reals_as_rational_cuts` marker to equal the closure.

This is a consistency gate between the manifest and the Lean attributes. It does
not pin declaration statements or bodies, and it does not prove HOL-to-Lean
equivalence or replace source-level review.
"""

from __future__ import annotations

import json
import hashlib
import re
import runpy
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parent.parent
MANIFEST = ROOT / "docs" / "HOL-THEOREM-MAP.json"
EXPORTER = ROOT / "scripts" / "HolRefExport.lean"
NESTED_AUDIT = ROOT / "Flapjack" / "Test" / "NestedRelationAudit.lean"
NESTED_AUDIT_SHA256 = "77f30bebc1f3622d310d980cf94d13f24b54716d802215872653e111cf34c2c6"
# Eight batches reduce peak import memory while avoiding hundreds of Lake starts.
EXPORT_BATCH_COUNT = 8


def validate_nested_audit_source(source: str) -> None:
    """Require the source-reviewed audit; this does not establish HOL correspondence."""
    if hashlib.sha256(source.encode("utf-8")).hexdigest() != NESTED_AUDIT_SHA256:
        raise ValueError("nested-list relation audit changed and requires source re-review")
    source = runpy.run_path(str(ROOT / "scripts" / "check-hol-refs.py"))["strip_lean_comments"](source)
    required = (
        "private def expectedNumberRule", "private def expectedWordRule",
        "private def expectedBlockRule", "private def expectedBytesRule",
        "private def expectedPointerRule", "private def expectedClosureRule",
        "private def expectedRecclosureRule", "private def expectedOutsideRule",
        "private def expectedLocalRule", "private def expectedCapturedRule",
        "private def expectedFunctionsNilRule", "private def expectedFunctionsConsRule",
        "private def expectedFunctionsWitness", "for (ruleName, expectedName) in rules do",
        "Lean.Meta.isDefEq rule.type expected.value",
        "Lean.Meta.isDefEq witness.type expectedWitness.value",
        "Lean.collectAxioms ``functionsRel_iff",
    )
    if any(source.count(item) != 1 for item in required):
        raise ValueError("nested-list relation audit is missing required checks")
    marker = "theorem nestedRelationAudit_passed : True := trivial"
    if source.count(marker) != 1 or source.index(marker) < source.index("Lean.collectAxioms ``functionsRel_iff"):
        raise ValueError("nested-list relation audit marker must follow the audit")

ALLOWED_QUALIFIERS = {
    "list_as_array", "names_as_string", "names_as_string_boundary",
    "fmap_as_finite_support", "fmap_as_finite_support_result",
    "fmap_as_finite_support_function",
    "fmap_as_finite_support_tuple",
    "fmap_as_finite_support_heterogeneous_function",
    "fmap_as_finite_support_result_observations",
    "fmap_as_finite_support_parameter_observations",
    "fmap_as_finite_support_parameter_predicate_domain",
    "fmap_as_finite_support_parameters",
    "fmap_as_finite_support_existentials",
    "fmap_as_finite_support_relation", "fmap_as_finite_support_equalities",
    "fmap_as_finite_support_equality",
    "words_as_type_indexed_bitvec",
    "word_dimension_as_width", "word_dimensions_as_widths",
    "reals_as_rational_cuts",
    "nested_list_rel_as_mutual",
}
BOOLEAN_QUALIFIERS = {
    "fmap_as_finite_support_result", "fmap_as_finite_support_equalities",
    "fmap_as_finite_support_equality", "words_as_type_indexed_bitvec",
    "reals_as_rational_cuts",
    "fmap_as_finite_support_parameter_observations",
}


def validate_export_record(record: Any, line_number: int) -> dict[str, Any]:
    """Reject malformed exporter output."""
    if not isinstance(record, dict):
        raise ValueError(f"Lean export line {line_number} is not an object")
    required = {"lean_name", "hol_path", "hol_name"}
    allowed = required | {"qualifiers", "inherits_reals_as_rational_cuts"}
    if not required.issubset(record) or not set(record) <= allowed:
        raise ValueError(f"Lean export line {line_number} has invalid fields")
    non_string = [key for key in required if not isinstance(record[key], str)]
    if non_string:
        raise ValueError(f"Lean export line {line_number} has non-string fields {non_string}")
    if not isinstance(record.get("inherits_reals_as_rational_cuts", False), bool):
        raise ValueError(
            f"Lean export line {line_number} has a non-boolean inherits_reals_as_rational_cuts"
        )
    qualifiers = record.get("qualifiers", {})
    if not isinstance(qualifiers, dict) or not set(qualifiers) <= ALLOWED_QUALIFIERS:
        raise ValueError(f"Lean export line {line_number} has invalid qualifiers")
    if any(
        (
            not isinstance(value, bool)
            if key in BOOLEAN_QUALIFIERS
            else not isinstance(value, str)
            if key == "word_dimension_as_width"
            else not isinstance(value, list) or not all(isinstance(field, str) for field in value)
        )
        for key, value in qualifiers.items()
    ):
        raise ValueError(f"Lean export line {line_number} has malformed qualifier fields")
    return record


def export_batches(umbrella: str, exporter: str, count: int = EXPORT_BATCH_COUNT) -> list[str]:
    """Partition the original imports without silently dropping umbrella declarations."""
    strip_comments = runpy.run_path(str(ROOT / "scripts" / "check-hol-refs.py"))["strip_lean_comments"]
    marker = "\nopen Lean Elab Command Flapjack"
    if exporter.count(marker) != 1:
        raise ValueError("unexpected HOL exporter header")
    header, body = exporter.split(marker, 1)
    pattern = re.compile(r"import ([A-Za-z_][A-Za-z0-9_.]*)\Z")

    def imports(source: str) -> list[str]:
        result = []
        for line in strip_comments(source).splitlines():
            line = line.strip()
            if not line:
                continue
            match = pattern.fullmatch(line)
            if not match:
                raise ValueError(f"unexpected declaration in import-only file: {line}")
            result.append(match.group(1))
        return result

    direct = imports(header)
    if direct.count("Flapjack") != 1 or direct.count("Flapjack.Test.NestedRelationAudit") != 1:
        raise ValueError("HOL exporter must import the umbrella and nested relation audit")
    all_imports = list(dict.fromkeys(
        imports(umbrella) + [name for name in direct if name not in
                             {"Flapjack", "Flapjack.Test.NestedRelationAudit"}]
    ))
    if not all_imports or "Flapjack" in all_imports:
        raise ValueError("invalid umbrella imports for HOL export")
    batches = []
    for index in range(count):
        selected = all_imports[len(all_imports) * index // count:len(all_imports) * (index + 1) // count]
        batch_header = "\n".join(f"import {name}" for name in
                                 ["Flapjack.Test.NestedRelationAudit", *selected])
        batches.append(batch_header + marker + body)
    return batches


def exported_refs() -> list[dict[str, Any]]:
    # Each batch is freshly set up by Lake, rather than reusing a saved setup
    # that may reference OLeans from an older source revision. Batches run
    # sequentially so their builds cannot race over Lake artifacts.
    batches = export_batches((ROOT / "Flapjack.lean").read_text(), EXPORTER.read_text())
    records: dict[str, dict[str, Any]] = {}
    (ROOT / ".lake").mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="hol-ref-export-", dir=ROOT / ".lake") as directory:
        for index, source in enumerate(batches):
            path = Path(directory) / f"Export{index}.lean"
            path.write_text(source)
            result = subprocess.run(
                ["lake", "--quiet", "lean", str(path)], cwd=ROOT,
                text=True, capture_output=True, check=False,
            )
            if result.returncode:
                raise RuntimeError(
                    f"Lean @[hol] export batch {index + 1} failed (exit {result.returncode}):\n"
                    f"{result.stdout}{result.stderr}"
                )
            seen_in_batch: set[str] = set()
            for line_number, line in enumerate(result.stdout.splitlines(), 1):
                try:
                    record = json.loads(line)
                except json.JSONDecodeError as error:
                    raise ValueError(
                        f"Lean export batch {index + 1} line {line_number} is not JSON: {line[:160]}"
                    ) from error
                record = validate_export_record(record, line_number)
                name = record["lean_name"]
                if name in seen_in_batch:
                    raise ValueError(f"duplicate declaration in Lean export batch: {name}")
                seen_in_batch.add(name)
                if name in records and records[name] != record:
                    raise ValueError(f"Lean export batches disagree on {name}")
                records[name] = record
    if not records:
        raise ValueError("Lean @[hol] export returned no declarations")
    return list(records.values())


def manifest_qualifiers(record: dict[str, Any]) -> dict[str, Any]:
    """The qualifiers a manifest row records, in the exporter's encoding."""
    qualifiers: dict[str, Any] = {
        "list_as_array": list(record.get("list_as_array", ())),
        "names_as_string": list(record.get("names_as_string", ())),
        "names_as_string_boundary": list(record.get("names_as_string_boundary", ())),
        "fmap_as_finite_support": list(record.get("fmap_as_finite_support", ())),
    }
    if record.get("statement_status") == "reviewed_fmap_as_finite_support_parameter_observations":
        qualifiers["fmap_as_finite_support_parameter_observations"] = True
    for key in (
        "fmap_as_finite_support_relation",
        "fmap_as_finite_support_function",
        "fmap_as_finite_support_tuple",
        "fmap_as_finite_support_heterogeneous_function",
        "fmap_as_finite_support_result_observations",
        "fmap_as_finite_support_parameters",
        "fmap_as_finite_support_parameter_predicate_domain",
        "fmap_as_finite_support_existentials",
        "word_dimensions_as_widths",
        "nested_list_rel_as_mutual",
    ):
        if record.get(key, ()):
            qualifiers[key] = list(record[key])
    for key in BOOLEAN_QUALIFIERS:
        if record.get(key, False):
            qualifiers[key] = True
    if record.get("word_dimension_as_width") is not None:
        qualifiers["word_dimension_as_width"] = record["word_dimension_as_width"]
    return qualifiers


def check_records(
    manifest: list[dict[str, Any]], exports: list[dict[str, Any]]
) -> int:
    """Check every reviewed row against its elaborated declaration.

    Rows are matched by HOL reference and Lean leaf name: one HOL theorem may
    have several Lean cases, while Lean leaf names may recur in separate
    namespaces. Ambiguity fails rather than choosing an arbitrary declaration.
    Returns the number of reviewed rows checked.
    """
    by_key: dict[tuple[str, str, str], list[dict[str, Any]]] = {}
    for item in exports:
        key = (item["hol_path"], item["hol_name"], item["lean_name"].rsplit(".", 1)[-1])
        by_key.setdefault(key, []).append(item)
    checked = 0
    for record in manifest:
        if not str(record.get("statement_status", "")).startswith("reviewed_"):
            continue
        # Source scanners retain Lean's escaped identifier delimiters, while
        # Name.toString exports the underlying leaf (e.g. dfn'FMIN_S).
        leaf = record["lean_name"]
        if leaf.startswith("«") and leaf.endswith("»"):
            leaf = leaf[1:-1]
        key = (record["hol_path"], record["hol_name"], leaf)
        candidates = by_key.get(key, [])
        if len(candidates) != 1:
            raise ValueError(
                f"{record['lean_path']}:{record['lean_name']}: "
                f"expected one tagged declaration for {key}, found {len(candidates)}"
            )
        item = candidates[0]
        qualifiers = manifest_qualifiers(record)
        exported_qualifiers = item.get("qualifiers", {})
        if any(exported_qualifiers.get(name, []) != value
               for name, value in qualifiers.items()):
            raise ValueError(
                f"{record['lean_path']}:{record['lean_name']}: manifest qualifiers "
                "differ from elaborated @[hol] exporter"
            )
        if (exported_qualifiers.get("fmap_as_finite_support_tuple", []) !=
                qualifiers.get("fmap_as_finite_support_tuple", [])):
            raise ValueError(
                f"{record['lean_path']}:{record['lean_name']}: tuple-map qualifier "
                "differs from elaborated @[hol] exporter"
            )
        if (exported_qualifiers.get("nested_list_rel_as_mutual", []) !=
                qualifiers.get("nested_list_rel_as_mutual", [])):
            raise ValueError(
                f"{record['lean_path']}:{record['lean_name']}: nested-list relation qualifier "
                "differs from elaborated @[hol] exporter"
            )
        if (exported_qualifiers.get("reals_as_rational_cuts", False)
                and not qualifiers.get("reals_as_rational_cuts", False)):
            raise ValueError(
                f"{record['lean_path']}:{record['lean_name']}: elaborated @[hol] carries "
                "reals_as_rational_cuts but the manifest record does not"
            )
        exported_inherits = bool(item.get("inherits_reals_as_rational_cuts", False))
        manifest_inherits = bool(record.get("inherits_reals_as_rational_cuts", False))
        if exported_inherits != manifest_inherits:
            raise ValueError(
                f"{record['lean_path']}:{record['lean_name']}: manifest "
                f"inherits_reals_as_rational_cuts={manifest_inherits} but the elaborated "
                f"declaration closure gives {exported_inherits}"
            )
        checked += 1
    return checked


def main() -> int:
    try:
        validate_nested_audit_source(NESTED_AUDIT.read_text(encoding="utf-8"))
        manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))
        checked = check_records(manifest, exported_refs())
        print(f"{checked} reviewed theorem-map rows match their elaborated @[hol] attributes")
        return 0
    except (OSError, ValueError, RuntimeError, subprocess.SubprocessError) as error:
        print(f"HOL reference export check failed: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
