#!/usr/bin/env python3
"""Detect drift between HOL probe scripts, their captured ``.out`` rows, and a
committed content lock.

Run with the repository's Python test suite (CI executes
``python3 -m unittest discover -s scripts/tests -p 'test_check_hol*.py'``) or
directly:

    python3 scripts/check-hol-probe-rows.py

The checker has three independent, deterministic parts.

1. Structural coverage. Every ``scripts/hol-probes/<name>.out`` is parsed into
   rows of the form ``label=value`` (the value may span continuation lines; a
   new row starts at the first column with ``^[A-Za-z][A-Za-z0-9_]*=``). For
   probes whose ``<name>_probeScript.sml`` prints rows through a statically
   detectable helper (``print (label ^ "=")`` or ``print label; print "="``,
   including thin wrappers) the printed label set and the captured label set
   must agree exactly and the ``.out`` must not repeat a label. Probes that use
   a different printing convention are listed in ``UNSUPPORTED``; probes whose
   committed ``.out`` deliberately omits named script rows are listed in
   ``PARTIAL_OUT``. A probe that is neither classified as supported, partial,
   nor unsupported fails the check, so a new convention cannot be dropped
   silently.

2. Content lock. ``scripts/hol-probes/rows.lock.json`` records the SHA-256 of
   every captured ``.out``. Any change to an ``.out`` byte, whether a value, a
   label, or a row addition/removal, fails until the lock is regenerated with
   ``--update`` after review.

3. Driver structure. Literal ``run_probe`` registrations in ``regenerate.sh``
   must supply a source path and, optionally, a working directory after their
   labels. A dangling continuation must not absorb another registration.

This gate does not evaluate HOL. The probe scripts and ``.out`` files are
committed artifacts, so the checker compares them against each other and
against the lock; it does not prove that the captured values are correct. The
per-row Lean transcriptions cannot be cross-checked mechanically: no
``Flapjack/Test`` module stores a probe row as a ``"label=value"`` string
literal, and the few ``-- label=value`` comment rows are partial, annotated
(for example ``crep_invalid_four=NONE`` with a trailing explanation), or split
across several probes, so there is no deterministic textual key to match
against. Tightening the gate to the Lean expectations would require adding a
machine-readable row mapping to each test, which is out of scope here; the
content lock plus the script/out label comparison is the deterministic
equivalent.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import shlex
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
PROBES = ROOT / "scripts" / "hol-probes"
LOCK = PROBES / "rows.lock.json"

LABEL_RE = re.compile(r"^([A-Za-z][A-Za-z0-9_]*)=(.*)$")
DEF_RE = re.compile(r"(?m)^(?:fun|val)\s+([A-Za-z][A-Za-z0-9_]*)[^\n]*?=")
NEXT_DEF_RE = re.compile(r"(?m)^(fun|val|local|end)\b")

# Probes whose printed labels cannot be recovered statically. Their ``.out`` is
# still covered by the content lock; only the script/out label comparison is
# skipped.
UNSUPPORTED = {
    "compile_panop_probe.out": (
        "prints a bare HOL term with no `label=` row convention"
    ),
    "crep_to_loop_evaluate_io_mono_type_probe.out": (
        "prints repeated `free_variable` labels and embeds labels inside "
        "multi-line strings (`print \"\\nloop_source_type=\"`)"
    ),
    "crep_to_loop_write_bytearray_mem_rel_probe.out": (
        "the local `row` helper composes labels (`<base>_pan` / `<base>_word`) "
        "that are not static literals"
    ),
    "loop_to_word_compile_correct_cases_probe.out": (
        "labels are built dynamically (`print (\"cc_case_\" ^ n ^ \"=\")`)"
    ),
    "reg_alloc_mk_bij_probe.out": (
        "the local `print_bij` helper composes suffix labels from a base name"
    ),
}

# Supported probes whose committed ``.out`` deliberately records a subset of
# the rows the probe script prints. The listed script labels are expected to be
# absent; every other script label must still appear and every ``.out`` label
# must still be printed by the script.
PARTIAL_OUT: dict[str, tuple[frozenset[str], str]] = {
    "crep_arith_lookup_code_probe.out": (
        frozenset({"wrong_arity", "duplicate_parameters", "missing_function"}),
        "the committed `.out` records only the nonempty-code-map result row; "
        "the probe also prints three `lookup_code` failure rows",
    ),
    "crep_primop_loop_primop_probe.out": (
        frozenset({"crep_primop_loop_primop_done"}),
        "final `_done` status marker is not a captured data row",
    ),
    "loop_props_assigned_vars_probe.out": (
        frozenset({"avs_nested_assign_negative"}),
        "the committed `.out` omits this row (curated subset)",
    ),
    "loop_sem_sh_mem_load_probe.out": (
        frozenset({"byte_align_three"}),
        "the committed `.out` omits the standalone `byte_align` helper row "
        "(curated subset)",
    ),
    "pan_to_crep_slc_tlc_probe.out": (
        frozenset({"slc_tlc_probe_done"}),
        "final `_done` status marker is not a captured data row",
    ),
    "pan_to_crep_state_rel_carrier_probe.out": (
        frozenset({"state_rel_carrier_probe_done"}),
        "final `_done` status marker is not a captured data row",
    ),
}


def read_text(path: Path) -> str:
    return path.read_text(encoding="utf-8", errors="replace")


def parse_rows(text: str) -> list[tuple[str, str]]:
    """Parse ``label=value`` rows, where a value may span continuation lines.

    Blank lines separate records and are dropped. Lines before the first label
    (HOL banners and load-path noise) are ignored.
    """
    rows: list[list[object]] = []
    current: list[object] | None = None
    for raw in text.splitlines():
        line = raw.rstrip()
        if not line.strip():
            continue
        match = LABEL_RE.match(line)
        if match:
            current = [match.group(1), [match.group(2)]]
            rows.append(current)
        elif current is not None:
            current[1].append(line)  # type: ignore[union-attr]
    return [(label, "\n".join(lines).strip()) for label, lines in rows]  # type: ignore[misc]


def definition_bodies(text: str) -> list[tuple[str, str]]:
    """Return ``(name, body)`` for each top-level ``fun``/``val`` definition."""
    result: list[tuple[str, str]] = []
    for match in DEF_RE.finditer(text):
        rest = text[match.end():]
        following = NEXT_DEF_RE.search(rest)
        end = match.end() + following.start() if following else len(text)
        result.append((match.group(1), text[match.start():end]))
    return result


def script_printed_labels(text: str) -> tuple[set[str], set[str]]:
    """Return the printed label set and the detected label-printer names.

    A definition is a label printer when its body prints ``label`` (either
    ``label ^ "="`` or ``print label``), or when it forwards its ``label``
    parameter to another label printer. String literals passed as the first
    argument to a label printer are collected, together with labels printed
    directly as ``print "label=..."``.
    """
    bodies = definition_bodies(text)
    printers: set[str] = set()
    for name, body in bodies:
        if re.search(r"print\s*\(?\s*label\b", body) or re.search(r"label\s*\^", body):
            printers.add(name)
    changed = True
    while changed:
        changed = False
        for name, body in bodies:
            if name in printers:
                continue
            for helper in printers:
                if re.search(
                    r"\b" + re.escape(helper) + r"\b[^;]*\blabel\b", body
                ):
                    printers.add(name)
                    changed = True
                    break
    labels: set[str] = set()
    for helper in printers:
        for match in re.finditer(
            r"\b" + re.escape(helper) + r'\s+"([A-Za-z][A-Za-z0-9_]*)"', text
        ):
            labels.add(match.group(1))
    for match in re.finditer(r'print\s*\(?\s*"([A-Za-z][A-Za-z0-9_]*)=', text):
        labels.add(match.group(1))
    return labels, printers


def out_files(probes_dir: Path) -> list[Path]:
    return sorted(probes_dir.glob("*.out"))


def expected_lock(probes_dir: Path) -> list[dict[str, object]]:
    records: list[dict[str, object]] = []
    for out in out_files(probes_dir):
        raw = out.read_bytes()
        rows = parse_rows(raw.decode("utf-8", errors="replace"))
        records.append(
            {
                "out": out.name,
                "sha256": hashlib.sha256(raw).hexdigest(),
                "bytes": len(raw),
                "rows": len(rows),
            }
        )
    return records


def render_lock(records: list[dict[str, object]]) -> str:
    """Render the content lock in the canonical pretty indent-2 format.

    Keys are emitted in a fixed order so that ``--update`` (and any manual
    merge union routed through it) always reproduces the canonical rendering
    instead of churning unrelated records.
    """
    ordered = [
        {key: record[key] for key in ("bytes", "out", "rows", "sha256")}
        for record in records
    ]
    return json.dumps({"version": 1, "records": ordered}, indent=2) + "\n"


def check_structural(probes_dir: Path) -> list[str]:
    errors: list[str] = []
    for out in out_files(probes_dir):
        name = out.name
        rows = parse_rows(read_text(out))
        labels = [label for label, _ in rows]
        script = probes_dir / (out.stem + "Script.sml")

        if name in UNSUPPORTED:
            continue
        if not script.is_file():
            errors.append(f"{name}: missing probe script {script.name}")
            continue

        duplicates = sorted(
            {label for label in labels if labels.count(label) > 1}
        )
        if duplicates:
            errors.append(f"{name}: duplicate label(s) {duplicates}")

        script_labels, _printers = script_printed_labels(read_text(script))
        if not script_labels:
            errors.append(
                f"{name}: probe script has no statically detectable printed "
                "labels and is not in the documented UNSUPPORTED list"
            )
            continue

        missing_from_out = script_labels - set(labels)
        missing_from_script = set(labels) - script_labels
        if name in PARTIAL_OUT:
            allowed_missing, _ = PARTIAL_OUT[name]
            extra = missing_from_out - allowed_missing
            if extra:
                errors.append(
                    f"{name}: probe script prints {sorted(extra)} but the "
                    "committed `.out` omits them without a PARTIAL_OUT entry"
                )
        elif missing_from_out:
            errors.append(
                f"{name}: probe script prints {sorted(missing_from_out)} that "
                "the committed `.out` does not record"
            )
        if missing_from_script:
            errors.append(
                f"{name}: `.out` records label(s) {sorted(missing_from_script)} "
                "that the probe script does not print"
            )
    return errors


def check_lock(probes_dir: Path, lock_path: Path) -> list[str]:
    records = expected_lock(probes_dir)
    if not lock_path.is_file():
        return [f"{lock_path}: missing content lock; run --update to create it"]
    committed = json.loads(read_text(lock_path))
    old = {record["out"]: record for record in committed.get("records", [])}
    new = {record["out"]: record for record in records}
    changed = sorted(
        name for name in old.keys() | new.keys() if old.get(name) != new.get(name)
    )
    if not changed:
        if read_text(lock_path) != render_lock(records):
            return [
                f"{lock_path}: captured content matches but rendering is not the "
                "canonical indent-2 form; run --update to normalise the lock"
            ]
        return []
    detail = ", ".join(changed[:12]) + (" ..." if len(changed) > 12 else "")
    return [
        f"captured `.out` lock differs for {len(changed)} file(s): {detail}; "
        "review the regenerated rows, update the Lean replay, then run --update"
    ]


def check_registrations(text: str) -> list[str]:
    """Check literal run_probe commands without executing the shell script."""
    errors = []
    logical = re.sub(r"\\\r?\n", " ", text)
    for number, line in enumerate(logical.splitlines(), 1):
        if not re.match(r"^run_probe\s", line):
            continue
        tokens = shlex.split(line, comments=True)
        source = next((i for i in range(3, len(tokens))
                       if tokens[i].startswith(("$", "/"))), len(tokens))
        paths = tokens[source:]
        if (len(tokens) < 4 or tokens.count("run_probe") != 1
                or not tokens[1].endswith("Script.sml")
                or not tokens[2].endswith(".out")
                or len(paths) not in (1, 2)
                or not paths[0].endswith("Script.sml")
                or (len(paths) == 2 and not paths[1].startswith(("$", "/")))
                or any(not re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*", label)
                       for label in tokens[3:source])):
            errors.append(f"regenerate.sh logical line {number}: malformed run_probe "
                          "registration (expected labels followed by source and optional directory)")
    return errors


def check(probes_dir: Path, lock_path: Path) -> None:
    errors = check_structural(probes_dir) + check_lock(probes_dir, lock_path)
    driver = probes_dir / "regenerate.sh"
    if driver.is_file():
        errors += check_registrations(read_text(driver))
    if errors:
        raise ValueError("\n".join(errors))


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--update",
        action="store_true",
        help="rewrite the captured-.out content lock after review",
    )
    args = parser.parse_args()
    try:
        if args.update:
            records = expected_lock(PROBES)
            LOCK.write_text(render_lock(records), encoding="utf-8")
            print(f"wrote {len(records)} captured-.out hashes to {LOCK}")
            return 0
        check(PROBES, LOCK)
        supported = len(out_files(PROBES)) - len(UNSUPPORTED)
        skipped = ", ".join(sorted(UNSUPPORTED))
        print(
            f"hol-probe rows OK: {len(out_files(PROBES))} captured outputs "
            f"locked, {supported} label-checked"
        )
        if skipped:
            print(f"label check skipped (documented): {skipped}")
        return 0
    except (OSError, ValueError, KeyError) as error:
        print(f"HOL probe row check failed: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
