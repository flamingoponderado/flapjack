#!/usr/bin/env python3
"""Verify `@[hol "<path>" "<name>"]` cross-references and emit the HOL-to-Lean map.

Every Lean declaration that ports a HOL4 declaration carries
`@[hol "cakeml/.../fooScript.sml" "theorem_name"]` (see `Flapjack/HolRef.lean`
and `AGENTS.md`).  This script checks, without running Lean, that

* the cited file exists in the `cakeml` submodule, and
* a HOL declaration with exactly that name is declared in that file; when
  the name is duplicated, the tag must cite a matching source line
  (`Theorem`, `Triviality`, `Definition`, `Datatype`, `Inductive`,
  `CoInductive`, `Overload`, `Type`, or an SML-level `val name = ...`), and
* the Lean module carrying the tag is transitively imported from the library
  root `Flapjack.lean`, so `lake build Flapjack` actually elaborates it.  A
  tagged theorem in an orphaned module would otherwise count as ported while
  never being checked.

Usage:
  scripts/check-hol-refs.py            # check; exit 1 on any bad reference
  scripts/check-hol-refs.py --mapping  # also print a TSV mapping to stdout:
                                       #   lean_file:line  lean_decl  hol_path  hol_name[:line]
  scripts/check-hol-refs.py --orphans  # also list every non-test module that is
                                       # not reachable from Flapjack.lean (warning only)

Uses only the standard library.
"""

from __future__ import annotations

import os
import re
import sys
from functools import lru_cache
from collections.abc import Iterable
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LEAN_DIRS = [ROOT / "Flapjack", ROOT / "Flapjack.lean"]

ATTR_RE = re.compile(r'\bhol\s+"([^"]+)"\s+"([^"]+)"(?:\s+(\d+))?')
QUALIFIER_RE = re.compile(r'\(\s*list_as_array\s*:=\s*\[([^]]*)\]\s*\)')
NAMES_AS_STRING_RE = re.compile(r'\(\s*names_as_string\s*:=\s*\[([^]]*)\]\s*\)')
NAMES_AS_STRING_BOUNDARY_RE = re.compile(
    r'\(\s*names_as_string_boundary\s*:=\s*\[([^]]*)\]\s*\)'
)
FMAP_AS_FINITE_SUPPORT_RE = re.compile(
    r'\(\s*fmap_as_finite_support\s*:=\s*\[([^]]*)\]\s*\)'
)
FMAP_AS_FINITE_SUPPORT_RESULT_RE = re.compile(
    r'\(\s*fmap_as_finite_support_result\s*\)'
)
FMAP_AS_FINITE_SUPPORT_RELATION_RE = re.compile(
    r'\(\s*fmap_as_finite_support_relation\s*:=\s*\[([^]]*)\]\s*\)'
)
FMAP_AS_FINITE_SUPPORT_EQUALITIES_RE = re.compile(
    r'\(\s*fmap_as_finite_support_equalities\s*\)'
)
RELATION_FIELD_RE = re.compile(
    r'^\s*([A-Za-z_][A-Za-z0-9_\']*)\s*\.\s*([A-Za-z_][A-Za-z0-9_\']*)\s*$'
)
DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance|inductive|structure|class|opaque|axiom)\s+"
    r"([^\s:({\[]+)"
)
HOL_HEADER_KEYWORDS = (
    "Theorem",
    "Triviality",
    "Definition",
    "Datatype",
    "Inductive",
    "CoInductive",
    "Overload",
    "Type",
)
IMPORT_RE = re.compile(r"^import\s+(Flapjack(?:\.[A-Za-z0-9_]+)*)", re.M)


def module_name(path: Path) -> str:
    rel = path.relative_to(ROOT).with_suffix("")
    return ".".join(rel.parts)


def module_path(module: str) -> Path:
    return ROOT / (module.replace(".", "/") + ".lean")


def reachable_modules(root: str = "Flapjack") -> set[str]:
    """Modules transitively imported from the library root."""
    seen: set[str] = set()
    stack = [root]
    while stack:
        module = stack.pop()
        if module in seen:
            continue
        seen.add(module)
        path = module_path(module)
        if not path.is_file():
            continue
        for imported in IMPORT_RE.findall(path.read_text(encoding="utf-8")):
            if imported not in seen:
                stack.append(imported)
    return seen


def lean_files() -> list[Path]:
    files: list[Path] = []
    for entry in LEAN_DIRS:
        if entry.is_file():
            files.append(entry)
        elif entry.is_dir():
            files.extend(sorted(entry.rglob("*.lean")))
    return files


def find_lean_decl(lines: list[str], start: int) -> str:
    """Name of the declaration that the attribute at `lines[start]` decorates."""
    for offset in range(0, 8):
        index = start + offset
        if index >= len(lines):
            break
        match = DECL_RE.match(lines[index])
        if match:
            return match.group(1)
    return "?"


def hol_attribute_sites(lines: list[str]):
    """Yield HOL attributes, including attributes split across Lean lines."""
    comment_depth = 0
    start: int | None = None
    chunks: list[str] = []
    attribute_bracket_depth = 0
    for number, line in enumerate(lines, start=1):
        # Ignore documentation/examples in nestable Lean block comments.
        in_comment = comment_depth > 0
        comment_depth += line.count("/-") - line.count("-/")
        if in_comment or comment_depth > 0:
            continue
        stripped = line.lstrip()
        if stripped.startswith("--"):
            continue
        if start is None:
            if not stripped.startswith("@["):
                continue
            start = number
            attribute_bracket_depth = 0
        chunks.append(stripped)
        attribute_bracket_depth += stripped.count("[") - stripped.count("]")
        if attribute_bracket_depth > 0:
            continue
        attribute = " ".join(chunks)
        if "hol " in attribute:
            for hol_path, hol_name, hol_line in ATTR_RE.findall(attribute):
                def fields_for(pattern: re.Pattern[str]) -> tuple[str, ...]:
                    qualifier = pattern.search(attribute)
                    return tuple(
                        field.strip() for field in qualifier.group(1).split(",")
                    ) if qualifier else ()

                def relation_fields_for() -> tuple[tuple[str, str], ...]:
                    qualifier = FMAP_AS_FINITE_SUPPORT_RELATION_RE.search(attribute)
                    if not qualifier:
                        return ()
                    entries: list[tuple[str, str]] = []
                    for raw in qualifier.group(1).split(","):
                        match = RELATION_FIELD_RE.match(raw)
                        if match:
                            entries.append((match.group(1), match.group(2)))
                        elif raw.strip():
                            entries.append((raw.strip(), ""))
                    return tuple(entries)

                yield (
                    start,
                    hol_path,
                    hol_name,
                    int(hol_line) if hol_line else None,
                    fields_for(QUALIFIER_RE),
                    fields_for(NAMES_AS_STRING_RE),
                    fields_for(NAMES_AS_STRING_BOUNDARY_RE),
                    fields_for(FMAP_AS_FINITE_SUPPORT_RE),
                    bool(FMAP_AS_FINITE_SUPPORT_RESULT_RE.search(attribute)),
                    relation_fields_for(),
                    bool(FMAP_AS_FINITE_SUPPORT_EQUALITIES_RE.search(attribute)),
                )
        start = None
        chunks = []
        attribute_bracket_depth = 0


def strip_lean_comments(text: str) -> str:
    """Remove nested Lean comments while preserving strings and line breaks."""
    result: list[str] = []
    index = 0
    depth = 0
    in_string = False
    escaped = False
    line_comment = False
    while index < len(text):
        if line_comment:
            if text[index] == "\n":
                line_comment = False
                result.append("\n")
            else:
                result.append(" ")
            index += 1
        elif depth:
            if text.startswith("/-", index):
                depth += 1
                result.extend((" ", " "))
                index += 2
            elif text.startswith("-/", index):
                depth -= 1
                result.extend((" ", " "))
                index += 2
            else:
                result.append("\n" if text[index] == "\n" else " ")
                index += 1
        elif in_string:
            char = text[index]
            result.append(char)
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
            index += 1
        elif text.startswith("/-", index):
            depth = 1
            result.extend((" ", " "))
            index += 2
        elif text.startswith("--", index):
            line_comment = True
            result.extend((" ", " "))
            index += 2
        else:
            char = text[index]
            result.append(char)
            if char == '"':
                in_string = True
            index += 1
    return "".join(result)


def structure_fields(lines: list[str]) -> set[str]:
    """Collect field names declared by structures in one Lean module."""
    fields: set[str] = set()
    structure_indent: int | None = None
    for line in strip_lean_comments("\n".join(lines)).splitlines():
        structure = re.match(r"^(\s*)structure\s+[A-Za-z0-9_'.]+.*\bwhere\s*$", line)
        if structure:
            structure_indent = len(structure.group(1))
            continue
        if structure_indent is None:
            continue
        if not line.strip():
            continue
        indent = len(line) - len(line.lstrip())
        if indent <= structure_indent:
            structure_indent = None
            continue
        field = re.match(r"^\s+([A-Za-z_][A-Za-z0-9_']*)\s*:", line)
        if field:
            fields.add(field.group(1))
    return fields


def structure_field_types(lines: list[str]) -> dict[str, dict[str, str]]:
    """Text of each structure field declaration's type, keyed by structure.

    The type is the remainder of the declaration line; qualified finite-map
    fields name their `HolFiniteMapExact` carrier on that line, which is enough
    for the representation gate to reject raw `α → Option β` maps.  Keeping the
    lookup owner-specific matters when a module declares several structures with
    the same field names (a broad state and its finite-support counterpart): the
    gate must read the type from the disambiguated owning carrier, not from the
    first structure that happens to declare the field.
    """
    field_types: dict[str, dict[str, str]] = {}
    structure_indent: int | None = None
    current: str | None = None
    for line in strip_lean_comments("\n".join(lines)).splitlines():
        structure = re.match(
            r"^(\s*)structure\s+([A-Za-z0-9_'.]+).*\bwhere\s*$", line
        )
        if structure:
            structure_indent = len(structure.group(1))
            current = structure.group(2)
            field_types.setdefault(current, {})
            continue
        if structure_indent is None:
            continue
        if not line.strip():
            continue
        indent = len(line) - len(line.lstrip())
        if indent <= structure_indent:
            structure_indent = None
            current = None
            continue
        field = re.match(r"^\s+([A-Za-z_][A-Za-z0-9_']*)\s*:\s*(?P<type>.+)$", line)
        if field and current is not None:
            field_types[current].setdefault(field.group(1), field.group("type").strip())
    return field_types


def structure_field_map(lines: list[str]) -> dict[str, set[str]]:
    """Field names of every structure declared in this module."""
    members: dict[str, set[str]] = {}
    structure_indent: int | None = None
    current: str | None = None
    for line in strip_lean_comments("\n".join(lines)).splitlines():
        structure = re.match(
            r"^(\s*)structure\s+([A-Za-z0-9_'.]+).*\bwhere\s*$", line
        )
        if structure:
            structure_indent = len(structure.group(1))
            current = structure.group(2)
            members.setdefault(current, set())
            continue
        if structure_indent is None:
            continue
        if not line.strip():
            continue
        indent = len(line) - len(line.lstrip())
        if indent <= structure_indent:
            structure_indent = None
            current = None
            continue
        field = re.match(r"^\s+([A-Za-z_][A-Za-z0-9_']*)\s*:", line)
        if field and current is not None:
            members[current].add(field.group(1))
    return members


@lru_cache(maxsize=None)
def imported_structure_field_types(
    module: str, root: str
) -> dict[str, list[tuple[str, set[str], dict[str, str]]]]:
    """Collect carrier structures reachable through this module's imports.

    Finite-map qualifiers may use a structure declared by an imported
    counterpart module. The tagged module still needs a local kernel-checked
    roundtrip witness, but the field names and carrier types are read from the
    actual imported declaration rather than inferred from a same-named local
    duplicate.
    """
    root_path = Path(root)
    current = root_path / module
    if not current.is_file():
        return {}
    pending = list(IMPORT_RE.findall(current.read_text(encoding="utf-8")))
    visited: set[str] = set()
    result: dict[str, list[tuple[str, set[str], dict[str, str]]]] = {}
    while pending:
        imported = pending.pop()
        if imported in visited:
            continue
        visited.add(imported)
        path = root_path / (imported.replace(".", "/") + ".lean")
        if not path.is_file():
            continue
        lines = path.read_text(encoding="utf-8").splitlines()
        members = structure_field_map(lines)
        types = structure_field_types(lines)
        for name, fields in members.items():
            result.setdefault(name, []).append(
                (imported, fields, types.get(name, {}))
            )
        pending.extend(IMPORT_RE.findall("\n".join(lines)))
    return result


def identifier_token_occurs(text: str, name: str) -> bool:
    """Whether `name` occurs in `text` as a complete Lean identifier token.

    A plain substring test would let one structure name match inside a longer
    name (for example `State` matching `FiniteState`), which could select the
    wrong owning carrier.  Boundary characters are the complement of Lean's
    identifier alphabet.
    """
    return (
        re.search(
            rf"(?<![A-Za-z0-9_']){re.escape(name)}(?![A-Za-z0-9_'])", text
        )
        is not None
    )


def owning_structure_for_fields(
    members: dict[str, set[str]], fields: Iterable[str],
    declaration_text: str = "",
) -> str | None:
    """The carrier structure declaring every qualified field.

    The qualifier stays narrow: all named fields must live in one carrier
    structure, so fields split across several structures are rejected.  When a
    module declares several structures with the same field names (for example a
    broad state and its finite-support counterpart), the tagged declaration's
    own carrier disambiguates: the owner must be named as a whole identifier
    token in the declaration text.
    """
    wanted = set(fields)
    candidates = [name for name, names in members.items() if wanted <= names]
    if len(candidates) == 1:
        return candidates[0]
    if declaration_text:
        named = [
            name
            for name in candidates
            if identifier_token_occurs(declaration_text, name)
        ]
        if len(named) == 1:
            return named[0]
    return None


TOP_DECL_RE = re.compile(
    r"^(?:@\[|def |theorem |lemma |abbrev |instance |structure |inductive )"
)


def tagged_declaration_text(lines: list[str], attribute_start: int) -> str:
    """Source text of the declaration carrying an attribute at `attribute_start`.

    Used to disambiguate the owning carrier structure when a module defines more
    than one structure with the same fields: the tagged declaration's signature
    names the carrier it is stated over.
    """
    region: list[str] = []
    seen_declaration = False
    for line in lines[attribute_start - 1:]:
        stripped = line.lstrip()
        if stripped.startswith("@["):
            if seen_declaration:
                break
            region.append(line)
            if re.search(r"(?:^|\s)(?:def|theorem|lemma|abbrev|instance|structure) ", stripped):
                seen_declaration = True
                if ":=" in stripped:
                    break
            continue
        if not line.strip():
            region.append(line)
            continue
        if seen_declaration and TOP_DECL_RE.match(line):
            break
        if re.match(r"(?:def|theorem|lemma|abbrev|instance|structure) ", stripped):
            seen_declaration = True
        region.append(line)
        if seen_declaration and ":=" in line:
            break
    return "\n".join(region)


TO_FUNCTION_RE = re.compile(r"\bto([A-Z][A-Za-z0-9_']*)")
OF_FUNCTION_RE = re.compile(r"\bof([A-Z][A-Za-z0-9_']*)")


def has_fmap_witness(
    lines: list[str],
    owning: str | None,
    counterpart_names: Iterable[str],
) -> bool:
    """Require the canonical finite-map translation witness in this module.

    The witness is named `holFmapAsFiniteSupportWitness`; its statement must
    name the unique structure that owns every qualified field and must express a
    genuine kernel-proved roundtrip between that carrier and a broad counterpart,
    i.e. it applies (or names) both a `toX` project and its `ofX`
    reconstruction for the same `X` and states an equality or equivalence.  A
    bare `State -> Broad -> State` arrow, or an unrelated counterpart mention,
    is NOT a canonical witness.  Lake checks the proof; this gate checks
    presence and shape without hard-coding any one carrier module.
    """
    if not owning:
        return False
    source = strip_lean_comments("\n".join(lines))
    pattern = re.compile(
        rf"^\s*(?:@\[[\s\S]*?\]\s*)?(?:private\s+|protected\s+)?"
        rf"(?:theorem|lemma)\s+holFmapAsFiniteSupportWitness\b"
        rf"(?P<statement>[\s\S]*?):=",
        re.M,
    )
    for match in pattern.finditer(source):
        statement = match.group("statement")
        if not identifier_token_occurs(statement, owning):
            continue
        if "=" not in statement and "\u2194" not in statement:
            continue
        projects = {m.group(1) for m in TO_FUNCTION_RE.finditer(statement)}
        reconstructions = {m.group(1) for m in OF_FUNCTION_RE.finditer(statement)}
        if projects & reconstructions:
            return True
    return False


def fmap_as_finite_support_errors(
    lines: list[str], fields: tuple[str, ...], module: str,
    declaration_text: str = "",
) -> list[str]:
    """Validate the reviewed canonical HOL finite-map translation.

    Each named field must be a same-module structure field whose declared type
    uses `HolFiniteMapExact`; a raw `α → Option β` lookup map is ineligible.
    All named fields must belong to ONE owning carrier structure (when several
    structures declare the same fields, the tagged declaration's carrier
    disambiguates as a whole identifier token), and the module must provide a
    canonical witness `holFmapAsFiniteSupportWitness` naming that structure and
    stating a real `toX`/`ofX` roundtrip with its broad counterpart (a bare arrow
    or unrelated counterpart mention is rejected).  The field-type check reads
    the type from the disambiguated owning carrier, so a same-named field on a
    different structure (for example a raw function-backed broad state) neither
    satisfies nor blocks the qualifier.
    """
    errors: list[str] = []
    if len(set(fields)) != len(fields):
        errors.append("fmap_as_finite_support fields must be distinct")
    local_types = structure_field_types(lines)
    members = structure_field_map(lines)
    imported = imported_structure_field_types(module, str(ROOT))
    owning: str | None = None
    owner_types: dict[str, str] = {}
    wanted = set(fields)
    if fields:
        # Resolve by the tagged declaration's carrier when possible. An
        # imported carrier must be named by that declaration; a same-named
        # local structure must not silently shadow it. If the tagged
        # declaration does not disambiguate, accept only one local candidate,
        # preserving the old same-module rule.
        local_candidates = [
            name for name, names in members.items() if wanted <= names
        ]
        imported_candidates = [
            (name, source, names, types)
            for name, declarations in imported.items()
            for source, names, types in declarations
            if wanted <= names
        ]
        if declaration_text:
            named_local = [
                name for name in local_candidates
                if identifier_token_occurs(declaration_text, name)
            ]
            named_imported = [
                item for item in imported_candidates
                if identifier_token_occurs(declaration_text, item[0])
            ]
            named = [(name, local_types.get(name, {})) for name in named_local]
            named.extend((name, types) for name, _source, _names, types in named_imported)
            if len(named) == 1:
                owning, owner_types = named[0]
        elif len(local_candidates) == 1:
            owning = local_candidates[0]
            owner_types = local_types.get(owning, {})
    for field in fields:
        if owning is None:
            errors.append(
                f"fmap_as_finite_support field `{field}` is not resolved to one "
                f"carrier structure in {module} or its imports"
            )
            continue
        field_type = owner_types.get(field, "")
        if "HolFiniteMapExact" not in field_type:
            errors.append(
                f"fmap_as_finite_support field `{field}` of owning structure "
                f"`{owning}` does not use the approved HolFiniteMapExact carrier; "
                "a raw function-backed map is ineligible"
            )
    if fields and owning is None:
        errors.append(
            "fmap_as_finite_support fields must all be declared by one owning "
            f"carrier structure in {module} (when several structures share the "
            "field names, the tagged declaration must name its carrier)"
        )
    elif fields and not has_fmap_witness(lines, owning, members.keys()):
        errors.append(
            "fmap_as_finite_support has no same-module checked canonical witness "
            "`holFmapAsFiniteSupportWitness` naming the owning structure and "
            "stating a real `toX`/`ofX` roundtrip with its broad counterpart"
        )
    return errors


def has_fmap_relation_witness(lines: list[str], carrier: str) -> bool:
    """Require a per-carrier canonical finite-map relation witness in this module.

    A multi-carrier relation names several carriers; each distinct carrier must
    provide a same-module kernel-checked witness
    `holFmapAsFiniteSupportRelationWitness_<carrier>` that names the carrier and
    states a genuine `toX`/`ofX` roundtrip with its broad counterpart.  A bare
    arrow or an unrelated counterpart mention is rejected.  The witness is
    carrier-specific so one declaration cannot reuse another carrier's evidence.
    """
    if not carrier:
        return False
    source = strip_lean_comments("\n".join(lines))
    pattern = re.compile(
        rf"^\s*(?:@\[[\s\S]*?\]\s*)?(?:private\s+|protected\s+)?"
        rf"(?:theorem|lemma)\s+"
        rf"holFmapAsFiniteSupportRelationWitness_{re.escape(carrier)}\b"
        rf"(?P<statement>[\s\S]*?):=",
        re.M,
    )
    for match in pattern.finditer(source):
        statement = match.group("statement")
        if not identifier_token_occurs(statement, carrier):
            continue
        if "=" not in statement and "\u2194" not in statement:
            continue
        projects = {m.group(1) for m in TO_FUNCTION_RE.finditer(statement)}
        reconstructions = {m.group(1) for m in OF_FUNCTION_RE.finditer(statement)}
        if projects & reconstructions:
            return True
    return False


def parameter_has_hol_finite_map_binder(declaration_text: str, name: str) -> bool:
    """Whether `name` is a binder of `declaration_text` with a HolFiniteMapExact type.

    A bare finite-map-parameter entry records that a HOL finite-map argument of
    the tagged declaration is represented by the canonical `HolFiniteMapExact`
    translation.  The parameter must be an explicit or implicit binder of the
    declaration whose declared type mentions `HolFiniteMapExact`; a raw
    function-backed `α → Option β` parameter is ineligible.
    """
    if not declaration_text or not name:
        return False
    pattern = re.compile(rf"[\(\{{]\s*{re.escape(name)}\s*:\s*([^)\}}]*)[\)\}}]")
    for match in pattern.finditer(declaration_text):
        if "HolFiniteMapExact" in match.group(1):
            return True
    return False


def fmap_as_finite_support_relation_errors(
    lines: list[str], entries: tuple[tuple[str, str], ...], module: str,
    declaration_text: str = "",
) -> list[str]:
    """Validate a multi-carrier finite-map relation qualifier.

    Each entry is either `Carrier.field` or a bare finite-map parameter name.
    A `Carrier.field` entry requires the carrier to be a structure declared in
    this module or reachable through its imports, the field to be one of that
    carrier's fields using the approved `HolFiniteMapExact` carrier, and the
    tagged declaration to visibly name every such carrier; every distinct
    carrier additionally needs its own same-module canonical witness
    `holFmapAsFiniteSupportRelationWitness_<carrier>` (see
    `has_fmap_relation_witness`).  A bare entry requires the tagged
    declaration to bind that name at a `HolFiniteMapExact` type: it records a
    standalone map parameter (no owning carrier), so no carrier witness is
    required.  This gate is deliberately separate from the single-owner
    `fmap_as_finite_support` gate and does not relax it.
    """
    errors: list[str] = []
    if len(set(entries)) != len(entries):
        errors.append("fmap_as_finite_support_relation entries must be distinct")
    local_types = structure_field_types(lines)
    imported = imported_structure_field_types(module, str(ROOT))
    own_types: dict[str, dict[str, str]] = {}
    field_entries = [(carrier, field) for carrier, field in entries if field]
    parameter_entries = [(carrier, field) for carrier, field in entries if not field]
    for name, _field in parameter_entries:
        if not name or "." in name:
            errors.append(
                f"fmap_as_finite_support_relation bare entry `{name}` must be a "
                "plain finite-map parameter name"
            )
        elif not parameter_has_hol_finite_map_binder(declaration_text, name):
            errors.append(
                f"fmap_as_finite_support_relation bare entry `{name}` must be a "
                "parameter of the tagged declaration whose declared type uses the "
                "approved HolFiniteMapExact carrier; a raw function-backed map is "
                "ineligible"
            )
    for carrier, field in field_entries:
        if carrier not in own_types:
            if carrier in local_types:
                own_types[carrier] = local_types[carrier]
            else:
                for name, declarations in imported.items():
                    if name != carrier:
                        continue
                    for _source, _names, types in declarations:
                        if field in types:
                            own_types[carrier] = types
                            break
                    break
        types = own_types.get(carrier)
        if types is None:
            errors.append(
                f"fmap_as_finite_support_relation carrier `{carrier}` is not a "
                f"structure declared in {module} or its imports"
            )
            continue
        if declaration_text and not identifier_token_occurs(declaration_text, carrier):
            errors.append(
                f"fmap_as_finite_support_relation carrier `{carrier}` is not "
                "named in the tagged declaration; the relation must be stated "
                "over the carrier it qualifies"
            )
        field_type = types.get(field, "")
        if not field_type:
            errors.append(
                f"fmap_as_finite_support_relation field `{field}` is not a field "
                f"of carrier `{carrier}`"
            )
        elif "HolFiniteMapExact" not in field_type:
            errors.append(
                f"fmap_as_finite_support_relation field `{carrier}.{field}` does "
                "not use the approved HolFiniteMapExact carrier; a raw "
                "function-backed map is ineligible"
            )
    for carrier in sorted({carrier for carrier, _ in field_entries if carrier}):
        if not has_fmap_relation_witness(lines, carrier):
            errors.append(
                "fmap_as_finite_support_relation has no same-module checked "
                f"canonical witness `holFmapAsFiniteSupportRelationWitness_{carrier}` "
                "naming the carrier and stating a real `toX`/`ofX` roundtrip with "
                "its broad counterpart"
            )
    return errors


def fmap_as_finite_support_result_witness_name(decl_name: str) -> str:
    """Canonical witness name for a standalone HolFiniteMapExact declaration."""
    return f"holFmapAsFiniteSupportResultWitness_{decl_name}"


def _last_top_level_colon(text: str) -> int:
    """Index of the last `:` outside any parentheses/brackets, or -1."""
    depth = 0
    last = -1
    for index, char in enumerate(text):
        if char in "([{":
            depth += 1
        elif char in ")]}":
            depth = max(0, depth - 1)
        elif char == ":" and depth == 0 and not text.startswith(":=", index):
            last = index
    return last


def _split_top_level(text: str, separators: tuple[str, ...]) -> tuple[str, str] | None:
    """Split at the first top-level separator, ignoring parentheses/brackets."""
    depth = 0
    index = 0
    while index < len(text):
        char = text[index]
        if char in "([{":
            depth += 1
        elif char in ")]}":
            depth = max(0, depth - 1)
        elif depth == 0:
            for separator in separators:
                if text.startswith(separator, index):
                    return text[:index], text[index + len(separator):]
        index += 1
    return None


def _split_top_level_all(text: str, separator: str) -> list[str]:
    """Split at every top-level occurrence of `separator`."""
    parts: list[str] = []
    depth = 0
    index = 0
    start = 0
    while index < len(text):
        char = text[index]
        if char in "([{":
            depth += 1
        elif char in ")]}":
            depth = max(0, depth - 1)
        elif depth == 0 and text.startswith(separator, index):
            parts.append(text[start:index])
            index += len(separator)
            start = index
            continue
        index += 1
    parts.append(text[start:])
    return parts


def _normalize_whitespace(text: str) -> str:
    return "".join(text.split())


def _strip_outer_parens(text: str) -> str:
    """Remove balanced parentheses that enclose the whole expression."""
    text = text.strip()
    while len(text) >= 2 and text[0] == "(" and text[-1] == ")":
        depth = 0
        balanced = True
        for index, char in enumerate(text):
            if char == "(":
                depth += 1
            elif char == ")":
                depth -= 1
                if depth == 0 and index != len(text) - 1:
                    balanced = False
                    break
        if not balanced:
            break
        text = text[1:-1].strip()
    return text


def _lookup_key(side: str) -> str | None:
    """Whitespace-normalized argument of the last lookup application in `side`."""
    matches = list(re.finditer(r"(?i)\b(?:lookup|flookup)\b", side))
    if not matches:
        return None
    tail = side[matches[-1].end():]
    return _normalize_whitespace(tail.strip().rstrip(")").strip())


def has_fmap_result_witness(
    lines: list[str], decl_name: str, module: str
) -> tuple[bool, str]:
    """Require the canonical standalone finite-map translation witness.

    The witness is `holFmapAsFiniteSupportResultWitness_<decl>`; its final
    equality/iff conclusion must mention the tagged declaration on exactly one
    side with a lookup operation on that side, and must not be a self-equality
    or a relation already assumed by a premise. A missing, vacuous,
    wrongly-named, unrelated, or type-name-only witness is rejected.
    Lake checks the proof; this gate checks presence and shape.
    """
    if decl_name in ("?", ""):
        return (False, "could not identify the tagged declaration name")
    source = strip_lean_comments("\n".join(lines))
    witness = fmap_as_finite_support_result_witness_name(decl_name)
    pattern = re.compile(
        rf"^\s*(?:@\[[\s\S]*?\]\s*)?(?:private\s+|protected\s+)?"
        rf"(?:theorem|lemma)\s+{re.escape(witness)}\b(?P<statement>[\s\S]*?):=",
        re.M,
    )
    matches = list(pattern.finditer(source))
    if not matches:
        return (
            False,
            f"in {module} has no same-module checked witness `{witness}` "
            f"for the tagged declaration `{decl_name}`",
        )
    for match in matches:
        statement = match.group("statement")
        if not identifier_token_occurs(statement, decl_name):
            return (
                False,
                f"witness `{witness}` does not mention the tagged declaration "
                f"`{decl_name}`",
            )
        if not re.search(r"(?i)\b(?:lookup|flookup)\b", statement):
            return (
                False,
                f"witness `{witness}` does not state a lookup-level "
                "correspondence to the HOL finite map",
            )
        colon = _last_top_level_colon(statement)
        conclusion = statement[colon + 1:] if colon >= 0 else statement
        segments: list[str] = []
        rest = conclusion
        while True:
            split = _split_top_level(rest, ("\u2192", "->"))
            if split is None:
                segments.append(rest)
                break
            segments.append(split[0])
            rest = split[1]
        premises, final = segments[:-1], segments[-1]
        relation = _split_top_level(final, ("\u2194",)) or _split_top_level(final, ("=",))
        if relation is None:
            return (
                False,
                f"witness `{witness}` is vacuous: no equality/iff conclusion",
            )
        lhs, rhs = relation
        if "".join(lhs.split()) == "".join(rhs.split()):
            return (
                False,
                f"witness `{witness}` is a self-equality; it does not "
                "establish lookup-level correspondence",
            )
        in_lhs = identifier_token_occurs(lhs, decl_name)
        in_rhs = identifier_token_occurs(rhs, decl_name)
        if not (in_lhs or in_rhs):
            return (
                False,
                f"witness `{witness}` conclusion does not mention the tagged "
                f"declaration `{decl_name}`",
            )
        if in_lhs == in_rhs:
            return (
                False,
                f"witness `{witness}` must mention the tagged declaration on "
                "exactly one side of its equality/iff",
            )
        target_side = lhs if in_lhs else rhs
        if not re.search(r"(?i)\b(?:lookup|flookup)\b", target_side):
            return (
                False,
                f"witness `{witness}` does not apply a lookup to the tagged "
                "declaration's side of the conclusion",
            )
        if not re.match(
            rf"^[\s(]*{re.escape(decl_name)}\b", target_side.strip()
        ):
            return (
                False,
                f"witness `{witness}` does not apply the lookup directly to the "
                f"tagged declaration `{decl_name}`; an ignored-proof "
                "(threaded-argument) witness is rejected",
            )
        binder_zone = statement[:colon] if colon >= 0 else ""
        for premise in ([binder_zone] if binder_zone else []) + premises:
            if (
                identifier_token_occurs(premise, decl_name)
                and re.search(r"(?i)\b(?:lookup|flookup)\b", premise)
                and ("=" in premise or "\u2194" in premise)
            ):
                return (
                    False,
                    f"witness `{witness}` assumes the target relation in a "
                    "premise instead of proving it",
                )
    return (True, "")


def fmap_as_finite_support_result_errors(
    lines: list[str], module: str,
    declaration_text: str, decl_name: str,
) -> list[str]:
    """Validate a standalone declaration whose own carrier is HolFiniteMapExact.

    Unlike `fmap_as_finite_support`, which names fields of an owning structure,
    this qualifier applies to a definition or theorem that returns (or consumes)
    a `HolFiniteMapExact` directly. The tagged declaration must mention the
    approved carrier (a raw `α → Option β` map is ineligible) and the module
    must provide the canonical lookup-level witness.
    """
    errors: list[str] = []
    if "HolFiniteMapExact" not in declaration_text:
        errors.append(
            "fmap_as_finite_support_result requires the tagged declaration's own "
            "input/result carrier to use the approved HolFiniteMapExact "
            "translation; a raw `\u03b1 \u2192 Option \u03b2` function map is ineligible"
        )
    ok, message = has_fmap_result_witness(lines, decl_name, module)
    if not ok:
        errors.append(f"fmap_as_finite_support_result {message}")
    return errors


def fmap_as_finite_support_equalities_witness_name(decl_name: str, index: int) -> str:
    return f"holFmapAsFiniteSupportEqualityWitness_{decl_name}_{index}"


def _count_top_level_conjuncts(text: str) -> int:
    count = 1
    depth = 0
    index = 0
    while index < len(text):
        char = text[index]
        if char in "([{":
            depth += 1
        elif char in ")]}":
            depth = max(0, depth - 1)
        elif depth == 0 and text.startswith("\u2227", index):
            count += 1
            index += 1
        index += 1
    return count


def _statement_conclusion(text: str) -> str:
    """Statement conclusion of a declaration text, with body and premises removed."""
    body = text.split(":=", 1)[0]
    colon = _last_top_level_colon(body)
    conclusion = body[colon + 1:] if colon >= 0 else body
    rest = conclusion
    while True:
        split = _split_top_level(rest, ("\u2192", "->"))
        if split is None:
            return rest
        rest = split[1]


def _has_lookup_equality_witness(
    lines: list[str], witness: str, forbidden: str,
    expected: tuple[str, str] | None = None,
) -> tuple[bool, str]:
    source = strip_lean_comments("\n".join(lines))
    pattern = re.compile(
        rf"^\s*(?:@\[[\s\S]*?\]\s*)?(?:private\s+|protected\s+)?"
        rf"(?:theorem|lemma)\s+{re.escape(witness)}\b(?P<statement>[\s\S]*?):=",
        re.M,
    )
    matches = list(pattern.finditer(source))
    if not matches:
        return (False, f"has no same-module checked witness `{witness}`")
    for match in matches:
        statement = match.group("statement")
        if forbidden and identifier_token_occurs(statement, forbidden):
            return (
                False,
                f"witness `{witness}` mentions the tagged theorem `{forbidden}`; "
                "an ignored-proof (threaded-argument) witness is rejected",
            )
        colon = _last_top_level_colon(statement)
        conclusion = statement[colon + 1:] if colon >= 0 else statement
        segments: list[str] = []
        rest = conclusion
        while True:
            split = _split_top_level(rest, ("\u2192", "->"))
            if split is None:
                segments.append(rest)
                break
            segments.append(split[0])
            rest = split[1]
        premises, final = segments[:-1], segments[-1]
        binder_zone = statement[:colon] if colon >= 0 else ""
        if re.search(r"(?i)\b(?:lookup|flookup)\b", binder_zone) and (
            "=" in binder_zone or "\u2194" in binder_zone
        ):
            return (
                False,
                f"witness `{witness}` assumes the target relation in a premise "
                "instead of proving it",
            )
        if _split_top_level(final, ("\u2194",)) is not None:
            return (
                False,
                f"witness `{witness}` must state an equality, not an iff",
            )
        relation = _split_top_level(final, ("=",))
        if relation is None:
            return (
                False,
                f"witness `{witness}` is vacuous: no equality conclusion",
            )
        lhs, rhs = relation
        if "".join(lhs.split()) == "".join(rhs.split()):
            return (
                False,
                f"witness `{witness}` is a self-equality; it does not "
                "establish lookup-level correspondence",
            )
        if not (
            re.search(r"(?i)\b(?:lookup|flookup)\b", lhs)
            and re.search(r"(?i)\b(?:lookup|flookup)\b", rhs)
        ):
            return (
                False,
                f"witness `{witness}` must apply a lookup on BOTH sides of its "
                "equality",
            )
        left_key = _lookup_key(lhs)
        right_key = _lookup_key(rhs)
        if left_key is None or right_key is None or left_key != right_key:
            return (
                False,
                f"witness `{witness}` must apply both lookups at the SAME key",
            )
        if expected is not None:
            expected_lhs = _normalize_whitespace(expected[0])
            expected_rhs = _normalize_whitespace(expected[1])
            lhs_norm = _normalize_whitespace(lhs)
            rhs_norm = _normalize_whitespace(rhs)
            forward = expected_lhs in lhs_norm and expected_rhs in rhs_norm
            backward = expected_lhs in rhs_norm and expected_rhs in lhs_norm
            if not (forward or backward):
                return (
                    False,
                    f"witness `{witness}` is not associated with its numbered "
                    "finite-map equality conjunct",
                )
        for premise in premises:
            if re.search(r"(?i)\b(?:lookup|flookup)\b", premise) and (
                "=" in premise or "\u2194" in premise
            ):
                return (
                    False,
                    f"witness `{witness}` assumes the target relation in a "
                    "premise instead of proving it",
                )
    return (True, "")


def fmap_as_finite_support_equalities_errors(
    lines: list[str], module: str,
    declaration_text: str, decl_name: str,
) -> list[str]:
    """Validate a theorem whose conclusion is a conjunction of finite-map equalities.

    HOL theorems such as `slc_tlc_rw` conclude several `|->` map equalities.
    Each conjunct must be witnessed at the lookup level by a same-module checked
    `holFmapAsFiniteSupportEqualityWitness_<decl>_<index>`; the witnesses must not
    mention the tagged theorem, so the ignored-proof/threaded-argument pattern is
    rejected. The tagged declaration's own statement must use the approved
    `HolFiniteMapExact` translation.

    This is a conjunction-specific qualifier, so at least two top-level equality
    conjuncts are required. The checks are syntactic: the checker enforces witness
    count, naming, lookup shape, same-key application, and per-conjunct textual
    association, but it does NOT prove that the Lean witnesses and conjuncts
    correspond to the HOL map equalities. Source review must compare each numbered
    witness against the HOL equality and record that comparison in the reviewer
    note.
    """
    errors: list[str] = []
    if "HolFiniteMapExact" not in declaration_text:
        errors.append(
            "fmap_as_finite_support_equalities requires the tagged declaration's "
            "conclusion to use the approved HolFiniteMapExact translation; a raw "
            "`\u03b1 \u2192 Option \u03b2` function map is ineligible"
        )
    conclusion = _statement_conclusion(declaration_text)
    count = _count_top_level_conjuncts(conclusion)
    if count < 2:
        errors.append(
            "fmap_as_finite_support_equalities requires at least two finite-map "
            "equality conjuncts in the tagged declaration's conclusion"
        )
        return errors
    conjuncts = _split_top_level_all(conclusion, "\u2227")
    for index in range(1, count + 1):
        witness = fmap_as_finite_support_equalities_witness_name(decl_name, index)
        conjunct = conjuncts[index - 1] if index - 1 < len(conjuncts) else ""
        expected = _split_top_level(_strip_outer_parens(conjunct), ("=",))
        if expected is None:
            errors.append(
                f"fmap_as_finite_support_equalities conjunct {index} is not a "
                "map equality"
            )
            continue
        ok, message = _has_lookup_equality_witness(
            lines, witness, decl_name, expected,
        )
        if not ok:
            errors.append(
                f"fmap_as_finite_support_equalities conjunct {index} {message}"
            )
    return errors


def has_list_array_witness(lines: list[str], field: str) -> bool:
    """Require a same-module, kernel-checked representation theorem for a field.

    The witness convention is `holListArrayWitness_<field>` and its theorem
    type must mention both `RepresentsHOLNodeList` and the qualified state field.
    The relation must occur in the result type, exactly once, and not in any
    premise: a theorem assuming the relation it claims to establish is not a
    representation witness. Lake checks the witness proof when it builds the
    tagged module; this syntactic gate does not itself prove semantic
    correspondence.
    """
    source = strip_lean_comments("\n".join(lines))
    pattern = re.compile(
        rf"^\s*(?:@[\s\S]*?\]\s*)?(?:private\s+|protected\s+)?"
        rf"(?:theorem|lemma)\s+holListArrayWitness_{re.escape(field)}\b"
        rf"(?P<type>[\s\S]*?):=",
        re.M,
    )
    for match in pattern.finditer(source):
        statement = match.group("type")
        depth = 0
        result_start: int | None = None
        for index, char in enumerate(statement):
            if char in "([{":
                depth += 1
            elif char in ")]}":
                depth -= 1
            elif char == ":" and depth == 0:
                result_start = index + 1
        if result_start is None:
            continue
        premises, result_type = statement[:result_start], statement[result_start:]
        if (
            "RepresentsHOLNodeList" not in premises
            and result_type.count("RepresentsHOLNodeList") == 1
            and re.search(rf"\.\s*{re.escape(field)}\b", result_type)
        ):
            return True
    return False


def list_as_array_errors(lines: list[str], fields: tuple[str, ...], module: str) -> list[str]:
    """Validate qualified fields against local state declarations and witnesses."""
    errors: list[str] = []
    declared_fields = structure_fields(lines)
    for field in fields:
        if field not in declared_fields:
            errors.append(
                f"list_as_array field `{field}` is not a field of a Lean structure "
                f"declared in {module}"
            )
        if not has_list_array_witness(lines, field):
            errors.append(
                f"list_as_array field `{field}` has no same-module checked witness "
                f"`holListArrayWitness_{field}`"
            )
    return errors


def has_mlstring_witness(lines: list[str], declaration: str) -> bool:
    """Require a same-module byte-range theorem for a byte-observable tag.

    The theorem is named for the tagged declaration and its result must
    establish `NameRanged`. Input range premises are allowed. This syntax check
    does not establish that the result is the right output or that a premise is
    discharged on the executed path; Lean checks the proof and source review
    records those obligations.
    """
    source = strip_lean_comments("\n".join(lines))
    pattern = re.compile(
        rf"^\s*(?:@\[[\s\S]*?\]\s*)?(?:private\s+|protected\s+)?"
        rf"(?:theorem|lemma)\s+holMlStringWitness_{re.escape(declaration)}\b"
        rf"(?P<type>[\s\S]*?):=",
        re.M,
    )
    for match in pattern.finditer(source):
        statement = match.group("type")
        depth = 0
        result_start: int | None = None
        for index, char in enumerate(statement):
            if char in "([{":
                depth += 1
            elif char in ")]}":
                depth -= 1
            elif char == ":" and depth == 0:
                result_start = index + 1
        if result_start is None:
            continue
        result_type = statement[result_start:]
        result = result_type.strip()
        if re.match(r"^(?:[A-Za-z0-9_]+\.)*NameRanged\b", result):
            return True
    return False


def names_as_string_errors(
    lines: list[str],
    identifiers: tuple[str, ...],
    boundary_identifiers: tuple[str, ...],
    module: str,
    declaration: str,
) -> list[str]:
    """Validate reviewed HOL `mlstring` identifiers and byte boundaries."""
    errors: list[str] = []
    if len(set(identifiers)) != len(identifiers):
        errors.append("names_as_string identifiers must be distinct")
    if len(set(boundary_identifiers)) != len(boundary_identifiers):
        errors.append("names_as_string_boundary identifiers must be distinct")
    for identifier in boundary_identifiers:
        if identifier not in identifiers:
            errors.append(
                f"names_as_string_boundary identifier `{identifier}` is not listed by "
                "names_as_string"
            )
        if not has_mlstring_witness(lines, declaration):
            errors.append(
                f"names_as_string_boundary identifier `{identifier}` in {module}:{declaration} "
                f"has no same-module checked witness `holMlStringWitness_{declaration}` "
                "with a NameRanged result"
            )
    return errors


def hol_declaration_lines(
    path: Path, cache: dict[Path, dict[str, list[int]]]
) -> dict[str, list[int]]:
    if path not in cache:
        names: dict[str, list[int]] = {}
        header = re.compile(
            r"^(?:%s)\s+([A-Za-z0-9_']+)" % "|".join(HOL_HEADER_KEYWORDS)
        )
        sml_val = re.compile(r"^val\s+([A-Za-z0-9_']+)\s*=")
        # HOL ``Datatype:`` blocks put the declared type name on the next
        # line(s) (``name = ...``) and terminate with a top-level ``End``.
        datatype_header = re.compile(r"^Datatype\s*:?\s*$")
        datatype_name = re.compile(r"^\s*([A-Za-z0-9_']+)\s*=")
        datatype_end = re.compile(r"^End\b")
        in_datatype = False
        with path.open(encoding="utf-8", errors="replace") as handle:
            for number, line in enumerate(handle, start=1):
                if in_datatype:
                    if datatype_end.match(line):
                        in_datatype = False
                    else:
                        match = datatype_name.match(line)
                        if match:
                            names.setdefault(match.group(1), []).append(number)
                    continue
                if datatype_header.match(line):
                    in_datatype = True
                    continue
                match = header.match(line) or sml_val.match(line)
                if match:
                    names.setdefault(match.group(1), []).append(number)
        cache[path] = names
    return cache[path]


def hol_ref_error(
    path: Path, name: str, line: int | None,
    cache: dict[Path, dict[str, list[int]]]
) -> str | None:
    declared = hol_declaration_lines(path, cache).get(name, [])
    if not declared:
        return f"declares no `{name}`"
    if line is None and len(declared) > 1:
        return (
            f"declares `{name}` at multiple lines {declared}; "
            "add the source line to @[hol]"
        )
    if line is not None and line not in declared:
        return f"declares `{name}` at {declared}, not at line {line}"
    return None


def main(argv: list[str]) -> int:
    want_mapping = "--mapping" in argv
    want_orphans = "--orphans" in argv
    errors: list[str] = []
    mapping: list[tuple[str, str, str, str]] = []
    cache: dict[Path, dict[str, list[int]]] = {}
    reachable = reachable_modules()

    if not (ROOT / "cakeml" / "pancake").is_dir():
        print(
            "error: the cakeml submodule is not checked out; run "
            "`git submodule update --init --depth 1 -- cakeml`",
            file=sys.stderr,
        )
        return 1

    for lean_path in lean_files():
        rel = lean_path.relative_to(ROOT).as_posix()
        lines = lean_path.read_text(encoding="utf-8").splitlines()
        module = module_name(lean_path)
        module_reported = False
        for (number, hol_path, hol_name, hol_line, list_fields,
             names_fields, boundary_fields, fmap_fields, fmap_result,
             fmap_relation, fmap_equalities) in hol_attribute_sites(lines):
            where = f"{rel}:{number}"
            lean_decl = find_lean_decl(lines, number - 1)
            if module not in reachable and not module_reported:
                module_reported = True
                errors.append(
                    f"{rel}: module {module} carries @[hol] but is not imported "
                    f"(transitively) from Flapjack.lean, so `lake build Flapjack` "
                    f"never checks it; add the import to Flapjack.lean"
                )
            if list_fields:
                errors.extend(
                    f"{where}: {error}"
                    for error in list_as_array_errors(lines, list_fields, rel)
                )
            if fmap_fields:
                errors.extend(
                    f"{where}: {error}"
                    for error in fmap_as_finite_support_errors(
                        lines, fmap_fields, rel, tagged_declaration_text(lines, number)
                    )
                )
            if fmap_result:
                errors.extend(
                    f"{where}: {error}"
                    for error in fmap_as_finite_support_result_errors(
                        lines, rel, tagged_declaration_text(lines, number), lean_decl
                    )
                )
            if fmap_relation:
                errors.extend(
                    f"{where}: {error}"
                    for error in fmap_as_finite_support_relation_errors(
                        lines, fmap_relation, rel, tagged_declaration_text(lines, number)
                    )
                )
            if fmap_equalities:
                errors.extend(
                    f"{where}: {error}"
                    for error in fmap_as_finite_support_equalities_errors(
                        lines, rel, tagged_declaration_text(lines, number), lean_decl
                    )
                )
            if names_fields or boundary_fields:
                errors.extend(
                    f"{where}: {error}"
                    for error in names_as_string_errors(
                        lines, names_fields, boundary_fields, rel, lean_decl
                    )
                )
            target = ROOT / hol_path
            if not hol_path.startswith("cakeml/") or not hol_path.endswith(".sml"):
                errors.append(f"{where}: path is not a cakeml/...sml file: {hol_path}")
                continue
            if not target.is_file():
                errors.append(f"{where}: HOL file does not exist: {hol_path}")
                continue
            ref_error = hol_ref_error(target, hol_name, hol_line, cache)
            if ref_error is not None:
                errors.append(
                    f"{where}: {hol_path} {ref_error} "
                    f"(cited by {lean_decl})"
                )
                continue
            mapped_name = f"{hol_name}:{hol_line}" if hol_line is not None else hol_name
            mapping.append((where, lean_decl, hol_path, mapped_name))

    if want_mapping:
        for row in mapping:
            print("\t".join(row))

    if want_orphans:
        orphans = sorted(
            module_name(path)
            for path in lean_files()
            if path.is_relative_to(ROOT / "Flapjack")
            and not path.is_relative_to(ROOT / "Flapjack" / "Test")
            and module_name(path) not in reachable
        )
        for module in orphans:
            print(f"warning: {module} is not reachable from Flapjack.lean", file=sys.stderr)

    if errors:
        for error in errors:
            print(f"error: {error}", file=sys.stderr)
        print(f"{len(errors)} bad @[hol] reference(s)", file=sys.stderr)
        return 1
    print(f"{len(mapping)} @[hol] reference(s) checked", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
