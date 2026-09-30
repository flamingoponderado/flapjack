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
from stat import S_ISREG
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
FMAP_AS_FINITE_SUPPORT_FUNCTION_RE = re.compile(
    r'\(\s*fmap_as_finite_support_function\s*:=\s*\[([^]]*)\]\s*\)'
)
FMAP_AS_FINITE_SUPPORT_RESULT_RE = re.compile(
    r'\(\s*fmap_as_finite_support_result\s*\)'
)
FMAP_AS_FINITE_SUPPORT_PARAMS_RE = re.compile(
    r'\(\s*fmap_as_finite_support_parameters\s*:=\s*\[([^]]*)\]\s*\)'
)
FMAP_AS_FINITE_SUPPORT_EXISTENTIALS_RE = re.compile(
    r'\(\s*fmap_as_finite_support_existentials\s*:=\s*\[([^]]*)\]\s*\)'
)
FMAP_AS_FINITE_SUPPORT_RELATION_RE = re.compile(
    r'\(\s*fmap_as_finite_support_relation\s*:=\s*\[([^]]*)\]\s*\)'
)
FMAP_AS_FINITE_SUPPORT_EQUALITIES_RE = re.compile(
    r'\(\s*fmap_as_finite_support_equalities\s*\)'
)
WORDS_AS_TYPE_INDEXED_BITVEC_RE = re.compile(
    r'\(\s*words_as_type_indexed_bitvec\s*\)'
)
WORD_DIMENSION_AS_WIDTH_RE = re.compile(
    r'\(\s*word_dimension_as_width\s*:=\s*([A-Za-z_][A-Za-z0-9_\']*)\s*\)'
)
WORD_POSITIVITY_EXTRA_RE = re.compile(
    r"(?:width\s*(?:≠|!=|>|≥)\s*(?:0|1)\b|0\s*<\s*width\b|1\s*≤\s*width\b"
    r"|Nat\.pos\b|NeZero\.out\b)"
)
FFI_UNIVERSE_LEVEL_RE = re.compile(r":\s*Type\s+[A-Za-z_][A-Za-z0-9_']*\b")
FFI_SORT_RE = re.compile(r":\s*Sort\b")
HOL_FFI_CARRIER_RE = re.compile(r"\bHolFfiState\b")
# Reviewed word abbreviations that denote a fixed-width `BitVec width` at the
# same width identifier (for example `RiscV.Word width`).  A carrier field typed
# through one of these is the standard translation of HOL `'a word` just like a
# literal `BitVec width` field.
WORD_CARRIER_ABBREV_NAMES = ("RiscV.Word",)


def field_mentions_word_carrier(type_text: str, width_name: str) -> bool:
    """Whether a field type denotes a word carrier at `width_name`.

    Accepts a literal `BitVec width_name` or a reviewed word abbreviation such
    as `RiscV.Word width_name`; both translate HOL's type-indexed `'a word`.
    """
    if re.search(r"\bBitVec\s+" + re.escape(width_name) + r"\b", type_text):
        return True
    for abbrev in WORD_CARRIER_ABBREV_NAMES:
        if re.search(
            re.escape(abbrev) + r"\s+" + re.escape(width_name) + r"\b", type_text
        ):
            return True
    return False


_WORD_CARRIER_ALTERNATION = "|".join(
    re.escape(name) for name in WORD_CARRIER_ABBREV_NAMES
)
# A word carrier token (`BitVec` or a reviewed abbreviation such as
# `RiscV.Word`).
WORD_CARRIER_TOKEN_RE = re.compile(
    r"\b(?:BitVec|" + _WORD_CARRIER_ALTERNATION + r")\b"
)
# A word carrier applied to an identifier dimension, e.g. `BitVec width`.
WORD_DIMENSION_ID_RE = re.compile(
    r"\b(?:BitVec|" + _WORD_CARRIER_ALTERNATION + r")\s+([A-Za-z_][A-Za-z0-9_']*)"
)
# A word carrier applied to a literal dimension, e.g. `BitVec 0`.
WORD_DIMENSION_LITERAL_RE = re.compile(
    r"\b(?:BitVec|" + _WORD_CARRIER_ALTERNATION + r")\s+([0-9]+)"
)
NAT_WIDTH_BINDER_RE = re.compile(
    r"[\{\(]\s*([A-Za-z_][A-Za-z0-9_']*)\s*:\s*Nat\s*[\}\)]"
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


class _LeanFileInfo:
    """One read of a Lean source file plus its lazily memoized parses.

    The transitive-import walkers below visit the same imported files once per
    tagged module; re-reading and re-parsing them each time dominated the run
    time.  Results are keyed by path, size, and mtime (see `_lean_file_info`),
    so a file rewritten between calls (as the checker tests do) is re-read.
    """

    def __init__(self, text: str) -> None:
        self.text = text
        self.lines = text.splitlines()
        self.imports = IMPORT_RE.findall(text)
        self._memo: dict[str, object] = {}

    def parsed(self, key: str, parse):
        if key not in self._memo:
            self._memo[key] = parse(self)
        return self._memo[key]


_LEAN_FILE_INFO: dict[tuple[str, int, int], _LeanFileInfo] = {}


def _lean_file_info(path: Path) -> _LeanFileInfo | None:
    """The memoized contents of `path`, or None when it is not a regular file."""
    try:
        stat = path.stat()
    except OSError:
        return None
    if not S_ISREG(stat.st_mode):
        return None
    key = (str(path), stat.st_size, stat.st_mtime_ns)
    info = _LEAN_FILE_INFO.get(key)
    if info is None:
        info = _LeanFileInfo(path.read_text(encoding="utf-8"))
        _LEAN_FILE_INFO[key] = info
    return info


def module_name(path: Path) -> str:
    rel = path.relative_to(ROOT).with_suffix("")
    return ".".join(rel.parts)


def module_path(module: str) -> Path:
    return ROOT / (module.replace(".", "/") + ".lean")


def module_source_file(module: str, root: str | Path) -> Path:
    """Resolve a dotted module name or repo-relative Lean path under a root."""
    module_path = Path(module)
    if module_path.suffix == ".lean" or "/" in module:
        return Path(root) / module_path
    return Path(root) / (module.replace(".", "/") + ".lean")


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


def hol_attribute_sites(lines: list[str], *, include_fmap_existentials: bool = False,
                        include_word_dimension_width: bool = False,
                        include_fmap_function: bool = False):
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

                site = (
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
                    bool(WORDS_AS_TYPE_INDEXED_BITVEC_RE.search(attribute)),
                    fields_for(FMAP_AS_FINITE_SUPPORT_PARAMS_RE),
                )
                if include_fmap_existentials:
                    site += (fields_for(FMAP_AS_FINITE_SUPPORT_EXISTENTIALS_RE),)
                if include_word_dimension_width:
                    width = WORD_DIMENSION_AS_WIDTH_RE.search(attribute)
                    site += (width.group(1) if width else None,)
                if include_fmap_function:
                    site += (fields_for(FMAP_AS_FINITE_SUPPORT_FUNCTION_RE),)
                yield site
        start = None
        chunks = []
        attribute_bracket_depth = 0


_COMMENT_START_RE = re.compile(r'/-|--|"')
_BLOCK_COMMENT_TOKEN_RE = re.compile(r"/-|-/")
_STRING_TOKEN_RE = re.compile(r'\\.|"', re.S)
_NOT_NEWLINE_RE = re.compile(r"[^\n]")


def strip_lean_comments(text: str) -> str:
    """Remove nested Lean comments while preserving strings and line breaks.

    Comment characters become spaces (line breaks are kept) so offsets and
    line numbers are unchanged.  Scanning jumps between the next significant
    token with precompiled regexes instead of stepping one character at a
    time; tokens are matched leftmost-first, as a character-by-character scan
    would.
    """
    result: list[str] = []
    pos = 0
    length = len(text)
    while pos < length:
        match = _COMMENT_START_RE.search(text, pos)
        if match is None:
            result.append(text[pos:])
            break
        start = match.start()
        result.append(text[pos:start])
        token = match.group()
        if token == '"':
            cursor = match.end()
            while True:
                inner = _STRING_TOKEN_RE.search(text, cursor)
                if inner is None:
                    end = length
                    break
                cursor = inner.end()
                if inner.group() == '"':
                    end = cursor
                    break
            result.append(text[start:end])
            pos = end
        elif token == "--":
            newline = text.find("\n", start)
            end = length if newline < 0 else newline
            result.append(" " * (end - start))
            pos = end
        else:
            depth = 1
            cursor = match.end()
            while depth:
                inner = _BLOCK_COMMENT_TOKEN_RE.search(text, cursor)
                if inner is None:
                    cursor = length
                    break
                depth += 1 if inner.group() == "/-" else -1
                cursor = inner.end()
            result.append(_NOT_NEWLINE_RE.sub(" ", text[start:cursor]))
            pos = cursor
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


def structure_headers(lines: list[str]) -> dict[str, str]:
    """Binders declared before `where` for every structure in this module.

    The `words_as_type_indexed_bitvec` qualifier resolves a width-indexed
    carrier by its declaration, so the positivity discharge (`[NeZero width]`)
    is read from the carrier's own header rather than assumed from its name.
    """
    headers: dict[str, str] = {}
    for line in strip_lean_comments("\n".join(lines)).splitlines():
        match = re.match(
            r"^\s*structure\s+([A-Za-z0-9_'.]+)(?P<header>.*?)\bwhere\s*$", line
        )
        if match:
            headers.setdefault(match.group(1), match.group("header"))
    return headers


def inductive_constructor_types(lines: list[str]) -> dict[str, dict[str, str]]:
    """Constructor payload text for indexed inductive word carriers."""
    owners: dict[str, dict[str, str]] = {}
    current: str | None = None
    owner_indent: int | None = None
    constructor_indent: int | None = None
    constructor_name: str | None = None
    constructor_lines: list[str] = []

    def flush() -> None:
        if current is not None and constructor_name is not None:
            owners[current][f"constructor:{constructor_name}"] = " ".join(
                constructor_lines
            ).strip()

    for line in strip_lean_comments("\n".join(lines)).splitlines():
        declaration = re.match(
            r"^(\s*)inductive\s+([A-Za-z0-9_'.]+).*\bwhere\s*$", line
        )
        if declaration:
            flush()
            current = declaration.group(2)
            owner_indent = len(declaration.group(1))
            constructor_indent = None
            constructor_name = None
            constructor_lines = []
            owners.setdefault(current, {})
            continue
        if current is None or owner_indent is None or not line.strip():
            continue
        indent = len(line) - len(line.lstrip())
        if indent <= owner_indent:
            flush()
            current = None
            owner_indent = None
            constructor_indent = None
            constructor_name = None
            constructor_lines = []
            continue
        constructor = re.match(r"^\s*\|\s*([A-Za-z_][A-Za-z0-9_']*)", line)
        if constructor:
            flush()
            constructor_indent = indent
            constructor_name = constructor.group(1)
            constructor_lines = [line.strip()]
        elif constructor_name is not None and constructor_indent is not None:
            if indent > constructor_indent:
                constructor_lines.append(line.strip())
            else:
                flush()
                constructor_indent = None
                constructor_name = None
                constructor_lines = []
    flush()
    return owners


def inductive_headers(lines: list[str]) -> dict[str, str]:
    """Binders before `where` for width-indexed inductive carriers."""
    headers: dict[str, str] = {}
    for line in strip_lean_comments("\n".join(lines)).splitlines():
        match = re.match(
            r"^\s*inductive\s+([A-Za-z0-9_'.]+)(?P<header>.*?)\bwhere\s*$",
            line,
        )
        if match:
            headers.setdefault(match.group(1), match.group("header"))
    return headers


@lru_cache(maxsize=None)
def imported_inductive_owners(
    module: str, root: str
) -> dict[str, list[tuple[str, str, dict[str, str]]]]:
    """Imported width-indexed inductives, with payloads scoped to each owner."""
    root_path = Path(root)
    current = _lean_file_info(module_source_file(module, root_path))
    if current is None:
        return {}
    pending = list(current.imports)
    visited: set[str] = set()
    result: dict[str, list[tuple[str, str, dict[str, str]]]] = {}
    while pending:
        imported = pending.pop()
        if imported in visited:
            continue
        visited.add(imported)
        info = _lean_file_info(root_path / (imported.replace(".", "/") + ".lean"))
        if info is None:
            continue
        lines = info.lines
        headers = info.parsed("inductive_headers", lambda i: inductive_headers(i.lines))
        payloads = info.parsed(
            "inductive_constructor_types",
            lambda i: inductive_constructor_types(i.lines),
        )
        for name, header in headers.items():
            result.setdefault(name, []).append(
                (imported, header, payloads.get(name, {}))
            )
        pending.extend(info.imports)
    return result


@lru_cache(maxsize=None)
def imported_structure_headers(module: str, root: str) -> dict[str, list[str]]:
    """Header binders of structures reachable through this dotted module name.

    Mirrors `imported_structure_field_types` so the word-dimension qualifier can
    read an imported carrier's `[NeZero width]` discharge from its actual
    declaration rather than from a same-named local duplicate.
    """
    root_path = Path(root)
    current = _lean_file_info(module_source_file(module, root_path))
    if current is None:
        return {}
    pending = list(current.imports)
    visited: set[str] = set()
    result: dict[str, list[str]] = {}
    while pending:
        imported = pending.pop()
        if imported in visited:
            continue
        visited.add(imported)
        info = _lean_file_info(root_path / (imported.replace(".", "/") + ".lean"))
        if info is None:
            continue
        lines = info.lines
        for name, header in info.parsed(
            "structure_headers", lambda i: structure_headers(i.lines)
        ).items():
            result.setdefault(name, []).append(header)
        pending.extend(info.imports)
    return result


@lru_cache(maxsize=None)
def imported_structure_owners(
    module: str, root: str
) -> dict[str, list[tuple[str, str, dict[str, str]]]]:
    """Per-owner declarations of imported structures for a dotted module name.

    The result is name -> [(module, header, fields)].

    The word-dimension qualifier must bind each candidate carrier to its own
    module, header, and field set.  Pooling headers and field types across
    same-named structures (a fake local shadow and an imported owner) would let
    one owner's `[NeZero width]` combine with another owner's `BitVec` field, so
    the evidence is grouped per declaration here instead.
    """
    root_path = Path(root)
    current = _lean_file_info(module_source_file(module, root_path))
    if current is None:
        return {}
    pending = list(current.imports)
    visited: set[str] = set()
    result: dict[str, list[tuple[str, str, dict[str, str]]]] = {}
    while pending:
        imported = pending.pop()
        if imported in visited:
            continue
        visited.add(imported)
        info = _lean_file_info(root_path / (imported.replace(".", "/") + ".lean"))
        if info is None:
            continue
        lines = info.lines
        headers = info.parsed("structure_headers", lambda i: structure_headers(i.lines))
        types = info.parsed(
            "structure_field_types", lambda i: structure_field_types(i.lines)
        )
        for name, fields in types.items():
            result.setdefault(name, []).append(
                (imported, headers.get(name, ""), fields)
            )
        pending.extend(info.imports)
    return result


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
    current = _lean_file_info(module_source_file(module, root_path))
    if current is None:
        return {}
    pending = list(current.imports)
    visited: set[str] = set()
    result: dict[str, list[tuple[str, set[str], dict[str, str]]]] = {}
    while pending:
        imported = pending.pop()
        if imported in visited:
            continue
        visited.add(imported)
        info = _lean_file_info(root_path / (imported.replace(".", "/") + ".lean"))
        if info is None:
            continue
        lines = info.lines
        members = info.parsed("structure_field_map", lambda i: structure_field_map(i.lines))
        types = info.parsed(
            "structure_field_types", lambda i: structure_field_types(i.lines)
        )
        for name, fields in members.items():
            result.setdefault(name, []).append(
                (imported, fields, types.get(name, {}))
            )
        pending.extend(info.imports)
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
    r"^(?:@\[|(?:private |protected |noncomputable |partial |unsafe )*"
    r"(?:def |theorem |lemma |abbrev |instance |structure |inductive ))"
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
            if re.search(
                r"(?:^|\s)(?:(?:private|protected|noncomputable|partial|unsafe)\s+)*"
                r"(?:def|theorem|lemma|abbrev|instance|structure) ",
                stripped,
            ):
                seen_declaration = True
                if ":=" in stripped:
                    break
            continue
        if not line.strip():
            region.append(line)
            continue
        if seen_declaration and TOP_DECL_RE.match(line):
            break
        if re.match(
            r"(?:(?:private|protected|noncomputable|partial|unsafe)\s+)*"
            r"(?:def|theorem|lemma|abbrev|instance|structure) ",
            stripped,
        ):
            seen_declaration = True
        region.append(line)
        if seen_declaration and ":=" in line:
            break
    return "\n".join(region)


def tagged_declaration_source(lines: list[str], attribute_start: int) -> str:
    """Signature and body of the declaration carrying an attribute.

    Most carrier checks need only the signature. Existential representation
    qualifiers also need to inspect a relation body whose existential is in
    the definition, rather than in its type.
    """
    signature = tagged_declaration_text(lines, attribute_start)
    header_lines = len(signature.splitlines())
    body: list[str] = []
    for line in lines[attribute_start - 1 + header_lines:]:
        if TOP_DECL_RE.match(line):
            break
        body.append(line)
    return signature + "\n" + "\n".join(body)


TO_FUNCTION_RE = re.compile(r"\bto([A-Z][A-Za-z0-9_']*)")
OF_FUNCTION_RE = re.compile(r"\bof([A-Z][A-Za-z0-9_']*)")
FMAP_WITNESS_RE = re.compile(
    r"^\s*(?:@\[[\s\S]*?\]\s*)?(?:private\s+|protected\s+)?"
    r"(?:theorem|lemma)\s+holFmapAsFiniteSupportWitness\b"
    r"(?P<statement>[\s\S]*?):=",
    re.M,
)


@lru_cache(maxsize=None)
def _fmap_witness_statements(source: str) -> tuple[str, ...]:
    """Statements of every `holFmapAsFiniteSupportWitness` in `source`.

    The scan does not depend on the carrier being checked, so it is shared by
    every qualified declaration in a module.  A source that never mentions the
    witness name cannot match, which skips the lazy attribute scan entirely.
    """
    if "holFmapAsFiniteSupportWitness" not in source:
        return ()
    return tuple(
        match.group("statement") for match in FMAP_WITNESS_RE.finditer(source)
    )


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
    for statement in _fmap_witness_statements(strip_lean_comments("\n".join(lines))):
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


def _top_level_depth(text: str, end: int) -> int:
    """Parenthesis/bracket depth in `text` before position `end`."""
    depth = 0
    for char in text[:end]:
        if char in "([{":
            depth += 1
        elif char in ")]}":
            depth = max(0, depth - 1)
    return depth


def _lookup_receiver_and_key(side: str) -> tuple[str, str] | None:
    """Split an equality side of shape `<map expr>.lookup <key>`.

    Returns `(receiver, key)` for the last TOP-LEVEL dot lookup application,
    or `None` when the side is not a bare `.lookup` of some map expression
    (for example a wrapping `let`, a prefix application, or a nested term).
    `key` may be any nonempty text; callers separately require it to be a
    universally bound identifier.
    """
    text = _strip_outer_parens(side).strip()
    candidates = [
        match
        for match in re.finditer(r"(?i)\.\s*(?:lookup|flookup)\b", text)
        if _top_level_depth(text, match.start()) == 0
    ]
    if not candidates:
        return None
    match = candidates[-1]
    receiver = text[:match.start()].strip()
    key = text[match.end():].strip()
    if not receiver or not key:
        return None
    return (receiver, key)


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


def fmap_as_finite_support_parameters_errors(
    lines: list[str], module: str, declaration_text: str, decl_name: str,
    parameters: tuple[str, ...],
) -> list[str]:
    """Validate named standalone HolFiniteMapExact input binders.

    This qualifier is for HOL finite-map parameters consumed by a declaration
    whose result is not itself a map. Each named binder must be explicitly
    typed by HolFiniteMapExact and have a same-module lookup/support roundtrip
    witness. It is deliberately separate from the result qualifier, whose
    lookup witness concerns a map-valued result.
    """
    errors: list[str] = []
    if not parameters:
        return ["fmap_as_finite_support_parameters requires at least one binder"]
    if len(set(parameters)) != len(parameters):
        errors.append("fmap_as_finite_support_parameters has duplicate binders")
    for parameter in parameters:
        binder = re.compile(
            r"[({]\s*" + re.escape(parameter)
            + r"\s*:\s*HolFiniteMapExact\b"
        )
        if binder.search(declaration_text) is None:
            errors.append(
                "fmap_as_finite_support_parameters binder "
                f"`{parameter}` must be an input parameter typed HolFiniteMapExact"
            )
            continue
        witness = f"holFmapAsFiniteSupportParamWitness_{decl_name}_{parameter}"
        source = strip_lean_comments("\n".join(lines))
        pattern = re.compile(
            rf"^\s*(?:@\[[\s\S]*?\]\s*)?(?:private\s+|protected\s+)?"
            rf"(?:theorem|lemma)\s+{re.escape(witness)}\b"
            rf"(?P<statement>[\s\S]*?):=",
            re.M,
        )
        match = pattern.search(source)
        if match is None:
            errors.append(
                "fmap_as_finite_support_parameters requires same-module "
                f"canonical witness `{witness}` for binder `{parameter}`"
            )
            continue
        statement = match.group("statement")
        applied = (
            re.search(r"ofBroad\s*[\(.A-Za-z_]", statement) is not None
            and re.search(r"toBroad\s*(?:lookup)?\s*[\(.A-Za-z_]", statement) is not None
            and re.search(r"lookup\s*[\(.A-Za-z_]", statement) is not None
            and re.search(r"\.finiteSupport\b|finiteSupport\s*[\),]", statement) is not None
        )
        if (
            not identifier_token_occurs(statement, parameter)
            or "HolFiniteMapExact" not in statement
            or "lookup" not in statement
            or "finiteSupport" not in statement
            or "toBroad" not in statement
            or "ofBroad" not in statement
            or not applied
            or re.search(r"=\s*" + re.escape(parameter) + r"\b", statement) is None
        ):
            errors.append(
                "fmap_as_finite_support_parameters witness "
                f"`{witness}` must state the canonical lookup/finiteSupport "
                f"toBroad/ofBroad roundtrip for `{parameter}`"
            )
    return errors


def _strip_outer_parens(text: str) -> str:
    """Strip one pair of parentheses only when it encloses the whole string."""
    text = text.strip()
    while text.startswith("(") and text.endswith(")"):
        depth = 0
        enclosed = True
        for index, char in enumerate(text):
            if char == "(":
                depth += 1
            elif char == ")":
                depth -= 1
                if depth == 0 and index != len(text) - 1:
                    enclosed = False
                    break
        if not enclosed or depth != 0:
            break
        text = text[1:-1].strip()
    return text


def _split_type_top_level(text: str, delimiters: tuple[str, ...]) -> list[str]:
    """Split Lean type notation outside balanced parenthesized/bracketed terms."""
    parts: list[str] = []
    start = 0
    parens = brackets = 0
    index = 0
    while index < len(text):
        char = text[index]
        if char == "(":
            parens += 1
        elif char == ")":
            parens -= 1
        elif char == "[":
            brackets += 1
        elif char == "]":
            brackets -= 1
        if parens == 0 and brackets == 0:
            delimiter = next(
                (item for item in delimiters if text.startswith(item, index)), None
            )
            if delimiter is not None:
                parts.append(text[start:index].strip())
                index += len(delimiter)
                start = index
                continue
        index += 1
    parts.append(text[start:].strip())
    return parts


def _tuple_type_components(text: str) -> list[str] | None:
    inner = _strip_outer_parens(text)
    components = _split_type_top_level(inner, ("×",))
    return components if len(components) > 1 else None


def fmap_as_finite_support_function_errors(
    lines: list[str], declaration_source: str, decl_name: str,
    positions: tuple[str, ...],
) -> list[str]:
    """Validate the exact nested finite-map slots of a function type alias.

    This qualifier is intentionally limited to a type abbreviation with one
    top-level arrow, a tuple argument, and an Option-wrapped tuple result. The
    position names are one-based (`argument_N`, `result_N`). It verifies both
    carrier slots are `HolFiniteMapExact`, contain identical canonical map
    types, and account for every such occurrence in the abbreviation.
    """
    errors: list[str] = []
    if not positions:
        return ["fmap_as_finite_support_function requires named map positions"]
    if len(set(positions)) != len(positions):
        errors.append("fmap_as_finite_support_function has duplicate positions")
    parsed: dict[str, int] = {}
    for position in positions:
        match = re.fullmatch(r"(argument|result)_([1-9][0-9]*)", position)
        if match is None:
            errors.append(
                "fmap_as_finite_support_function positions must be one-based "
                "`argument_N` or `result_N` entries"
            )
            continue
        key = match.group(1)
        if key in parsed:
            errors.append(
                "fmap_as_finite_support_function requires exactly one argument "
                "position and one result position"
            )
        parsed[key] = int(match.group(2))
    if set(parsed) != {"argument", "result"}:
        errors.append(
            "fmap_as_finite_support_function requires both argument_N and result_N"
        )

    source = strip_lean_comments(declaration_source)
    module_source = strip_lean_comments("\n".join(lines))
    if re.search(
        r"^\s*(?:private\s+|protected\s+)?theorem\s+"
        r"holFmapAsFiniteSupportWitness\b",
        module_source, re.M,
    ) is None:
        errors.append(
            "fmap_as_finite_support_function requires same-module canonical "
            "holFmapAsFiniteSupportWitness"
        )
    alias_start = re.search(rf"\babbrev\s+{re.escape(decl_name)}\b", source)
    if alias_start is None:
        errors.append(
            "fmap_as_finite_support_function applies only to a type abbreviation"
        )
        return errors
    alias_source = source[alias_start.start():]
    assign = alias_source.find(":=")
    if assign < 0:
        errors.append("fmap_as_finite_support_function cannot find the alias body")
        return errors
    body = alias_source[assign + 2:].strip()
    arrow = _split_type_top_level(body, ("→", "->"))
    if len(arrow) != 2:
        errors.append(
            "fmap_as_finite_support_function requires exactly one top-level function arrow"
        )
        return errors
    argument_parts = _tuple_type_components(arrow[0])
    if argument_parts is None:
        errors.append("fmap_as_finite_support_function argument must be a product")
    result_text = _strip_outer_parens(arrow[1])
    option = re.match(r"Option\s+(.+)$", result_text, re.S)
    result_parts = _tuple_type_components(option.group(1)) if option else None
    if result_parts is None:
        errors.append(
            "fmap_as_finite_support_function result must be Option of a product"
        )

    selected: list[str] = []
    for side, components in (("argument", argument_parts), ("result", result_parts)):
        if components is None or side not in parsed:
            continue
        index = parsed[side] - 1
        if index >= len(components):
            errors.append(
                f"fmap_as_finite_support_function {side}_{index + 1} is outside "
                f"the {len(components)}-component product"
            )
            continue
        component = components[index]
        if "HolFiniteMapExact" not in component:
            errors.append(
                f"fmap_as_finite_support_function {side}_{index + 1} must use "
                "HolFiniteMapExact; raw function maps are ineligible"
            )
        selected.append(re.sub(r"\s+", "", component))
        for other_index, other in enumerate(components):
            if other_index != index and "HolFiniteMapExact" in other:
                errors.append(
                    "fmap_as_finite_support_function positions omit another "
                    f"HolFiniteMapExact at {side}_{other_index + 1}"
                )
    if selected and len(set(selected)) != 1:
        errors.append(
            "fmap_as_finite_support_function argument and result map carriers "
            "must have the same exact type"
        )
    if source.count("HolFiniteMapExact") != 2:
        errors.append(
            "fmap_as_finite_support_function must account for exactly two "
            "HolFiniteMapExact occurrences in the alias"
        )
    return errors


def fmap_as_finite_support_existentials_errors(
    lines: list[str], module: str, declaration_text: str, decl_name: str,
    binders: tuple[str, ...],
) -> list[str]:
    """Validate named existential HolFiniteMapExact binders.

    This qualifier records only the representation of an existential HOL
    finite-map witness. The existential scope and use remain part of the
    tagged declaration and require source review.
    """
    errors: list[str] = []
    if not binders:
        return ["fmap_as_finite_support_existentials requires at least one binder"]
    if len(set(binders)) != len(binders):
        errors.append("fmap_as_finite_support_existentials has duplicate binders")
    for binder in binders:
        existential = re.compile(
            r"∃\s*\(?\s*" + re.escape(binder)
            + r"\s*:\s*HolFiniteMapExact\b"
        )
        if existential.search(declaration_text) is None:
            errors.append(
                "fmap_as_finite_support_existentials binder "
                f"`{binder}` must be an existential typed HolFiniteMapExact"
            )
            continue
        witness = f"holFmapAsFiniteSupportExistentialWitness_{decl_name}_{binder}"
        source = strip_lean_comments("\n".join(lines))
        pattern = re.compile(
            rf"^\s*(?:@\[[\s\S]*?\]\s*)?(?:private\s+|protected\s+)?"
            rf"(?:theorem|lemma)\s+{re.escape(witness)}\b"
            rf"(?P<statement>[\s\S]*?):=",
            re.M,
        )
        match = pattern.search(source)
        if match is None:
            errors.append(
                "fmap_as_finite_support_existentials requires same-module "
                f"canonical witness `{witness}` for binder `{binder}`"
            )
            continue
        statement = match.group("statement")
        colon = _last_top_level_colon(statement)
        binder_zone = statement[:colon] if colon >= 0 else ""
        conclusion = statement[colon + 1:] if colon >= 0 else ""
        has_roundtrip = (
            re.search(r"ofBroad\s*[\(.A-Za-z_]", conclusion) is not None
            and re.search(r"toBroad\s*(?:lookup)?\s*[\(.A-Za-z_]", conclusion) is not None
            and re.search(
                r"\.lookup\s*=\s*" + re.escape(binder) + r"\.lookup\b",
                conclusion,
            ) is not None
            and re.search(
                r"\.finiteSupport\s*=\s*" + re.escape(binder) + r"\.finiteSupport\b",
                conclusion,
            ) is not None
            and re.search(
                r"ofBroad[\s\S]*?toBroad\s+" + re.escape(binder)
                + r"\s*\)\s*=\s*" + re.escape(binder) + r"\b",
                conclusion,
            ) is not None
        )
        if (
            colon < 0
            or "HolFiniteMapExact" not in binder_zone
            or re.search(
                r"\([^():]*:\s*[^)]*(?:lookup|finiteSupport|toBroad|ofBroad)[^)]*\)",
                binder_zone,
            ) is not None
            or "lookup" not in conclusion
            or "finiteSupport" not in conclusion
            or _split_top_level(conclusion, ("\u2192", "->")) is not None
            or not has_roundtrip
        ):
            errors.append(
                "fmap_as_finite_support_existentials witness "
                f"`{witness}` must state the canonical lookup/finiteSupport "
                f"toBroad/ofBroad roundtrip for `{binder}`"
            )
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


def _statements_of_declaration(source: str, name: str) -> list[str]:
    """Return each `theorem|lemma name ...` statement up to its body `:=`.

    The body separator is the first `:=` at parenthesis depth zero, so a
    `:=` appearing inside a `let` or other nested term in the statement does
    not truncate it.
    """
    results: list[str] = []
    for match in re.finditer(
        rf"(?:theorem|lemma)\s+{re.escape(name)}\b", source
    ):
        start = match.end()
        depth = 0
        end = -1
        i = start
        while i < len(source) - 1:
            char = source[i]
            if char in "([{":
                depth += 1
            elif char in ")]}":
                depth = max(0, depth - 1)
            elif char == ":" and source[i + 1] == "=" and depth == 0:
                end = i
                break
            i += 1
        if end != -1:
            results.append(source[start:end])
    return results


def _has_lookup_equality_witness(
    lines: list[str], witness: str, forbidden: str,
    expected: tuple[str, str] | None = None,
) -> tuple[bool, str]:
    source = strip_lean_comments("\n".join(lines))
    statements = _statements_of_declaration(source, witness)
    if not statements:
        return (False, f"has no same-module checked witness `{witness}`")
    for statement in statements:
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
            expected_lhs = _normalize_whitespace(_strip_outer_parens(expected[0]))
            expected_rhs = _normalize_whitespace(_strip_outer_parens(expected[1]))
            left = _lookup_receiver_and_key(lhs)
            right = _lookup_receiver_and_key(rhs)
            if left is None or right is None:
                return (
                    False,
                    f"witness `{witness}` must state each equality side precisely "
                    "as `<map expression>.lookup <key>` (no wrapping `let`, "
                    "prefix lookup, or nested term)",
                )
            left_receiver = _normalize_whitespace(_strip_outer_parens(left[0]))
            right_receiver = _normalize_whitespace(_strip_outer_parens(right[0]))
            if {left_receiver, right_receiver} != {expected_lhs, expected_rhs}:
                return (
                    False,
                    f"witness `{witness}` is not associated with its numbered "
                    "finite-map equality conjunct",
                )
            if left[1] != right[1]:
                return (
                    False,
                    f"witness `{witness}` must apply both lookups at the SAME key",
                )
            if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", left[1]):
                return (
                    False,
                    f"witness `{witness}` must bind its lookup key universally "
                    "(a fixed key does not establish the map equality)",
                )
            if not re.search(
                r"[\(\{]\s*" + re.escape(left[1]) + r"\s*[:\),\}]", binder_zone
            ):
                return (
                    False,
                    f"witness `{witness}` must bind its lookup key universally "
                    f"(no binder for `{left[1]}` in the statement)",
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
    count, naming, exact `<map expression>.lookup <key>` equality shape, same-key
    application, a universally bound key, and per-conjunct textual association
    (each side must be exactly the corresponding conjunct side), but it does NOT
    prove that the Lean witnesses and conjuncts correspond to the HOL map
    equalities. Source review must compare each numbered witness against the HOL
    equality and record that comparison in the reviewer note.
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


_DIMENSION_IDENT_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")
_DIMENSION_DIGITS_RE = re.compile(r"[0-9]+")
_DIMENSION_DIGITS_PAREN_RE = re.compile(r"[0-9]+")


def word_dimension_atoms(text: str) -> list[tuple[str, bool]]:
    """Structurally read the dimension argument of every word-carrier use.

    Rather than a partial regex over bare ``BitVec <id>`` / ``BitVec <digits>``
    spellings, this scans each word carrier (``BitVec`` or a reviewed
    abbreviation) and consumes the actual following dimension atom, so parenthesised
    and arithmetic forms are seen instead of silently skipped. Returns
    ``(atom, parenthesised)`` pairs where ``atom`` is the unparenthesised text of
    the dimension argument; a carrier with no readable argument is skipped.
    """
    atoms: list[tuple[str, bool]] = []
    for match in WORD_CARRIER_TOKEN_RE.finditer(text):
        pos = match.end()
        while pos < len(text) and text[pos].isspace():
            pos += 1
        if pos >= len(text):
            continue
        char = text[pos]
        if char == "(":
            depth = 0
            start = pos
            while pos < len(text):
                if text[pos] == "(":
                    depth += 1
                elif text[pos] == ")":
                    depth -= 1
                    if depth == 0:
                        pos += 1
                        break
                pos += 1
            atoms.append((text[start + 1:pos - 1].strip(), True))
        elif char.isdigit():
            start = pos
            while pos < len(text) and text[pos].isdigit():
                pos += 1
            atoms.append((text[start:pos], False))
        elif char.isalpha() or char == "_":
            start = pos
            while pos < len(text) and (text[pos].isalnum() or text[pos] in "_'"):
                pos += 1
            atoms.append((text[start:pos], False))
    return atoms


def word_dimension_identifier_atoms(text: str) -> list[str]:
    """The identifier word dimensions in `text` (parenthesised or bare)."""
    identifiers: list[str] = []
    for atom, parenthesised in word_dimension_atoms(text):
        if parenthesised:
            if _DIMENSION_IDENT_RE.fullmatch(atom) and not atom[0].isdigit():
                identifiers.append(atom)
        elif _DIMENSION_IDENT_RE.fullmatch(atom):
            identifiers.append(atom)
    return identifiers


def word_dimension_errors(text: str) -> list[str]:
    """Reject every nonpositive or unconstrained word dimension in `text`.

    Inspects every word dimension structurally: an identifier dimension must be a
    bound ``Nat`` parameter with its own ``[NeZero <width>]`` discharge; a numeric
    dimension (including leading-zero and parenthesised spellings such as ``00``,
    ``(0)``) must be positive; and a parenthesised or arithmetic dimension that is
    neither a plain identifier nor plain digits (``(width - width)``, ``(0 + 0)``)
    is rejected rather than skipped.
    """
    errors: list[str] = []
    for atom, parenthesised in word_dimension_atoms(text):
        inner = atom
        if parenthesised and _DIMENSION_DIGITS_RE.fullmatch(inner):
            spelling = f"BitVec ({inner})"
        elif _DIMENSION_DIGITS_RE.fullmatch(inner):
            spelling = f"BitVec {inner}"
        elif parenthesised and _DIMENSION_IDENT_RE.fullmatch(inner) and not inner[0].isdigit():
            spelling = f"BitVec ({inner})"
        elif not parenthesised and _DIMENSION_IDENT_RE.fullmatch(inner):
            spelling = f"BitVec {inner}"
        else:
            errors.append(
                f"`BitVec ({inner})` is not a positive width identifier; every word "
                "dimension in scope must be an explicit `Nat` parameter with its own "
                "`[NeZero <width>]` discharge"
            )
            continue
        if _DIMENSION_DIGITS_RE.fullmatch(inner):
            if int(inner) == 0:
                errors.append(
                    f"`{spelling}` is not a positive width; the qualifier records HOL's "
                    "positive `dimindex (:α)` dimension"
                )
            continue
        width = inner
        if NAT_WIDTH_BINDER_RE.search(text) is None or re.search(
            r"[\{\(]\s*" + re.escape(width) + r"\s*:\s*Nat\s*[\}\)]", text
        ) is None:
            errors.append(
                f"`{spelling}` is not at a `Nat` width binder; every word "
                "dimension in scope must be an explicit positive-width parameter"
            )
        elif re.search(
            r"\[\s*NeZero\s+" + re.escape(width) + r"\s*\]", text
        ) is None:
            errors.append(
                f"`{spelling}` lacks its own `[NeZero {width}]` discharge; "
                "every word dimension in scope must be constrained"
            )
    for neZero in re.finditer(r"\[\s*NeZero\s+([^\]]*?)\s*\]", text):
        argument = neZero.group(1).strip()
        if re.fullmatch(r"\(?\s*[A-Za-z_][A-Za-z0-9_']*\s*\)?", argument):
            continue
        if re.fullmatch(r"\(?\s*0+\s*\)?", argument):
            errors.append(
                "`[NeZero 0]` is not a valid positivity discharge; the dimension must "
                "be a positive width identifier"
            )
        else:
            errors.append(
                f"`[NeZero {argument}]` must discharge a width identifier; a literal "
                "or compound dimension is not a valid positivity discharge"
            )
    return errors


def words_as_type_indexed_bitvec_errors(
    declaration_text: str,
    declaration: str,
    module: str = "",
    root: str = "",
    lines: list[str] | None = None,
) -> list[str]:
    """Validate the HOL word-dimension / FFI-universe translation qualifier.

    The qualifier records the candidate standard translation of HOL's
    type-indexed ``'a word`` (dimension ``dimindex (:α)``) to Lean's
    positive-width ``BitVec width`` and of HOL's ``'ffi ffi_state`` to a
    universe-0 Lean host type. It is a translation statement only: it changes
    no quantifier, hypothesis, side condition, or conclusion, and it requires
    no cross-assistant agreement theorem.

    The checker inspects EVERY word dimension named in the declaration scope,
    not only the first: each ``BitVec <id>`` (or reviewed abbreviation such as
    ``RiscV.Word <id>``) must sit at a bound ``Nat`` width parameter with its own
    ``[NeZero <id>]``. A literal zero dimension (``BitVec 0``) and a
    ``[NeZero 0]`` instance are rejected, so an unrelated ``[NeZero width]``
    cannot license a second, unconstrained word width. The ``[NeZero width]``
    discharge of ``dimindex (:α) ≥ 1`` must be retained and must not be
    restated as an extra hypothesis, and an FFI host type must be bound by a
    ``{σ : Type}``/``(σ : Type 0)`` binder at the universe-0 ``Type`` (a
    ``Type`` with a positive level, a universe-level variable, or ``Sort`` is
    rejected).

    A signature need not spell out ``BitVec`` when it is stated over a
    width-indexed carrier: the qualifier is also accepted when the signature
    names a structure or inductive family (declared locally or reached through
    imports) whose own header carries ``[NeZero <width>]`` and whose fields or
    constructor payloads reach a direct ``BitVec <width>`` field through
    uniquely resolved, HOL-tagged width-indexed carriers. Every owner in that
    chain must retain the same width and its own positivity instance. Resolution
    follows typed payload references, not names alone; a same-named local
    duplicate shadowing an imported owner is rejected as ambiguous. Existing
    special handling for HOL ``ValueHOL``/``HolWordLab`` additionally checks
    their exact one-constructor wrapper shape.
    """
    errors: list[str] = []
    if not declaration_text.strip():
        return [
            "words_as_type_indexed_bitvec requires a resolvable tagged declaration "
            f"signature (checked for `{declaration}`)"
        ]
    stripped = strip_lean_comments(declaration_text)
    decl_start = re.search(
        r"(?:^|\s)(?:def|theorem|lemma|abbrev|instance|structure)\s", stripped
    )
    if decl_start is not None:
        stripped = stripped[decl_start.start():]
    has_body = ":=" in stripped
    signature, body = stripped.split(":=", 1) if has_body else (stripped, "")
    if not signature.strip():
        signature = stripped
    # For a type abbreviation, the words occur in its RHS, while Lean's
    # elaborated declaration type is only `Nat → Type`. Check the body for
    # carriers and the signature for the matching Nat/[NeZero] binders.
    word_scope = signature + ("\n" + body if re.search(r"\babbrev\s", signature) else "")

    errors.extend(word_dimension_errors(word_scope))
    direct_ids = set(word_dimension_identifier_atoms(word_scope))
    # A literal dimension such as `BitVec 5` (the `5 word` globals key type, say)
    # is not itself the `dimindex (:α)` translation; only an identifier dimension
    # takes the direct route. A literal-only signature still has to resolve a
    # reviewed carrier, and a literal `0` is rejected by `word_dimension_errors`.
    has_direct_word = bool(direct_ids)
    if has_direct_word:
        direct_widths = set(
            match.group(1) for match in NAT_WIDTH_BINDER_RE.finditer(signature)
        )
        if not any(identifier in direct_widths for identifier in direct_ids):
            errors.append(
                "words_as_type_indexed_bitvec must name the Lean positive-width word "
                "carrier `BitVec <width>` at a `Nat` width binder that translates HOL "
                "`'a word`; a fixed literal dimension is not the `dimindex (:α)` "
                "translation"
            )

    carrier_ok = False
    if not has_direct_word and lines is not None and module and root:
        local_types = structure_field_types(lines)
        local_types.update(inductive_constructor_types(lines))
        local_headers = structure_headers(lines)
        local_headers.update(inductive_headers(lines))
        imported_owners = {
            name: list(owners)
            for name, owners in imported_structure_owners(module, root).items()
        }
        for name, owners in imported_inductive_owners(module, root).items():
            imported_owners.setdefault(name, []).extend(owners)
        all_owners_by_name: dict[str, list[tuple[str, str, dict[str, str]]]] = {}
        for name in set(local_types) | set(imported_owners):
            owners: list[tuple[str, str, dict[str, str]]] = []
            if name in local_types:
                owners.append(
                    (module, local_headers.get(name, ""), local_types[name])
                )
            owners.extend(imported_owners.get(name, []))
            all_owners_by_name[name] = owners
        owners_by_name = {
            name: owners for name, owners in all_owners_by_name.items()
            if identifier_token_occurs(word_scope, name)
        }
        ambiguous = [
            name for name, owners in owners_by_name.items() if len(owners) != 1
        ]
        if ambiguous:
            errors.append(
                "words_as_type_indexed_bitvec must resolve each width-indexed "
                "carrier to a single owning declaration; ambiguous same-named "
                "owners were found for "
                + ", ".join(sorted(ambiguous))
                + " (a local duplicate shadowing an imported owner must be "
                "removed or disambiguated by signature)"
            )
        else:
            candidate_errors: list[str] = []
            def has_hol_tag(owner_module: str, owner_name: str) -> bool:
                info = _lean_file_info(module_source_file(owner_module, Path(root)))
                if info is None:
                    return False
                source_lines = info.parsed(
                    "stripped_lines",
                    lambda i: strip_lean_comments(i.text).splitlines(),
                )
                inductive_re = re.compile(
                    rf"^\s*inductive\s+{re.escape(owner_name)}(?:\s|\()"
                )
                declaration_line = next(
                    (
                        index for index, line in enumerate(source_lines)
                        if inductive_re.match(line)
                    ),
                    None,
                )
                if declaration_line is None:
                    return False
                # Allow a multiline @[hol] attribute, but do not borrow one
                # from an earlier declaration in the same module.
                prefix: list[str] = []
                declaration_re = re.compile(
                    r"^\s*(?:def|theorem|lemma|abbrev|instance|structure|inductive)\s"
                )
                for line in reversed(source_lines[:declaration_line]):
                    if declaration_re.match(line):
                        break
                    prefix.append(line)
                return any("@[hol" in line for line in prefix)

            def owner_has_width(
                owner: tuple[str, str, dict[str, str]], width: str
            ) -> bool:
                _owner_module, header, _payloads = owner
                return (
                    re.search(
                        r"[\{\(]\s*" + re.escape(width) + r"\s*:\s*Nat\s*[\}\)]",
                        header,
                    ) is not None
                    and re.search(
                        r"\[\s*NeZero\s+" + re.escape(width) + r"\s*\]",
                        header,
                    ) is not None
                )

            def reaches_bitvec(owner_name: str, width: str, seen: set[str]) -> bool:
                if owner_name in seen:
                    return False
                owners = all_owners_by_name.get(owner_name, [])
                if len(owners) != 1:
                    return False
                owner_module, header, payloads = owners[0]
                if not owner_has_width(owners[0], width):
                    return False
                # This recursive path is for exact syntax families only. It
                # must not accept an unrelated aggregate that merely contains
                # a word-bearing field.
                if not has_hol_tag(owner_module, owner_name):
                    return False
                owner_text = header + "\n" + "\n".join(payloads.values())
                dimension_ids = set(word_dimension_identifier_atoms(owner_text))
                if word_dimension_errors(owner_text):
                    return False
                if dimension_ids:
                    return width in dimension_ids and dimension_ids <= {width}
                next_seen = seen | {owner_name}
                payload_text = "\n".join(payloads.values())
                for nested_name, nested_owners in all_owners_by_name.items():
                    if len(nested_owners) != 1 or nested_name in next_seen:
                        continue
                    if not has_hol_tag(nested_owners[0][0], nested_name):
                        continue
                    if not owner_has_width(nested_owners[0], width):
                        continue
                    if re.search(
                        rf"(?<![A-Za-z0-9_']){re.escape(nested_name)}\s+"
                        rf"\(?{re.escape(width)}\)?(?![A-Za-z0-9_'])",
                        payload_text,
                    ) and reaches_bitvec(nested_name, width, next_seen):
                        return True
                return False

            def exact_hol_word_lab_carrier() -> bool:
                # ValueHOL stores word values through the exact HOL `word_lab`
                # wrapper. Do not bless HolWordLab by its name: resolve its
                # unique declaration and check its positive width and sole
                # BitVec payload before accepting the aggregate ValueHOL.
                nested_owners: list[tuple[str, str, dict[str, str]]] = []
                if "HolWordLab" in local_types:
                    nested_owners.append((
                        module, local_headers.get("HolWordLab", ""),
                        local_types["HolWordLab"],
                    ))
                nested_owners.extend(imported_owners.get("HolWordLab", []))
                if len(nested_owners) != 1:
                    return False
                _nested_module, nested_header, nested_payloads = nested_owners[0]
                nested_text = nested_header + "\n" + "\n".join(
                    nested_payloads.values()
                )
                nested_ids = word_dimension_identifier_atoms(nested_text)
                nested_widths = {
                    match.group(1) for match in NAT_WIDTH_BINDER_RE.finditer(nested_header)
                }
                if (
                    word_dimension_errors(nested_text)
                    or len(nested_ids) != 1
                    or nested_ids[0] not in nested_widths
                    or len(nested_payloads) != 1
                ):
                    return False
                payload = next(iter(nested_payloads.values()))
                fields = re.findall(
                    r"\(\s*[A-Za-z_][A-Za-z0-9_']*\s*:\s*([^()]+?)\s*\)",
                    payload,
                )
                return fields == [f"BitVec {nested_ids[0]}"]

            for owner_name, owners in owners_by_name.items():
                _owner_module, header, fields = owners[0]
                owner_text = header + "\n" + "\n".join(fields.values())
                owner_errors = word_dimension_errors(owner_text)
                owner_ids = set(word_dimension_identifier_atoms(owner_text))
                owner_widths = set(
                    match.group(1) for match in NAT_WIDTH_BINDER_RE.finditer(owner_text)
                )
                if (
                    not owner_errors
                    and any(identifier in owner_widths for identifier in owner_ids)
                ):
                    carrier_ok = True
                    break
                # Exact HOL `panSem$v` (`ValueHOL`) contains `HolWordLab width`
                # in its Val constructor. Resolve both owners independently:
                # ValueHOL must retain positive width, and HolWordLab must be
                # its exact one-constructor BitVec wrapper at positive width.
                if owner_name == "ValueHOL":
                    value_text = owner_text.replace("HolWordLab", "BitVec")
                    value_ids = word_dimension_identifier_atoms(value_text)
                    value_widths = {
                        match.group(1)
                        for match in NAT_WIDTH_BINDER_RE.finditer(header)
                    }
                    if (
                        not word_dimension_errors(value_text)
                        and value_ids
                        and all(identifier in value_widths for identifier in value_ids)
                        and exact_hol_word_lab_carrier()
                    ):
                        carrier_ok = True
                        break
                # Some exact HOL syntax is several datatypes away from words
                # at the theorem boundary (DeclHOL -> FunDeclHOL -> ProgHOL ->
                # ExpHOL -> BitVec). Follow only typed payload references
                # through unique, tagged owners, preserving the same width.
                owner_widths = {
                    match.group(1)
                    for match in NAT_WIDTH_BINDER_RE.finditer(header)
                }
                if len(owner_widths) == 1:
                    width = next(iter(owner_widths))
                    if (
                        owner_has_width(owners[0], width)
                        and has_hol_tag(_owner_module, owner_name)
                        and reaches_bitvec(owner_name, width, set())
                    ):
                        carrier_ok = True
                        break
                if owner_ids and not candidate_errors:
                    candidate_errors = owner_errors
            if not carrier_ok and candidate_errors:
                errors.extend(candidate_errors)

    if not has_direct_word:
        if not carrier_ok:
            errors.append(
                "words_as_type_indexed_bitvec must name the Lean positive-width word "
                "carrier `BitVec` that translates HOL `'a word`, or name a reviewed "
                "width-indexed carrier structure whose fields include `BitVec`-typed "
                "fields and whose declaration retains `[NeZero width]`"
            )
        if "NeZero" not in signature and not carrier_ok:
            errors.append(
                "words_as_type_indexed_bitvec must retain the `[NeZero width]` discharge "
                "of HOL `dimindex (:α) ≥ 1`"
            )
    extra = WORD_POSITIVITY_EXTRA_RE.search(signature)
    if extra is not None:
        errors.append(
            "words_as_type_indexed_bitvec must not restate word-dimension positivity "
            f"as an extra hypothesis (`{extra.group(0).strip()}`); `[NeZero width]` is "
            "the only allowed side condition"
        )
    if HOL_FFI_CARRIER_RE.search(signature):
        host_binder = re.search(
            r"[\{\(]\s*[^\s:(){}]+\s*:\s*Type\s*0?\s*[\}\)]", signature
        )
        if host_binder is None:
            errors.append(
                "words_as_type_indexed_bitvec must bind the FFI host type at a `Type` "
                "universe for HOL `'ffi ffi_state`"
            )
        if (
            FFI_UNIVERSE_LEVEL_RE.search(signature) is not None
            or FFI_SORT_RE.search(signature) is not None
            or re.search(r":\s*Type\s+(?!0\b)\d", signature) is not None
        ):
            errors.append(
                "words_as_type_indexed_bitvec must not introduce an FFI universe-level "
                "variable or a `Sort`; use the universe-0 `Type` instance"
            )
    return errors


def word_dimension_as_width_errors(declaration_text: str, declaration: str,
                                   width_name: str) -> list[str]:
    """Validate the narrow word-free type-dimension-to-Nat translation."""
    if not declaration_text.strip():
        return [
            "word_dimension_as_width requires a resolvable tagged declaration "
            f"signature (checked for `{declaration}`)"
        ]
    stripped = strip_lean_comments(declaration_text)
    decl_start = re.search(
        r"(?:^|\s)(?:def|theorem|lemma|abbrev|instance|structure)\s", stripped
    )
    if decl_start is not None:
        stripped = stripped[decl_start.start():]
    signature = stripped.split(":=", 1)[0]
    if not signature.strip():
        signature = stripped
    widths = {match.group(1) for match in NAT_WIDTH_BINDER_RE.finditer(signature)}
    errors: list[str] = []
    if width_name not in widths:
        errors.append(
            f"word_dimension_as_width `{width_name}` must name an explicit `(width : Nat)` binder"
        )
    if re.search(
        r"\[\s*NeZero\s+" + re.escape(width_name) + r"\s*\]", signature
    ) is None:
        errors.append(
            f"word_dimension_as_width `{width_name}` must retain its own `[NeZero {width_name}]` binder"
        )
    if WORD_CARRIER_TOKEN_RE.search(signature):
        errors.append(
            "word_dimension_as_width is only for word-free signatures; use "
            "words_as_type_indexed_bitvec for a signature carrying words"
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
             fmap_relation, fmap_equalities, words_bitvec,
             fmap_parameters, fmap_existentials, dimension_width,
             fmap_function_positions) in hol_attribute_sites(
                lines, include_fmap_existentials=True,
                include_word_dimension_width=True,
                include_fmap_function=True,
             ):
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
            if fmap_parameters:
                if fmap_fields or fmap_result or fmap_relation or fmap_equalities:
                    errors.append(
                        f"{where}: fmap_as_finite_support_parameters is "
                        "mutually exclusive with other finite-map qualifiers"
                    )
                errors.extend(
                    f"{where}: {error}"
                    for error in fmap_as_finite_support_parameters_errors(
                        lines, rel, tagged_declaration_text(lines, number),
                        lean_decl, fmap_parameters,
                    )
                )
            if fmap_existentials:
                errors.extend(
                    f"{where}: {error}"
                    for error in fmap_as_finite_support_existentials_errors(
                        lines, module, tagged_declaration_source(lines, number),
                        lean_decl, fmap_existentials,
                    )
                )
            if fmap_result:
                errors.extend(
                    f"{where}: {error}"
                    for error in fmap_as_finite_support_result_errors(
                        lines, rel, tagged_declaration_text(lines, number), lean_decl
                    )
                )
            if fmap_function_positions:
                if (fmap_fields or fmap_result or fmap_parameters or fmap_existentials
                        or fmap_relation or fmap_equalities):
                    errors.append(
                        f"{where}: fmap_as_finite_support_function is mutually "
                        "exclusive with other finite-map qualifiers"
                    )
                errors.extend(
                    f"{where}: {error}"
                    for error in fmap_as_finite_support_function_errors(
                        lines, tagged_declaration_source(lines, number), lean_decl,
                        fmap_function_positions,
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
            if words_bitvec:
                errors.extend(
                    f"{where}: {error}"
                    for error in words_as_type_indexed_bitvec_errors(
                        tagged_declaration_source(lines, number),
                        lean_decl,
                        module=module,
                        root=str(ROOT),
                        lines=lines,
                    )
                )
            if dimension_width:
                if words_bitvec:
                    errors.append(
                        f"{where}: word_dimension_as_width is mutually exclusive with "
                        "words_as_type_indexed_bitvec"
                    )
                errors.extend(
                    f"{where}: {error}"
                    for error in word_dimension_as_width_errors(
                        tagged_declaration_text(lines, number), lean_decl,
                        dimension_width,
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
