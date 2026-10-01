"""Narrow source recognition of HOL's three-result Hol_reln bindings.

This identifies source locations, not theorem truth or new trusted sources.
Only the literal generator and its source-used composition form are accepted.
"""

import re

_NAME = r"[A-Za-z_][A-Za-z0-9_']*"
_TUPLE = re.compile(
    r"^val\s*\(\s*(?P<stem>" + _NAME + r")_rules\s*,\s*"
    r"(?P=stem)_ind\s*,\s*(?P=stem)_cases\s*\)\s*=\s*"
    r"(?:Hol_reln\s*|\(\s*Hol_reln\s+o\s+[^\n]*?\)\s*)"
    r"(?P<quote>`{1,2})",
    re.MULTILINE,
)


def _headers_and_quotes(text: str) -> tuple[str, dict[int, int]]:
    """Mask nested comments, SML strings and HOL quotation bodies in place.

    Keep only a real quotation's opening delimiter for matching the generator;
    record its exclusive closing offset. Unterminated quotations are ineligible.
    """
    out = list(text)
    quotes: dict[int, int] = {}
    i = 0

    def mask(start: int, end: int) -> None:
        for j in range(start, end):
            if text[j] != "\n":
                out[j] = " "

    while i < len(text):
        if text.startswith("(*", i):
            start = i
            depth = 1
            i += 2
            while i < len(text) and depth:
                if text.startswith("(*", i):
                    depth += 1
                    i += 2
                elif text.startswith("*)", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            mask(start, i)
        elif text[i] == '"':
            start = i
            i += 1
            while i < len(text):
                if text[i] == "\\":
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
            mask(start, min(i, len(text)))
        elif text[i] in ("`", "“", "‘"):
            start = i
            delimiter = "``" if text.startswith("``", i) else text[i]
            closing = {"“": "”", "‘": "’"}.get(delimiter, delimiter)
            body = i + len(delimiter)
            close = text.find(closing, body)
            if close < 0:
                mask(body, len(text))
                break
            i = close + len(closing)
            mask(body, i)
            quotes[start] = i
        else:
            i += 1
    return "".join(out), quotes


def hol_reln_tuple_declarations(text: str) -> list[tuple[tuple[str, ...], int, int]]:
    """Return the three generated names and their shared source span.

    The binding must be top-level, use matching rules/ind/cases names, call
    Hol_reln directly or via composition, and supply a terminated quotation.
    This deliberately excludes aliases and arbitrary tuple-producing calls.
    """
    masked, quotes = _headers_and_quotes(text)
    # SML block keywords remain visible after comments, strings and HOL terms
    # are masked. Both halves of local/let remain nested until their end.
    scopes = []
    nested = set()
    for token in re.finditer(_NAME, masked):
        word = token.group()
        # HOL command annotations such as Overload NoRead[local] are not
        # SML block openings.
        if word == "local" and masked[:token.start()].rstrip().endswith("["):
            continue
        if word in ("local", "let", "struct", "sig", "abstype"):
            scopes.append(word)
        elif word == "end" and scopes:
            scopes.pop()
        if scopes:
            nested.add(token.start())
    result = []
    for match in _TUPLE.finditer(masked):
        if match.start() in nested:
            continue
        close = quotes.get(match.start("quote"))
        if close is None or not text[close:].lstrip().startswith(";"):
            continue
        stem = match.group("stem")
        names = tuple(stem + suffix for suffix in ("_rules", "_ind", "_cases"))
        start_line = text.count("\n", 0, match.start()) + 1
        end_line = text.count("\n", 0, close) + 1
        result.append((names, start_line, end_line))
    return result
