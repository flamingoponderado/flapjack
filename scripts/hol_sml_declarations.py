"""Narrow source recognition of literal HOL generator bindings.

This identifies source locations, not theorem truth or new trusted sources.
It covers Hol_reln's reviewed tuple form and bounded define_run calls.
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


def _mask_modern_blocks(text: str, masked: str) -> str:
    # Modern HOL blocks are not SML scopes: an unquoted HOL `let` inside a
    # Definition must not hide later top-level generator calls. Mask their
    # complete bodies, also excluding apparent bindings in theorem text.
    out = list(masked)
    modern = re.compile(r'^(?:Definition|Theorem|Triviality|Inductive|CoInductive)\b[^\n]*:|^Datatype\s*:?\s*$')
    in_block = False
    offset = 0
    for line in masked.splitlines(keepends=True):
        if not in_block and modern.match(line):
            in_block = True
        if in_block:
            for position in range(offset, offset + len(line)):
                if text[position] != '\n':
                    out[position] = ' '
            if re.match(r'^(?:End|QED)\b', line) or re.search(r'\bQED\s*$', line):
                in_block = False
        offset += len(line)
    return "".join(out)


def _nested_positions(masked: str) -> set[int]:
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
    return nested


def hol_reln_tuple_declarations(text: str) -> list[tuple[tuple[str, ...], int, int]]:
    """Return the three generated names and their shared source span.

    The binding must be top-level, use matching rules/ind/cases names, call
    Hol_reln directly or via composition, and supply a terminated quotation.
    This deliberately excludes aliases and arbitrary tuple-producing calls.
    """
    masked, quotes = _headers_and_quotes(text)
    nested = _nested_positions(masked)
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


def define_run_declarations(text: str) -> list[tuple[str, str, int, int]]:
    """Recognize a bounded literal define_run call's carrier and runner.

    This records source provenance, not successful HOL elaboration or type
    equivalence. The actual generator and its resulting declaration still
    require source review. Only a direct monomorphic type quotation, literal
    array-field list (inline or in an earlier top-level val), literal carrier
    name and matching run_NAME_def binding are supported. Arbitrary aliases,
    expressions, nested bindings and unterminated calls are excluded.
    """
    masked, quotes = _headers_and_quotes(text)
    masked = _mask_modern_blocks(text, masked)
    nested = _nested_positions(masked)
    field = r'"' + _NAME + r'"'
    fields = r'\[\s*(?:' + field + r'(?:\s*,\s*' + field + r')*)?\s*\]'
    header = re.compile(
        r'^val\s+run_(?P<name>' + _NAME + r')_def\s*=\s*define_run\s+(?P<quote>``)',
        re.MULTILINE)
    args = re.compile(
        r'\s*(?P<fields>' + fields + r'|' + _NAME + r')\s*"(?P<name>' + _NAME + r')"\s*;')
    result = []
    for match in header.finditer(masked):
        if match.start() in nested:
            continue
        shadows = re.finditer(r'^[ \t]*(?P<token>val|fun)\s+define_run\b',
                              masked[:match.start()], re.MULTILINE)
        if any(shadow.start('token') not in nested for shadow in shadows):
            continue
        val_patterns = re.finditer(r'^[ \t]*(?P<token>val)\s+(?P<pattern>[^\n=]*)=',
                                   masked[:match.start()], re.MULTILINE)
        if any(binding.start('token') not in nested and
               re.search(r'\bdefine_run\b', binding['pattern'])
               for binding in val_patterns):
            continue
        close = quotes.get(match.start('quote'))
        if close is None:
            continue
        if not re.fullmatch(r'``\s*:\s*' + _NAME + r'\s*``',
                            text[match.start('quote'):close]):
            continue
        tail = args.match(text, close)
        if tail is None or tail['name'] != match['name']:
            continue
        array_fields = tail['fields']
        if not array_fields.startswith('['):
            binding = re.compile(r'^val\s+' + re.escape(array_fields) + r'\s*=\s*', re.MULTILINE)
            literals = []
            bindings = 0
            for candidate in binding.finditer(masked, 0, match.start()):
                if candidate.start() in nested:
                    continue
                bindings += 1
                literal = re.match(fields + r'\s*;', text[candidate.end():])
                if literal is not None:
                    literals.append(literal.group())
            # An ambiguous/rebound array list is deliberately unsupported.
            if bindings != 1 or len(literals) != 1:
                continue
        start = text.count('\n', 0, match.start()) + 1
        end = text.count('\n', 0, tail.end()) + 1
        result.append((match['name'], 'run_' + match['name'] + '_def', start, end))
    return result
