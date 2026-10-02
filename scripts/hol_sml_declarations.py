"""Narrow source recognition of literal HOL generator bindings.

This identifies source locations, not theorem truth or new trusted sources.
It covers Hol_reln's reviewed tuple form, bounded define_run calls, and the
bounded define_monad_access_funs / define_MFarray_manip_funs accessor factories
and the bounded define_monad_exception_functions factory, and the L3 Import
`Construct`/`Record` type declarations of L3-generated model scripts.
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
        val_patterns = re.finditer(r'^[ \t]*(?P<token>val)\s+(?P<pattern>[^=;]*?)=',
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
            identifier = r"(?<![A-Za-z0-9_'])" + re.escape(array_fields) + r"(?![A-Za-z0-9_'])"
            val_patterns = re.finditer(r'^[ \t]*(?P<token>val)\s+(?P<pattern>[^=;]*?)=',
                                      masked[:match.start()], re.MULTILINE)
            bindings = sum(candidate.start('token') not in nested and
                           re.search(identifier, candidate['pattern']) is not None
                           for candidate in val_patterns)
            functions = re.finditer(r'^[ \t]*(?P<token>fun)\s+' + re.escape(array_fields) +
                                    r'(?=\s|\(|=)', masked[:match.start()], re.MULTILINE)
            if any(candidate.start('token') not in nested for candidate in functions):
                continue
            for candidate in binding.finditer(masked, 0, match.start()):
                if candidate.start() in nested:
                    continue
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


def _top_level_bindings(masked: str, nested: set[int], name: str, before: int) -> int:
    """Count top-level `val`/`fun` patterns that bind `name` before `before`."""
    identifier = r"(?<![A-Za-z0-9_'])" + re.escape(name) + r"(?![A-Za-z0-9_'])"
    count = 0
    for binding in re.finditer(r'^[ \t]*(?P<token>val|fun)\s+(?P<pattern>[^=;]*?)=',
                               masked[:before], re.MULTILINE):
        if binding.start('token') in nested:
            continue
        pattern = binding['pattern']
        if binding['token'] == 'fun':
            pattern = pattern.split()[0] if pattern.split() else ''
        if re.search(identifier, pattern):
            count += 1
    return count


def _record_fields(comment_masked: str, type_name: str, before: int) -> list[str] | None:
    """Field names, in order, of the unique top-level `Datatype:` record
    `type_name = <| f : ty; ... |>` declared before offset `before`."""
    block = re.compile(
        r'^Datatype\s*:?\s*\n\s*' + re.escape(type_name) + r'\s*=\s*<\|(?P<body>.*?)\|>\s*\nEnd\b',
        re.MULTILINE | re.DOTALL)
    found = [m for m in block.finditer(comment_masked, 0, before)]
    if len(found) != 1:
        return None
    fields = []
    for part in found[0]['body'].split(';'):
        field = re.match(r'\s*(' + _NAME + r')\s*:', part)
        if field is None:
            return None
        fields.append(field.group(1))
    return fields if len(set(fields)) == len(fields) else None


def monad_accessor_declarations(text: str) -> list[tuple[tuple[str, ...], int, int]]:
    """Recognize ml_monadBaseLib's generated state accessors.

    A top-level `val ACC = define_monad_access_funs ``:TY``;` call, with `TY`
    the unique literal `Datatype:` record declared earlier in the file,
    generates `get_F_def` and `set_F_def` for every record field `F`, in order.
    A top-level `val _ = define_MFarray_manip_funs [A1, ...] SUB UPD;` call,
    whose every `Ai` is bound exactly once at top level by `val Ai = el K ACC;`
    for such an `ACC` with `1 <= K <= #fields`, made after that generator call
    with no rebinding of `ACC` in between and no top-level rebinding of `el`
    before the manip call, generates `F_length_def`,
    `F_sub_def` and `update_F_def` for each selected field `F`. Both
    factories follow `cakeml/translator/monadic/monad_base/ml_monadBaseLib.sml`.
    This records source provenance only, not elaboration or type equivalence.
    Shadowed factories, aliases, nested or rebound bindings, non-literal types,
    computed indices and unterminated calls are excluded.
    """
    comment_masked, quotes = _headers_and_quotes(text)
    masked = _mask_modern_blocks(text, comment_masked)
    nested = _nested_positions(masked)
    result: list[tuple[tuple[str, ...], int, int]] = []
    # accessor-list binding -> (record fields, offset of its generator call)
    access: dict[str, tuple[list[str], int]] = {}

    def line(offset: int) -> int:
        return text.count('\n', 0, offset) + 1

    def shadowed(factory: str, before: int) -> bool:
        return _top_level_bindings(masked, nested, factory, before) > 0

    header = re.compile(
        r'^val\s+(?P<acc>' + _NAME + r')\s*=\s*define_monad_access_funs\s+(?P<quote>``)',
        re.MULTILINE)
    for match in header.finditer(masked):
        if match.start() in nested or shadowed('define_monad_access_funs', match.start()):
            continue
        close = quotes.get(match.start('quote'))
        if close is None:
            continue
        literal = re.fullmatch(r'``\s*:\s*(' + _NAME + r')\s*``', text[match.start('quote'):close])
        if literal is None or not re.match(r'\s*;', text[close:]):
            continue
        fields = _record_fields(comment_masked, literal.group(1), match.start())
        if fields is None:
            continue
        if _top_level_bindings(masked, nested, match['acc'], match.start()) > 0:
            continue
        names = tuple(prefix + field + '_def' for field in fields for prefix in ('get_', 'set_'))
        end = close + re.match(r'\s*;', text[close:]).end()
        access[match['acc']] = (fields, match.start())
        result.append((names, line(match.start()), line(end)))

    manip = re.compile(
        r'^val\s+(?P<lhs>' + _NAME + r')\s*=\s*define_MFarray_manip_funs\s*'
        r'\[(?P<items>[^\[\]]*)\]\s*(?P<sub>' + _NAME + r')\s+(?P<upd>' + _NAME + r')\s*;',
        re.MULTILINE)
    for match in manip.finditer(masked):
        if match.start() in nested or shadowed('define_MFarray_manip_funs', match.start()):
            continue
        # The selector must be the Pervasive `el`: any top-level rebinding
        # before the manip call disqualifies every selection.
        if shadowed('el', match.start()):
            continue
        items = [item.strip() for item in match['items'].split(',')]
        selected = []
        for item in items:
            if re.fullmatch(_NAME, item) is None:
                break
            if _top_level_bindings(masked, nested, item, match.start()) != 1:
                break
            binding = [b for b in re.finditer(
                r'^val\s+' + re.escape(item) + r'\s*=\s*el\s+(?P<k>[0-9]+)\s+(?P<acc>' + _NAME + r')\s*;',
                masked[:match.start()], re.MULTILINE) if b.start() not in nested]
            if len(binding) != 1 or binding[0]['acc'] not in access:
                break
            fields, generator = access[binding[0]['acc']]
            # Chronology: the generator call precedes the selection, and the
            # generator is the only top-level binding of the accessor list in
            # force at the selection.
            if not generator < binding[0].start():
                break
            if _top_level_bindings(masked, nested, binding[0]['acc'], binding[0].start()) != 1:
                break
            k = int(binding[0]['k'])
            if not 1 <= k <= len(fields):
                break
            selected.append(fields[k - 1])
        else:
            if selected and len(set(selected)) == len(selected):
                names = tuple(name for field in selected
                              for name in (field + '_length_def', field + '_sub_def',
                                           'update_' + field + '_def'))
                result.append((names, line(match.start()), line(match.end())))
    return result


def _variant_constructors(comment_masked: str, type_name: str, before: int) -> list[str] | None:
    """Constructor names, in order, of the unique top-level `Datatype:` variant
    `type_name = C1 ... | C2 ... | ...` declared before offset `before`."""
    block = re.compile(
        r'^Datatype\s*:?\s*\n\s*' + re.escape(type_name) + r'\s*=(?P<body>.*?)\nEnd\b',
        re.MULTILINE | re.DOTALL)
    found = [m for m in block.finditer(comment_masked, 0, before)]
    if len(found) != 1:
        return None
    body = found[0]['body']
    # Only a plain variant: no record, no nested datatype, no bracketed alternatives.
    if any(token in body for token in ('<|', '|>', ';', '(', ')')):
        return None
    constructors = []
    for alternative in body.split('|'):
        head = re.match(r'\s*(' + _NAME + r')\b', alternative)
        if head is None or not head.group(1)[0].isupper():
            return None
        constructors.append(head.group(1))
    return constructors if len(set(constructors)) == len(constructors) else None


def monad_exception_declarations(text: str) -> list[tuple[tuple[str, ...], int, int]]:
    """Recognize ml_monadBaseLib's generated exception functions.

    A top-level `val NAME = define_monad_exception_functions ``:EXN`` ``:STATE``;`
    call, with `EXN` the unique literal `Datatype:` variant declared earlier in
    the same file, generates `raise_C_def` and `handle_C_def` for every
    constructor `C` of `EXN`, in order
    (`cakeml/translator/monadic/monad_base/ml_monadBaseLib.sml:186-307`). This
    records source provenance only, not elaboration or type equivalence. A call
    whose exception type is declared elsewhere (for example in an ancestor
    theory), shadowed factories, nested or rebound bindings, non-literal types,
    record or parenthesised alternatives and unterminated calls are excluded.
    """
    comment_masked, quotes = _headers_and_quotes(text)
    masked = _mask_modern_blocks(text, comment_masked)
    nested = _nested_positions(masked)
    result: list[tuple[tuple[str, ...], int, int]] = []
    header = re.compile(
        r'^val\s+(?P<lhs>' + _NAME + r')\s*=\s*define_monad_exception_functions\s+(?P<q1>``)',
        re.MULTILINE)
    for match in header.finditer(masked):
        if match.start() in nested:
            continue
        if _top_level_bindings(masked, nested, 'define_monad_exception_functions', match.start()):
            continue
        close1 = quotes.get(match.start('q1'))
        if close1 is None:
            continue
        exn = re.fullmatch(r'``\s*:\s*(' + _NAME + r')\s*``', text[match.start('q1'):close1])
        if exn is None:
            continue
        second = re.match(r'\s*(?=``)', text[close1:])
        if second is None:
            continue
        q2 = close1 + second.end()
        close2 = quotes.get(q2)
        if close2 is None or re.fullmatch(r'``\s*:\s*' + _NAME + r'\s*``', text[q2:close2]) is None:
            continue
        end = re.match(r'\s*;', text[close2:])
        if end is None:
            continue
        constructors = _variant_constructors(comment_masked, exn.group(1), match.start())
        if constructors is None:
            continue
        names = tuple(prefix + c + '_def' for c in constructors for prefix in ('raise_', 'handle_'))
        start_line = text.count('\n', 0, match.start()) + 1
        end_line = text.count('\n', 0, close2 + end.end()) + 1
        result.append((names, start_line, end_line))
    return result


def _l3_tuple_names(text: str, start: int, list_form: bool) -> tuple[list[str], int] | None:
    """Scan one literal L3 `Construct` list or `Record` tuple from `start`.

    Return the type names (the first string literal of each top-level tuple of a
    `Construct` list, or of the single `Record` tuple) and the exclusive end
    offset, or None for any other shape. SML strings are skipped as atoms.
    """
    i = start
    while i < len(text) and text[i].isspace():
        i += 1
    opening = '[' if list_form else '('
    if i >= len(text) or text[i] != opening:
        return None
    depth = 0
    names: list[str] = []
    expect_name = False
    while i < len(text):
        c = text[i]
        if c == '"':
            j = i + 1
            while j < len(text) and text[j] != '"':
                if text[j] == '\\':
                    j += 1
                j += 1
            if j >= len(text):
                return None
            if expect_name:
                literal = text[i + 1:j]
                if re.fullmatch(_NAME, literal) is None:
                    return None
                names.append(literal)
            expect_name = False
            i = j + 1
            continue
        if c in '([':
            depth += 1
            # A type name opens each top-level tuple: depth 2 inside a
            # Construct list, depth 1 for the Record tuple.
            expect_name = c == '(' and depth == (2 if list_form else 1)
        elif c in ')]':
            depth -= 1
            expect_name = False
            if depth == 0:
                return (names, i + 1) if names else None
        elif not c.isspace():
            expect_name = False
        i += 1
    return None


def l3_type_declarations(text: str) -> list[tuple[tuple[str, ...], int, int]]:
    """Recognize the type declarations of an L3-generated model script.

    In a script that begins its theory with `val () = Import.start "THY"`
    (`HOL/examples/l3-machine-code/common/Import.sml:58`), a top-level
    `val _ = Construct [("T1", [...]), ...]` declares the algebraic types
    `T1`, ... and `val _ = Record ("T", [...])` declares the record type `T`
    (`Import.sml:153-165`, both through `Datatype.astHol_datatype`). Only literal
    names in those two literal forms are recognized; this records source
    provenance only, not elaboration or type equivalence. Calls inside comments,
    strings or nested SML scopes, rebound `Construct`/`Record`, and other
    argument shapes are excluded.
    """
    masked, _quotes = _headers_and_quotes(text)
    nested = _nested_positions(masked)
    start = re.search(r'^val\s*\(\s*\)\s*=\s*Import\.start\b', masked, re.MULTILINE)
    if start is None or start.start() in nested:
        return []
    header = re.compile(r'^val\s+_\s*=\s*(?P<kind>Construct|Record)\b', re.MULTILINE)
    result: list[tuple[tuple[str, ...], int, int]] = []
    for match in header.finditer(masked, start.end()):
        if match.start() in nested:
            continue
        if _top_level_bindings(masked, nested, match['kind'], match.start()):
            continue
        scanned = _l3_tuple_names(text, match.end(), match['kind'] == 'Construct')
        if scanned is None:
            continue
        names, end = scanned
        if len(set(names)) != len(names):
            continue
        start_line = text.count('\n', 0, match.start()) + 1
        end_line = text.count('\n', 0, end) + 1
        result.append((tuple(names), start_line, end_line))
    return result
