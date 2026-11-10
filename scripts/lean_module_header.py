"""Apply the Lean module-system header to generated Lean source.

Generated files are Lean `module`s (see #1373): `module`, `public import ...`,
then `@[expose] public section`, optionally with `backward.privateInPublic` when
public declarations use private helpers. Generators render the plain source and
pass it through `to_module` so their `--check` output matches the committed file.
"""
import re

PRIVATE_IN_PUBLIC = (
    "\n-- Public declarations below use private helpers.\n"
    "set_option backward.privateInPublic true\n"
    "set_option backward.privateInPublic.warn false\n"
)


def _skip_ws_comments(text, i):
    while i < len(text):
        if text[i].isspace():
            i += 1
        elif text.startswith("--", i):
            j = text.find("\n", i)
            i = len(text) if j < 0 else j + 1
        elif text.startswith("/-", i) and not text.startswith(("/-!", "/--"), i):
            depth = 0
            while i < len(text):
                if text.startswith("/-", i):
                    depth += 1
                    i += 2
                elif text.startswith("-/", i):
                    depth -= 1
                    i += 2
                    if depth == 0:
                        break
                else:
                    i += 1
        else:
            break
    return i


def to_module(text, private_in_public=False):
    """Return `text` with the module-system header inserted after its imports."""
    start = _skip_ws_comments(text, 0)
    i, last = start, None
    while True:
        m = re.compile(r"import[ \t]+[\w.«»]+[^\n]*\n?").match(text, i)
        if not m:
            break
        last = m.end()
        i = _skip_ws_comments(text, m.end())
    extra = PRIVATE_IN_PUBLIC if private_in_public else ""
    if last is None:
        return text[:start] + "module\n\n@[expose] public section\n" + extra + "\n" + text[start:]
    block = re.sub(r"^import ", "public import ", text[start:last], flags=re.M)
    if not block.endswith("\n"):
        block += "\n"
    return text[:start] + "module\n\n" + block + "\n@[expose] public section\n" + extra + text[last:]
