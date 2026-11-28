#!/usr/bin/env python3
"""Read-only audit of tagged declarations added since origin/main.

For every manifest row whose (hol_path, hol_name) is absent from
origin/main's manifest, compare the Lean signature with the HOL typed capture
recorded under scripts/hol-probes/*.out:

A. Conjunction premises. Count the top-level conjuncts of the capture's
   premise region (everything before the final `⇒`) and of the Lean
   declaration's premises (hypothesis binders plus top-level `→`). Fewer Lean
   conjuncts than HOL conjuncts flags a dropped conjunct.

B. Nested premises. Flag any hypothesis binder whose type has two or more
   top-level `→` when the capture's premise region contains a top-level `∧`
   (a curried `A → B → C` where HOL has `A ∧ B ⇒ C`).

C. Free-variable position. Flag a theorem whose Lean binder list places a
   variable that is free in the capture before an explicitly ∀-quantified one.

D. Free-variable order. When the capture has no explicit ∀, flag free
   variables that are not in their order of first occurrence.

The script writes nothing; it prints the counts and the flagged rows so a
reviewer can rerun it. False positives from renamed binders are expected and
must be justified by hand.
"""
import json, re, glob, subprocess, sys

ROOT = '/home/zksecurity/galette/flapjack'


def strip_lean_comments(text):
    out = []
    i = 0
    depth = 0
    while i < len(text):
        if text.startswith('/-', i):
            depth += 1
            i += 2
            continue
        if depth and text.startswith('-/', i):
            depth -= 1
            i += 2
            continue
        if depth:
            i += 1
            continue
        out.append(text[i])
        i += 1
    return ''.join(out)


def top_level_positions(s, ch, openers='({[', closers=')}]'):
    res = []
    depth = 0
    i = 0
    while i < len(s):
        c = s[i]
        if c in openers:
            depth += 1
        elif c in closers:
            depth -= 1
        elif depth == 0 and s.startswith(ch, i):
            res.append(i)
            i += len(ch)
            continue
        i += 1
    return res


def split_top(s, sep):
    pos = top_level_positions(s, sep)
    parts = []
    last = 0
    for p in pos:
        parts.append(s[last:p])
        last = p + len(sep)
    parts.append(s[last:])
    return parts


def lean_signature(path, name):
    src = strip_lean_comments(open(path, encoding='utf-8', errors='replace').read())
    m = re.search(r'^\s*(?:@\[[^\n]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|public\s+)*'
                  r'(theorem|lemma|def|abbrev|inductive|structure)\s+' + re.escape(name) + r"(?!['A-Za-z0-9_])",
                  src, re.M)
    if not m:
        return None
    start = m.end()
    rest = src[start:]
    cut = rest.find(':=')
    if cut >= 0:
        rest = rest[:cut]
    else:
        cut = rest.find('where')
        if cut >= 0:
            rest = rest[:cut]
    return (m.group(1), re.sub(r'\s+', ' ', rest).strip())


def parse_lean(sig):
    colons = top_level_positions(sig, ':')
    if not colons:
        return [], sig
    split = colons[-1]
    binder_text = sig[:split]
    type_text = sig[split + 1:].strip()
    binders = []
    depth = 0
    cur = ''
    for c in binder_text:
        if c in '({[':
            depth += 1
            if depth == 1:
                cur = ''
                continue
        if c in ')}]':
            depth -= 1
            if depth == 0:
                binders.append(cur.strip())
                cur = ''
                continue
        if depth == 0 and c == ' ':
            continue
        if depth >= 1:
            cur += c
    out = []
    for b in binders:
        if ':' in b:
            n, t = b.split(':', 1)
            out.append((n.strip(), t.strip()))
        else:
            out.append((b.strip(), ''))
    return out, type_text


def looks_prop(t):
    if not t:
        return False
    if t.startswith('∀') or t.startswith('∃'):
        return True
    return any(m in t for m in ('=', '≠', '∈', '¬', '↔', '∧', '≤'))


def main():
    base = json.loads(subprocess.run(['git', 'show', 'origin/main:docs/HOL-THEOREM-MAP.json'],
                                     capture_output=True, text=True).stdout)
    old = {(r['hol_path'], r['hol_name']) for r in base}
    cur = json.load(open('docs/HOL-THEOREM-MAP.json'))
    new = [r for r in cur if (r['hol_path'], r['hol_name']) not in old]

    captures = {}
    for p in glob.glob('scripts/hol-probes/*.out'):
        for line in open(p, encoding='utf-8', errors='replace'):
            m = re.match(r"^([A-Za-z0-9_']+)_typed=(.*)$", line.strip())
            if m and m.group(1) not in captures:
                captures[m.group(1)] = m.group(2)

    flags = {'A': [], 'B': [], 'C': [], 'D': [], 'no_capture': [], 'no_decl': []}
    checked = 0
    for r in new:
        cap = captures.get(r['hol_name'])
        if cap is None:
            flags['no_capture'].append(r['lean_name'])
            continue
        got = lean_signature(r['lean_path'], r['lean_name'])
        if got is None:
            flags['no_decl'].append(r['lean_name'])
            continue
        kind, sig = got
        checked += 1
        binders, typ = parse_lean(sig)
        arrows = len(split_top(typ, '→')) - 1
        prop_binders = [(n, t) for n, t in binders if looks_prop(t)]

        segments = split_top(cap, '⇒')
        hol_prem = '⇒'.join(segments[:-1]) if len(segments) > 1 else ''
        hol_conj = len(top_level_positions(hol_prem, '∧'))
        lean_parts = [t for _, t in prop_binders]
        lean_parts += [typ] if arrows else []
        lean_conj = sum(len(top_level_positions(t, '∧')) for t in lean_parts)

        # A: dropped conjuncts
        if hol_conj > lean_conj:
            flags['A'].append((r['lean_name'], hol_conj, lean_conj, hol_prem[:90]))

        # B: nested curried premise where HOL has a conjunction
        if hol_conj:
            for n, t in prop_binders:
                if len(split_top(t, '→')) - 1 >= 2:
                    flags['B'].append((r['lean_name'], n, t[:90]))
                    break

        explicit = set()
        for g in re.findall(r'∀\s*\(([^)]*)\)', cap):
            for name in re.findall(r"([A-Za-z][A-Za-z0-9_']*)\s*:", g):
                explicit.add(name)

        lean_names = [n for n, _ in binders if re.fullmatch(r"[A-Za-z][A-Za-z0-9_']*", n)]

        # C: explicit binder after a free one
        if kind in ('theorem', 'lemma') and explicit:
            seen_free = False
            for n in lean_names:
                if n in explicit:
                    if seen_free:
                        flags['C'].append((r['lean_name'], lean_names, sorted(explicit)))
                        break
                elif n in cap:
                    seen_free = True

        # D: no explicit forall -> order of first occurrence
        if kind in ('theorem', 'lemma') and not explicit:
            order = []
            for m in re.finditer(r"\b([A-Za-z][A-Za-z0-9_']*)\b", cap):
                w = m.group(1)
                if w in lean_names and w not in order:
                    order.append(w)
            present = [n for n in lean_names if n in cap]
            if present and order and [n for n in present if n in order] != [n for n in order if n in present]:
                flags['D'].append((r['lean_name'], lean_names, order))

    print(f'new rows: {len(new)}  checked with capture+decl: {checked}')
    for k in ('A', 'B', 'C', 'D'):
        print(f'{k} flags: {len(flags[k])}')
    print(f'no capture: {len(flags["no_capture"])}')
    print(f'no decl: {len(flags["no_decl"])}')
    for k in ('A', 'B', 'C', 'D'):
        print(f'--- {k} ---')
        for f in flags[k]:
            print(f)


if __name__ == '__main__':
    main()
