#!/usr/bin/env python3
"""Read-only audit of tagged declarations added since origin/main.

For every manifest row whose (hol_path, hol_name) is absent from
origin/main's manifest, compare the Lean signature with the HOL typed capture.

Captures are resolved through the probes themselves: each
``scripts/hol-probes/<name>_probeScript.sml`` registers ``emit "<label>"
"<HOL name>"`` calls, and ``regenerate.sh``'s ``run_probe`` lines record which
HOL file each probe reads. A row therefore matches a capture by (HOL file
basename, HOL name), which avoids pairing two same-named declarations from
different scripts.

Checks
  A. Conjunction premises. Compare the top-level conjunct count of the
     capture's premise region (before the final `⇒`) with the Lean premises
     (hypothesis binders plus top-level `→`); fewer Lean conjuncts flags a
     dropped conjunct.
  B. Nested premises. Flag a hypothesis binder with two or more top-level `→`
     where the capture's premise region contains a top-level `∧`.
  C. Free-variable position. Flag a theorem that places a variable free in the
     capture before an explicitly ∀-quantified one.
  D. Free-variable order. With no explicit ∀, flag free variables that are not
     in their order of first occurrence.
  E. Type variables. Flag a row whose capture has two or more distinct type
     variables but whose Lean statement has fewer independent type binders.

The script writes nothing; it prints counts and flagged rows so a reviewer can
rerun it. False positives from renamed binders are expected and must be
justified by hand. Two systematic false positives: A also fires when the
capture's `∧` sits in a `⇔` right-hand side, a definition body, or a conjunct
of a multi-part conclusion (the "premise region" is then not a premise); E
fires when the capture's extra type variables are vacuous auto-bound HOL
variables or when the capture is a case-constant equation rather than the
datatype.
"""
import json, re, glob, subprocess, os

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
                  r'(theorem|lemma|def|abbrev|inductive|structure)\s+' + re.escape(name) +
                  r"(?!['A-Za-z0-9_])", src, re.M)
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
    opener = ''
    for c in binder_text:
        if c in '({[':
            depth += 1
            if depth == 1:
                cur = ''
                opener = c
                continue
        if c in ')}]':
            depth -= 1
            if depth == 0:
                binders.append((opener, cur.strip()))
                cur = ''
                continue
        if depth == 0 and c == ' ':
            continue
        if depth >= 1:
            cur += c
    out = []
    for op, b in binders:
        if ':' in b:
            n, t = b.split(':', 1)
            out.append((n.strip(), t.strip(), op))
        else:
            out.append((b.strip(), '', op))
    return out, type_text


def looks_prop(t):
    if not t:
        return False
    if t.startswith('∀') or t.startswith('∃'):
        return True
    return any(m in t for m in ('=', '≠', '∈', '¬', '↔', '∧', '≤'))


def probe_registry():
    """script -> (out_name, hol_file_basename) from regenerate.sh run_probe lines."""
    reg = {}
    lines = open('scripts/hol-probes/regenerate.sh', encoding='utf-8').read().split('\n')
    cur = None
    for line in lines:
        s = line.strip()
        if s.startswith('run_probe '):
            cur = [s[len('run_probe '):].rstrip('\\').strip()]
            continue
        if cur is not None:
            cur.append(s.rstrip('\\').strip())
        if cur is not None and not s.endswith('\\'):
            toks = ' '.join(cur).split()
            if len(toks) >= 4:
                script, out = toks[0], toks[1]
                hol_file = os.path.basename(toks[-2].strip('"'))
                reg[script] = (out, hol_file)
            cur = None
    return reg


def emit_map(script):
    """label -> HOL name from a probe script, for every capture style the
    probes use: `emit`/`emit_exported` (label, name), `show`/`show_thm`
    (label, `Theory.Name`), `dt_label` (label, name) and `type_label`
    (label, theory, name)."""
    res = {}
    text = open('scripts/hol-probes/' + script, encoding='utf-8', errors='replace').read()
    for m in re.finditer(r'emit(?:_exported)?\s+"([^"]+)"\s+"([^"]+)"', text):
        res[m.group(1)] = m.group(2)
    for m in re.finditer(r"show(?:_thm)?\s+\"([^\"]+)\"\s+[A-Za-z0-9_]+\.[A-Za-z0-9_']+", text):
        label = m.group(1).rstrip('=')
        name = re.search(r'\.([A-Za-z0-9_\']+)$', m.group(0)).group(1)
        res[label] = name
    for m in re.finditer(r'dt_label\s+"([^"]+)"\s+"([^"]+)"', text):
        res[m.group(1)] = m.group(2)
    for m in re.finditer(r'type_label\s+"([^"]+)"\s+"[^"]+"\s+"([^"]+)"', text):
        res[m.group(1)] = m.group(2)
    for m in re.finditer(r'show_term\s+"([^"]+)"\s+"([^"]+)"', text):
        res[m.group(1)] = m.group(2)
    return res


def out_values(out_name):
    """label -> capture text from one probe's fixture."""
    res = {}
    path = 'scripts/hol-probes/' + out_name
    if not os.path.exists(path):
        return res
    for line in open(path, encoding='utf-8', errors='replace'):
        m = re.match(r"^([A-Za-z0-9_']+)=(.*)$", line.strip())
        if m:
            res.setdefault(m.group(1), m.group(2))
    return res


def build_captures():
    """HOL name -> list of (hol_file_basename, capture value), plus the raw
    label -> value map for the label fallback.  Each probe's captures are read
    from that probe's own fixture, so identical labels in different probes do
    not shadow one another; the fallback map keeps the first label occurrence
    across all fixtures, as before."""
    reg = probe_registry()
    values = {}
    for out in sorted(glob.glob('scripts/hol-probes/*.out')):
        for label, value in out_values(os.path.basename(out)).items():
            values.setdefault(label, value)
    caps = {}
    for script, (out_name, hol_file) in reg.items():
        spath = 'scripts/hol-probes/' + script
        if not os.path.exists(spath):
            continue
        vals = out_values(out_name)
        if not vals:
            continue
        for label, hol_name in emit_map(script).items():
            if label in vals:
                caps.setdefault(hol_name, []).append((hol_file, vals[label]))
    return caps, values


def resolve_capture(caps, values, hol_path, hol_name):
    """Pick the capture whose registered HOL file matches the row's file, else
    fall back to the conventional `<name>_typed` label."""
    cands = caps.get(hol_name)
    if cands:
        hol_file = os.path.basename(hol_path)
        matching = [v for f, v in cands if f == hol_file]
        if len(matching) == 1:
            return matching[0]
        if len(set(cands_values for _, cands_values in cands)) == 1:
            return cands[0][1]
    return values.get(hol_name + '_typed') or values.get(hol_name)


def main():
    base = json.loads(subprocess.run(['git', 'show', 'origin/main:docs/HOL-THEOREM-MAP.json'],
                                     capture_output=True, text=True).stdout)
    old = {(r['hol_path'], r['hol_name']) for r in base}
    cur = json.load(open('docs/HOL-THEOREM-MAP.json'))
    new = [r for r in cur if (r['hol_path'], r['hol_name']) not in old]
    caps, values = build_captures()

    flags = {'A': [], 'B': [], 'C': [], 'D': [], 'E': [], 'no_capture': [], 'no_decl': []}
    checked = 0
    for r in new:
        cap = resolve_capture(caps, values, r['hol_path'], r['hol_name'])
        if cap is None:
            flags['no_capture'].append((r['lean_name'], r['hol_path'], r['hol_name']))
            continue
        got = lean_signature(r['lean_path'], r['lean_name'])
        if got is None:
            flags['no_decl'].append(r['lean_name'])
            continue
        kind, sig = got
        checked += 1
        binders, typ = parse_lean(sig)
        arrows = len(split_top(typ, '→')) - 1
        prop_binders = [(n, t) for n, t, _ in binders if looks_prop(t)]

        segments = split_top(cap, '⇒')
        hol_prem = '⇒'.join(segments[:-1]) if len(segments) > 1 else ''
        hol_conj = len(top_level_positions(hol_prem, '∧'))
        lean_parts = [t for _, t in prop_binders]
        lean_parts += [typ] if arrows else []
        lean_conj = sum(len(top_level_positions(t, '∧')) for t in lean_parts)

        if hol_conj > lean_conj:
            flags['A'].append((r['lean_name'], hol_conj, lean_conj, hol_prem[:90]))

        if hol_conj:
            for n, t in prop_binders:
                if len(split_top(t, '→')) - 1 >= 2:
                    flags['B'].append((r['lean_name'], n, t[:90]))
                    break

        explicit = set()
        for g in re.findall(r'∀\s*\(([^)]*)\)', cap):
            for name in re.findall(r"([A-Za-z][A-Za-z0-9_']*)\s*:", g):
                explicit.add(name)

        lean_names = [n for n, _, _ in binders if re.fullmatch(r"[A-Za-z][A-Za-z0-9_']*", n)]

        if kind in ('theorem', 'lemma') and explicit:
            seen_free = False
            for n in lean_names:
                if n in explicit:
                    if seen_free:
                        flags['C'].append((r['lean_name'], lean_names, sorted(explicit)))
                        break
                elif n in cap:
                    seen_free = True

        if kind in ('theorem', 'lemma') and not explicit:
            order = []
            for m in re.finditer(r"\b([A-Za-z][A-Za-z0-9_']*)\b", cap):
                w = m.group(1)
                if w in lean_names and w not in order:
                    order.append(w)
            present = [n for n in lean_names if n in cap]
            if present and order and [n for n in present if n in order] != [n for n in order if n in present]:
                flags['D'].append((r['lean_name'], lean_names, order))

        hol_types = set(re.findall(r':([α-ω][′\d]?)', cap))
        lean_types = set()
        for n, t, op in binders:
            if op == '{' and ('Type' in t or 'Sort' in t):
                for part in n.split():
                    lean_types.add(part)
        if len(hol_types) >= 2 and len(lean_types) < len(hol_types):
            flags['E'].append((r['lean_name'], sorted(hol_types), sorted(lean_types)))

    print(f'new rows: {len(new)}  checked with capture+decl: {checked}')
    for k in ('A', 'B', 'C', 'D', 'E'):
        print(f'{k} flags: {len(flags[k])}')
    print(f'no capture: {len(flags["no_capture"])}')
    print(f'no decl: {len(flags["no_decl"])}')
    for k in ('A', 'B', 'C', 'D', 'E'):
        print(f'--- {k} ---')
        for f in flags[k]:
            print(f)
    print('--- no capture ---')
    for f in flags['no_capture']:
        print(f)


if __name__ == '__main__':
    main()
