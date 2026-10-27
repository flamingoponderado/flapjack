#!/usr/bin/env python3
"""Generate CFG production patterns from the pinned HOL cmlG_def capture.

Reject unknown terms and nonterminal inventories; `--check` detects drift.
The generated representation still requires source and parser correspondence
review.  It is not an equivalence proof.
"""
import argparse
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PROBE = ROOT / 'scripts/hol-probes/cake_cfg_grammar_probe.out'
NTS = ROOT / 'Flapjack/CakeParser/Nonterminal.lean'
OUTPUT = ROOT / 'Flapjack/CakeParser/CfgGrammar.lean'


def split_unions(text):
    parts, depth, start = [], 0, 0
    for i, char in enumerate(text):
        if char == '{': depth += 1
        elif char == '}': depth -= 1
        elif char == '∪' and depth == 0:
            parts.append(text[start:i].strip())
            start = i + 1
        if depth < 0: raise ValueError('unbalanced set')
    if depth: raise ValueError('unbalanced set')
    parts.append(text[start:].strip())
    return parts


def token_atom(rule, term, condition):
    if term.startswith('NN '):
        return '.nonterminal .' + term[3:]
    if not term.startswith('TK '): raise ValueError((rule, term))
    token = term[3:]
    if re.fullmatch(r'[A-Za-z]+T', token):
        return '.terminal .' + token[0].lower() + token[1:]
    literal = re.fullmatch(r'\((AlphaT|SymbolT) «([^»]*)»\)', token)
    if literal:
        kind, value = literal.groups()
        if not re.fullmatch(r'[A-Za-z0-9:=+*/.@-]+', value): raise ValueError((rule, value))
        return f'.terminal (.{kind[0].lower() + kind[1:]} (ofString "{value}"))'
    if token == '(TyvarT m)' and condition == 'T': return '.check .isTyvar'
    if token == '(IntT i)' and condition == 'T': return '.check .isInt'
    if token == '(CharT c)' and condition == 'T': return '.check .isChar'
    if token == '(StringT m)' and condition == 'T': return '.check .isString'
    if token == '(WordT n)' and condition == 'T': return '.check .isWord'
    if token == '(FFIT m)' and condition == 'T': return '.check .isFfi'
    if token == '(AlphaT m)' and condition == 'T': return '.anyAlpha'
    if token == '(SymbolT m)' and condition == 'T': return '.anySymbol'
    if token == '(LongidT p m)' and condition == 'T': return '.anyLongid'
    classes = {
        ('nStructName', '(AlphaT s)'): ("s ≠ «»", '.check (.alpha .nonempty)'),
        ('nUQConstructorName', '(AlphaT s)'): ("s ≠ «» ∧ isUpper (strsub s (0 :num))", '.check (.alpha .upperInitial)'),
        ('nV', '(AlphaT s)'): ("s ∉ {«before»; «div»; «mod»; «o»} ∧ s ≠ «» ∧ ¬isUpper (strsub s (0 :num))", '.check (.alpha .lowerInitialNotReserved)'),
        ('nV', '(SymbolT s)'): ('validPrefixSym (explode s)', '.check (.symbol .validPrefix)'),
        ('nFQV', '(LongidT str s)'): ('(str,s) | s ≠ «» ∧ (isAlpha (strsub s (0 :num)) ⇒ ¬isUpper (strsub s (0 :num)))', '.check (.longid .tailNonemptyHeadAlphaNotUpper)'),
        ('nConstructorName', '(LongidT str s)'): ('(str,s) | s ≠ «» ∧ isAlpha (strsub s (0 :num)) ∧ isUpper (strsub s (0 :num))', '.check (.longid .ctorUpperInitial)'),
        ('nOpID', '(LongidT str s)'): ('(str,s) | s ≠ «»', '.check .opidLongidNonempty'),
        ('nOpID', '(AlphaT s)'): ('s ≠ «»', '.check .opidAlphaNonempty'),
        ('nOpID', '(SymbolT s)'): ('s ≠ «»', '.check .opidSymbolNonempty'),
        ('nMultOps', '(SymbolT s)'): ('validMultSym (explode s)', '.check (.symbol .validMult)'),
        ('nAddOps', '(SymbolT s)'): ('validAddSym (explode s)', '.check (.symbol .validAdd)'),
        ('nRelOps', '(SymbolT s)'): ('validRelSym (explode s)', '.check (.symbol .validRel)'),
        ('nListOps', '(SymbolT s)'): ('validListSym (explode s)', '.check (.symbol .validList)'),
    }
    if (rule, token) not in classes: raise ValueError(('unknown token class', rule, token, condition))
    expected, result = classes[rule, token]
    if condition != expected: raise ValueError(('changed token predicate', rule, condition, expected))
    return result


def generate():
    line = next(line for line in PROBE.read_text().splitlines() if line.startswith('cml_grammar='))
    text = line.split('rules :=', 1)[1]
    text = re.sub(r'\(NN (n\w+) :\(token, MMLnonT\) symbol\)', r'NN \1', text)
    text = text.replace('([] :(token, MMLnonT) symbol list)', '[]')
    text = text.removesuffix('⟩|>')
    pieces = re.split(r'; mkNT (n\w+) ↦ ', text)
    first = re.search(r'mkNT (n\w+) ↦ ', pieces[0])
    if not first: raise ValueError('missing first grammar rule')
    rules = [(first.group(1), pieces[0].split('↦ ', 1)[1])]
    rules += [(pieces[i], pieces[i + 1]) for i in range(1, len(pieces), 2)]
    declared = set(re.findall(r'^  \| (n\w+)', NTS.read_text(), re.M))
    if len(rules) != len(declared) or {n for n, _ in rules} != declared:
        raise ValueError('grammar nonterminal inventory differs')
    rendered = []
    for name, rhs in rules:
        patterns = []
        for group in split_unions(rhs):
            if not group.startswith('{') or not group.endswith('}'): raise ValueError((name, group))
            body = group[1:-1].strip()
            if body.startswith('[]'):
                if body != '[]': raise ValueError((name, body))
                patterns.append('[]'); continue
            matches = list(re.finditer(r'\[([^\[\]]*)\]', body))
            if not matches: raise ValueError((name, body))
            condition = body[matches[-1].end():].strip()
            if condition.startswith('| '): condition = condition[2:]
            elif condition: raise ValueError((name, condition))
            if len(matches) > 1 and condition: raise ValueError((name, body))
            for match in matches:
                terms = [term.strip() for term in match.group(1).split(';') if term.strip()]
                patterns.append('[' + ', '.join(token_atom(name, term, condition) for term in terms) + ']')
            if len(matches) > 1:
                remainder = re.sub(r'\[[^\[\]]*\]', '', body).replace(';', '').strip()
                if remainder: raise ValueError((name, remainder))
        rendered.append(f'  | .{name} => [' + ', '.join(patterns) + ']')
    names = ', '.join('.' + name for name, _ in rules)
    return '''-- Generated by scripts/generate-cake-cfg-grammar.py from the pinned HOL capture.
import Flapjack.CakeParser.CfgGrammarCore

/-! Generated source grammar patterns. This is Flapjack infrastructure until
the full `cmlG_def` correspondence and token-class interpretations are reviewed. -/
namespace Flapjack.CakeParser.CfgGrammar
open Flapjack.Basis.Pure.MlString Flapjack.Misc.Grammar

/-- Source production patterns indexed by CakeML nonterminal. -/
def productions : Nonterminal → List (List Atom)
''' + '\n'.join(rendered) + '''

/-- The finite list of all source grammar nonterminals. -/
def nonterminals : List Nonterminal := [''' + names + ''']

/-- Every nonterminal is represented in the generated finite support. -/
theorem mem_nonterminals (n : Nonterminal) : n ∈ nonterminals := by
  cases n <;> simp [nonterminals]

/-- Source-shaped CakeML grammar built from the generated production patterns.
Full equivalence to HOL's `cmlG` is not yet established. -/
def cmlGrammar : Grammar Token Nonterminal where
  start := .inl .nTopLevelDecs
  rules :=
    { lookup := fun key => match key with
        | .inl n => some (fun rhs => (productions n).any (fun pattern => matchesProduction pattern rhs) = true)
        | .inr _ => none
      finiteSupport := by
        refine ⟨nonterminals.map Sum.inl, ?_⟩
        intro key present
        cases key with
        | inl n => exact List.mem_map.mpr ⟨n, mem_nonterminals n, rfl⟩
        | inr _ => exact False.elim (present rfl) }

/-- Lookup is direct for every source nonterminal. -/
theorem lookup_nonterminal (n : Nonterminal) :
    cmlGrammar.rules.lookup (.inl n) =
      some (fun rhs => (productions n).any (fun pattern => matchesProduction pattern rhs) = true) := rfl

/-- The original grammar contains no auxiliary numeric nonterminal rules. -/
theorem lookup_auxiliary (n : Nat) : cmlGrammar.rules.lookup (.inr n) = none := rfl

end Flapjack.CakeParser.CfgGrammar
'''


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = generate()
    if args.check:
        if not OUTPUT.exists() or OUTPUT.read_text() != result: raise SystemExit('CakeML CFG grammar is stale')
        print('CakeML CFG grammar matches the pinned HOL capture')
    else:
        OUTPUT.write_text(result)
