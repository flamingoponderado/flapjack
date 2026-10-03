# Words quantified inside HOL predicates

The `words_as_type_indexed_bitvec` qualifier also covers a plain Lean `def`
whose result is `Prop` and whose word values occur in explicitly typed logical
quantifiers in its body. For example, HOL `wf_data (:'a) data` quantifies
arithmetic instructions and load offsets internally; its Lean signature can
retain just `(width : Nat) [NeZero width]` and the knowledge argument.

The reference checker extracts parenthesized typed binders from `∀` and `∃`
prefixes in such a predicate. Their types join the signature's word carrier
scope. It does not treat the whole predicate body as a carrier declaration.
The route excludes theorem proofs, definitions with another result type,
proof-typed quantifier binders, and bodies containing `let`, `have`, `by`,
`fun`, or `match`, and bodies containing string literals. A discarded word
value, a comment or a string's contents therefore cannot
license this route. More elaborate predicate presentations need a separately
reviewed extension.

Every direct word dimension retains its own `Nat` and `NeZero` binders in the
predicate signature. Internal applications of the reviewed width-first
structure and inductive carriers also check their dimension against that
signature, including when another internal binder already mentions `BitVec`.
The existing source resolution rules still apply to a named carrier used to
establish the word translation. Literal zero, missing positivity, and an
unbound second dimension are rejected.

Use the existing `reviewed_words_as_type_indexed_bitvec` manifest status and
record the actual internally quantified word carriers in the source comparison
note. The qualifier changes no HOL quantifier, hypothesis, conjunct or result.
Do not add a dummy word argument, replace an internally word-valued predicate
with a word-free numeric dimension, or omit a conjunct to obtain a passing
check. Source review must compare the entire HOL predicate and the imported
carriers; the syntactic checker and Lean kernel do not prove cross-language
equivalence.
